import Mathlib

#leansearch "IsPrime."

#eval 4 % 3



/-- Finite Field instances, implemented as a pair of Natural numbers. -/
structure FF (p: ℕ ) [Fact p.Prime] where

  /-- The -/
  num: ℕ

  /-- A proof that the value is between 0 and the characteristic -/
  zero_le_num_lt_char: 0 ≤ num ∧ num < p



instance {p: ℕ} [Fact p.Prime] : Inhabited (FF p) :=
  ⟨ { num := 0,
      zero_le_num_lt_char := ⟨ by linarith, Nat.pos_of_neZero p ⟩  } ⟩


def add (p: ℕ ) [Fact p.Prime] (a b : FF p) : FF p :=
  ⟨ (a.num + b.num) % p,
     by
       constructor
       · positivity
       · refine Nat.mod_lt (a.num + b.num) ?_
         exact Nat.pos_of_neZero p ⟩
