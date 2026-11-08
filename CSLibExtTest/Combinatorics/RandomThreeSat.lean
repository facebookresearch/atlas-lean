/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Combinatorics.RandomThreeSat

@[expose] public section

namespace CSLibExtTest.RandomThreeSat

open CSLibExt.Combinatorics.RandomThreeSat

/-- Boundary check: with no clauses every formula is satisfiable. -/
example (n : ℕ) : satProb n 0 = 1 := satProb_zero n

/-- The sample space is nonempty once clauses exist, so the probability
bounds apply. -/
example {n m : ℕ} (hn : 3 ≤ n) : satProb n m ≤ 1 :=
  satProb_le_one

/-- Empty-space boundary: with fewer than three variables and a positive
clause count the formula space is empty, and the bound still holds. -/
example : satProb 2 1 ≤ 1 :=
  satProb_le_one

/-- The clause count is the source's `8 * C(n, 3)`, checked at `n = 3`
and `n = 4`. -/
example : Fintype.card (Clause 3) = 8 := by
  rw [card_clause]
  norm_num [Nat.choose]

example : Fintype.card (Clause 4) = 32 := by
  rw [card_clause]
  norm_num [Nat.choose]

/-- A concrete clause on three variables is satisfied by the all-`true`
assignment when its polarities are all `true` on its variables. -/
example :
    clauseSat (fun _ => true)
      ⟨(Finset.univ, fun i => decide (i ∈ (Finset.univ : Finset (Fin 3)))),
        by simp, by simp⟩ := by
  refine ⟨0, by simp, ?_⟩
  simp

/-- Cutoff monotonicity is the expected order on densities. -/
example {ρ : ℝ} (h : IsUpperCutoff ρ) : IsUpperCutoff (ρ + 1) :=
  h.mono (by linarith)

example {ρ : ℝ} (h : IsLowerCutoff ρ) : IsLowerCutoff (ρ - 1) :=
  h.anti (by linarith)

-- The canonical-CNF bridge agrees with the model's native predicates.
example (a : Fin 3 → Bool) (c : Clause 3) :
    clauseSat a c ↔
      Cslib.Logic.PL.CNFClause.Satisfies (extendAssign a) (toCNFClause c) :=
  clauseSat_iff a c

example (F : Formula 3 2) :
    Satisfiable F ↔ Cslib.Logic.PL.CNFSat (toCNF F) :=
  satisfiable_iff F

end CSLibExtTest.RandomThreeSat
