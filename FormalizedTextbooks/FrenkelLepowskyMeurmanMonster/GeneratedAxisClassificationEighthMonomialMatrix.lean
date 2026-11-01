/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthPermutationFlag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatialMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! Actual diagonal matrix action of genuine signed Golay permutations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The physical matrix entries of an original signed Golay permutation. -/
theorem generatedEighth_monomial_matrix_entry (c : golayCode)
    (p : golayAutomorphismSubgroup) (i j : Fin 24) :
    leechIsomMatrix (golayMonomialPair (c, p)) i j =
      qSign (c.val i) * (if p.val.symm i = j then 1 else 0) := by
  change qSign (c.val i) * ((Pi.single j (1 : ℝ) : Fin 24 → ℝ) (p.val.symm i)) = _
  simp [Pi.single_apply, eq_comm]

/-- Original signed Golay permutations act on every diagonal matrix by coordinate relabeling. -/
theorem generatedEighth_monomial_diagonal (c : golayCode)
    (p : golayAutomorphismSubgroup) (a : Fin 24 → ℝ) :
    conwayMatrixAction (golayMonomialPair (c, p)) (Matrix.diagonal a) =
      Matrix.diagonal (fun i => a (p.val.symm i)) := by
  rw [conwayMatrixAction_eq_conjugate]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    generatedEighth_monomial_matrix_entry, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single (p.val.symm i)]
  · by_cases hij : i = j
    · subst j
      simp only [ite_true, mul_one]
      rw [mul_right_comm, qSign_sq, one_mul]
    · have hne : p.val.symm j ≠ p.val.symm i := fun h => hij (p.val.symm.injective h).symm
      simp [hne, hij]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
