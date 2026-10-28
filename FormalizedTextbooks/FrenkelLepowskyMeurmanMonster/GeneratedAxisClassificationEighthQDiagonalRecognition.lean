/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQForwardDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechFrameMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineGeometry

/-! The original diagonal action determines the physical permutation up to actual Golay signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem single_diagonal_outer (i : Fin 24) :
    Matrix.diagonal (Pi.single i (1 : ℝ)) =
      Matrix.vecMulVec (Pi.single i 1) (Pi.single i 1) := by
  ext j k
  by_cases hji : j = i <;> by_cases hki : k = i <;>
    simp_all [Matrix.diagonal_apply, Matrix.vecMulVec, Pi.single_apply, eq_comm]

private theorem relabel_single (p : Equiv.Perm (Fin 24)) (i : Fin 24) :
    (fun j => (Pi.single i (1 : ℝ) : Fin 24 → ℝ) (p.symm j)) = Pi.single (p i) 1 := by
  funext j
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

/-- The genuine diagonal action forces signed coordinate images with the specified permutation. -/
theorem generatedEighth_diagonal_signed_coordinates (e : leechIsomSubgroup)
    (p : golayAutomorphismSubgroup)
    (hd : ∀ d : Fin 24 → ℝ, conwayMatrixAction e (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d (p.val.symm i))) (i : Fin 24) :
    e.val (Pi.single i 1) = Pi.single (p.val i) 1 ∨
      e.val (Pi.single i 1) = -(Pi.single (p.val i) 1 : Fin 24 → ℝ) := by
  have h := hd (Pi.single i 1)
  rw [single_diagonal_outer, conwayMatrixAction_vecMulVec,
    relabel_single, single_diagonal_outer] at h
  apply (generatedNormEight_outer_eq_iff (Pi.single (p.val i) 1)
    (e.val (Pi.single i 1)) (by
      intro hz
      have hi := congrFun hz (p.val i)
      norm_num at hi)).mp
  exact h.symm

/-- A genuine diagonal action identifies the whole physical map up to genuine code signs. -/
theorem generatedEighth_diagonal_recognizes_permutation (e : leechIsomSubgroup)
    (p : golayAutomorphismSubgroup)
    (hd : ∀ d : Fin 24 → ℝ, conwayMatrixAction e (Matrix.diagonal d) =
      Matrix.diagonal (fun i => d (p.val.symm i))) :
    ∃ c : golayCode, e = golaySignIsometry c * golayPermutationIsometry p := by
  have hm : e ∈ golayMonomialSubgroup := by
    apply leechFrame_mem_monomial
    intro i
    rcases generatedEighth_diagonal_signed_coordinates e p hd i with h | h
    · exact ⟨p.val i, 0, by simpa only [qSign_zero, one_smul] using h⟩
    · exact ⟨p.val i, 1, by simpa only [qSign_one, neg_one_smul] using h⟩
  obtain ⟨c, q, he⟩ := hm
  have hqp : q = p := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have h := hd (Pi.single i 1)
    rw [he] at h
    change conwayMatrixAction (golayMonomialPair (c, q)) (Matrix.diagonal (Pi.single i 1)) = _ at h
    rw [generatedEighth_monomial_diagonal] at h
    have hv := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A (q.val i) (q.val i)) h
    simp only [Matrix.diagonal_apply, ite_true, Equiv.symm_apply_apply, Pi.single_apply] at hv
    by_contra hn
    have hpne : p.val.symm (q.val i) ≠ i := by
      intro hi
      apply hn
      have hj := congrArg p.val hi
      rw [Equiv.apply_symm_apply] at hj
      exact hj
    simp [hpne] at hv
  exact ⟨c, hqp ▸ he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
