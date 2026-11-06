/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneQMatrixAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalShort

/-! Actual preferred-Q images suffice to identify the signed sparse short action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Equality of genuine preferred-Q bases identifies the actual short-line permutation. -/
theorem generatedSeventhXiPlaneShort_permutation_of_base (r s : GriessShortIndex)
    (h : (generatedSeventhXiPlaneQMatrixHom (griessShortQ r)).base =
      (griessShortQ s).base) :
    griessShortPermutation generatedSeventhXiPlaneFiber.val.2 r = s := by
  have he := DFunLike.congr_fun generatedSeventhXiPlaneQMatrixHom_eq_actual (griessShortQ r)
  change generatedSeventhXiPlaneQMatrixHom (griessShortQ r) =
    spinConjugation generatedSeventhXiPlaneFiber.val.1 (griessShortQ r) at he
  rw [he, griessShortQ_image_base] at h
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact congrArg Multiplicative.toAdd h

/-- The certified matrix hom retains the full actual extraspecial short phase. -/
theorem generatedSeventhXiPlaneShort_phase (r : GriessShortIndex) :
    localShortPhase generatedSeventhXiPlaneFiber r =
      Multiplicative.toAdd (generatedSeventhXiPlaneQMatrixHom (griessShortQ r)).coeff := by
  have he := DFunLike.congr_fun generatedSeventhXiPlaneQMatrixHom_eq_actual (griessShortQ r)
  change generatedSeventhXiPlaneQMatrixHom (griessShortQ r) =
    spinConjugation generatedSeventhXiPlaneFiber.val.1 (griessShortQ r) at he
  rw [he]
  rfl

/-- Every actual preferred basis image retains its genuine phase and line label. -/
theorem generatedSeventhXiPlaneShort_basis (r s : GriessShortIndex)
    (h : (generatedSeventhXiPlaneQMatrixHom (griessShortQ r)).base =
      (griessShortQ s).base) :
    localShortOperator generatedSeventhXiPlaneFiber (Pi.single r (1 : ℝ)) =
      qSign (Multiplicative.toAdd (generatedSeventhXiPlaneQMatrixHom (griessShortQ r)).coeff) •
        Pi.single s 1 := by
  have hp := generatedSeventhXiPlaneShort_permutation_of_base r s h
  funext t
  obtain ⟨u, rfl⟩ := (griessShortPermutation generatedSeventhXiPlaneFiber.val.2).surjective t
  rw [localShortOperator_image, ← hp, ← generatedSeventhXiPlaneShort_phase r]
  by_cases hu : u = r
  · subst u
    simp
  · have hn : griessShortPermutation generatedSeventhXiPlaneFiber.val.2 u ≠
        griessShortPermutation generatedSeventhXiPlaneFiber.val.2 r :=
      fun he => hu ((griessShortPermutation generatedSeventhXiPlaneFiber.val.2).injective he)
    simp [hu, hn]

/-- Genuine base images and complete phase-weight agreement fix the entire sparse short vector.
No support completeness or source phase is inferred from unsigned binary data. -/
theorem generatedSeventhXiPlaneShort_sparse_fixed {κ : Type*} [Fintype κ]
    (r : κ → GriessShortIndex) (c : κ → ℝ) (p : Equiv.Perm κ)
    (hb : ∀ k, (generatedSeventhXiPlaneQMatrixHom (griessShortQ (r k))).base =
      (griessShortQ (r (p k))).base)
    (hc : ∀ k, qSign (Multiplicative.toAdd
      (generatedSeventhXiPlaneQMatrixHom (griessShortQ (r k))).coeff) * c k = c (p k)) :
    localShortOperator generatedSeventhXiPlaneFiber
        (∑ k, c k • Pi.single (r k) (1 : ℝ)) =
      ∑ k, c k • Pi.single (r k) (1 : ℝ) := by
  classical
  rw [map_sum]
  simp_rw [map_smul, generatedSeventhXiPlaneShort_basis _ _ (hb _), smul_smul]
  have hw (k : κ) : c k * qSign (Multiplicative.toAdd
      (generatedSeventhXiPlaneQMatrixHom (griessShortQ (r k))).coeff) = c (p k) := by
    rw [mul_comm]
    exact hc k
  simp_rw [hw]
  exact Equiv.sum_comp p (fun k => c k • Pi.single (r k) (1 : ℝ))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
