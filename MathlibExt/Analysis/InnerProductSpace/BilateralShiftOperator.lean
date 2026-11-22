/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The bilateral shift on `ℓ²(ℤ, 𝕜)`

The bilateral (two-sided) shift `S` on `ℓ²(ℤ, 𝕜)` shifts every coordinate
up by one: `(S x) n = x (n - 1)`. Its adjoint is the backward shift `B`,
`(B x) n = x (n + 1)`. In contrast to the unilateral shift on `ℓ²(ℕ, 𝕜)`,
the bilateral shift is a unitary operator: `B ∘ S = 1` and `S ∘ B = 1`,
so `S` is a surjective isometry. Its spectrum is the unit circle, proved
in `BilateralShiftSpectrum.lean`.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the spectral theorem, the Fredholm alternative, the Green's
operator). It is not one of the 72 v1 targets. The construction below
uses Mathlib's `ℓ²` space, its inner product (`lp.inner_eq_tsum`), and
single-coordinate vectors (`lp.single`).

## Main declarations

* `bilateralShiftCLM` : the bilateral shift as a bounded operator on `ℓ²(ℤ, 𝕜)`.
* `bilateralBackwardCLM` : the bilateral backward shift.
* `bilateralShiftCLM_apply`, `bilateralBackwardCLM_apply` : their pointwise actions.
* `norm_bilateralShiftCLM_apply`, `norm_bilateralBackwardCLM_apply` :
  both shifts preserve norms.
* `norm_bilateralShiftCLM`, `norm_bilateralBackwardCLM` : both have operator norm `1`.
* `adjoint_bilateralShiftCLM` : `S† = B`.
* `bilateralBackward_comp_bilateralShift`, `bilateralShift_comp_bilateralBackward` :
  the two shifts are mutual inverses.
* `bijective_bilateralShiftCLM` : `S` is bijective.
* `mem_unitary_bilateralShiftCLM` : `S` is unitary.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.BilateralShiftOperator

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The bilateral forward-shift function: `(S x) n = x (n - 1)`. -/
def bilateralShiftFun (x : ℤ → 𝕜) (n : ℤ) : 𝕜 := x (n - 1)

/-- The bilateral backward-shift function: `(B x) n = x (n + 1)`. -/
def bilateralBackwardFun (x : ℤ → 𝕜) (n : ℤ) : 𝕜 := x (n + 1)

omit [RCLike 𝕜] in
@[simp] theorem bilateralShiftFun_apply (x : ℤ → 𝕜) (n : ℤ) :
    bilateralShiftFun x n = x (n - 1) := rfl

omit [RCLike 𝕜] in
@[simp] theorem bilateralBackwardFun_apply (x : ℤ → 𝕜) (n : ℤ) :
    bilateralBackwardFun x n = x (n + 1) := rfl

theorem memℓp_bilateralShiftFun {x : ℓ²(ℤ, 𝕜)} : Memℓp (bilateralShiftFun (x : ℤ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have heq : (fun n => ‖bilateralShiftFun (x : ℤ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal)
      = (fun n => ‖(x : ℤ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal) ∘ ⇑(Equiv.subRight (1 : ℤ)) := by
    funext n
    simp [bilateralShiftFun, Equiv.subRight_apply]
  rw [heq]
  exact (Equiv.summable_iff (Equiv.subRight (1 : ℤ))).mpr h

theorem memℓp_bilateralBackwardFun {x : ℓ²(ℤ, 𝕜)} :
    Memℓp (bilateralBackwardFun (x : ℤ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have heq : (fun n => ‖bilateralBackwardFun (x : ℤ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal)
      = (fun n => ‖(x : ℤ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal) ∘ ⇑(Equiv.addRight (1 : ℤ)) := by
    funext n
    simp [bilateralBackwardFun]
  rw [heq]
  exact (Equiv.summable_iff (Equiv.addRight (1 : ℤ))).mpr h

/-- The bilateral forward shift as a linear map. -/
noncomputable def bilateralShiftLinMap : ℓ²(ℤ, 𝕜) →ₗ[𝕜] ℓ²(ℤ, 𝕜) where
  toFun x := ⟨bilateralShiftFun (x : ℤ → 𝕜), memℓp_bilateralShiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, bilateralShiftFun_apply, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, bilateralShiftFun_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- The bilateral backward shift as a linear map. -/
noncomputable def bilateralBackwardLinMap : ℓ²(ℤ, 𝕜) →ₗ[𝕜] ℓ²(ℤ, 𝕜) where
  toFun x := ⟨bilateralBackwardFun (x : ℤ → 𝕜), memℓp_bilateralBackwardFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, bilateralBackwardFun_apply, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, bilateralBackwardFun_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

theorem bilateralShiftLinMap_apply (x : ℓ²(ℤ, 𝕜)) (i : ℤ) :
    bilateralShiftLinMap x i = bilateralShiftFun (x : ℤ → 𝕜) i := rfl

theorem bilateralBackwardLinMap_apply (x : ℓ²(ℤ, 𝕜)) (i : ℤ) :
    bilateralBackwardLinMap x i = bilateralBackwardFun (x : ℤ → 𝕜) i := rfl

theorem tsum_bilateralShiftFun_norm (x : ℓ²(ℤ, 𝕜)) :
    ∑' i, ‖bilateralShiftFun (x : ℤ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal =
      ∑' i, ‖(x : ℤ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have heq := Equiv.tsum_eq (Equiv.subRight (1 : ℤ))
    (fun n => ‖(x : ℤ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal)
  rw [← heq]
  apply tsum_congr
  intro n
  simp [bilateralShiftFun, Equiv.subRight_apply]

theorem tsum_bilateralBackwardFun_norm (x : ℓ²(ℤ, 𝕜)) :
    ∑' i, ‖bilateralBackwardFun (x : ℤ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal =
      ∑' i, ‖(x : ℤ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have heq := Equiv.tsum_eq (Equiv.addRight (1 : ℤ))
    (fun n => ‖(x : ℤ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal)
  rw [← heq]
  apply tsum_congr
  intro n
  simp [bilateralBackwardFun]

theorem norm_bilateralShiftLinMap_apply (x : ℓ²(ℤ, 𝕜)) : ‖bilateralShiftLinMap x‖ = ‖x‖ := by
  have hpow : ‖bilateralShiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal = ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (bilateralShiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_bilateralShiftFun_norm x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

theorem norm_bilateralBackwardLinMap_apply (x : ℓ²(ℤ, 𝕜)) :
    ‖bilateralBackwardLinMap x‖ = ‖x‖ := by
  have hpow : ‖bilateralBackwardLinMap x‖ ^ (2 : ℝ≥0∞).toReal = ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (bilateralBackwardLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_bilateralBackwardFun_norm x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

/-- The bilateral shift as a bounded operator on `ℓ²(ℤ, 𝕜)`. -/
noncomputable def bilateralShiftCLM : ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜) :=
  bilateralShiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact le_of_eq (norm_bilateralShiftLinMap_apply x))

/-- The bilateral backward shift as a bounded operator on `ℓ²(ℤ, 𝕜)`. -/
noncomputable def bilateralBackwardCLM : ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜) :=
  bilateralBackwardLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact le_of_eq (norm_bilateralBackwardLinMap_apply x))

theorem bilateralShiftCLM_apply (x : ℓ²(ℤ, 𝕜)) (i : ℤ) :
    bilateralShiftCLM x i = bilateralShiftFun (x : ℤ → 𝕜) i := rfl

theorem bilateralBackwardCLM_apply (x : ℓ²(ℤ, 𝕜)) (i : ℤ) :
    bilateralBackwardCLM x i = bilateralBackwardFun (x : ℤ → 𝕜) i := rfl

theorem norm_bilateralShiftCLM_apply (x : ℓ²(ℤ, 𝕜)) : ‖bilateralShiftCLM x‖ = ‖x‖ :=
  norm_bilateralShiftLinMap_apply x

theorem norm_bilateralBackwardCLM_apply (x : ℓ²(ℤ, 𝕜)) :
    ‖bilateralBackwardCLM x‖ = ‖x‖ :=
  norm_bilateralBackwardLinMap_apply x

theorem isometry_bilateralShiftCLM : Isometry (bilateralShiftCLM (𝕜 := 𝕜)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_bilateralShiftCLM_apply]

theorem norm_bilateralShiftCLM : ‖bilateralShiftCLM (𝕜 := 𝕜)‖ = 1 := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (by norm_num : (0 : ℝ) ≤ 1)
      (fun x => by rw [one_mul]; exact le_of_eq (norm_bilateralShiftLinMap_apply x))
  · have hle : ‖bilateralShiftCLM (lp.single 2 0 (1 : 𝕜) : ℓ²(ℤ, 𝕜))‖ ≤
        ‖bilateralShiftCLM‖ * ‖(lp.single 2 0 (1 : 𝕜) : ℓ²(ℤ, 𝕜))‖ :=
      ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜) (f := bilateralShiftCLM)
        (x := (lp.single 2 0 (1 : 𝕜) : ℓ²(ℤ, 𝕜)))
    rw [norm_bilateralShiftCLM_apply, lp.norm_single (by simp : (0 : ℝ≥0∞) < 2), norm_one,
      mul_one] at hle
    exact hle

theorem norm_bilateralBackwardCLM : ‖bilateralBackwardCLM (𝕜 := 𝕜)‖ = 1 := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (by norm_num : (0 : ℝ) ≤ 1)
      (fun x => by rw [one_mul]; exact le_of_eq (norm_bilateralBackwardLinMap_apply x))
  · have hle : ‖bilateralBackwardCLM (lp.single 2 0 (1 : 𝕜) : ℓ²(ℤ, 𝕜))‖ ≤
        ‖bilateralBackwardCLM‖ * ‖(lp.single 2 0 (1 : 𝕜) : ℓ²(ℤ, 𝕜))‖ :=
      ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜) (f := bilateralBackwardCLM)
        (x := (lp.single 2 0 (1 : 𝕜) : ℓ²(ℤ, 𝕜)))
    rw [norm_bilateralBackwardCLM_apply, lp.norm_single (by simp : (0 : ℝ≥0∞) < 2), norm_one,
      mul_one] at hle
    exact hle

theorem adjoint_bilateralShiftCLM : (bilateralShiftCLM (𝕜 := 𝕜))† = bilateralBackwardCLM := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have heq := Equiv.tsum_eq (Equiv.subRight (1 : ℤ))
    (fun n => ⟪(bilateralBackwardCLM x : ℤ → 𝕜) n, (y : ℤ → 𝕜) n⟫_𝕜)
  rw [← heq]
  apply tsum_congr
  intro n
  simp [bilateralBackwardCLM_apply, bilateralShiftCLM_apply, Equiv.subRight_apply]

theorem bilateralBackward_comp_bilateralShift :
    bilateralBackwardCLM ∘L bilateralShiftCLM =
      (1 : ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) := by
  ext x i
  simp [ContinuousLinearMap.comp_apply, bilateralBackwardCLM_apply, bilateralShiftCLM_apply,
    bilateralBackwardFun_apply, bilateralShiftFun_apply]

theorem bilateralShift_comp_bilateralBackward :
    bilateralShiftCLM ∘L bilateralBackwardCLM =
      (1 : ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) := by
  ext x i
  simp [ContinuousLinearMap.comp_apply, bilateralBackwardCLM_apply, bilateralShiftCLM_apply,
    bilateralBackwardFun_apply, bilateralShiftFun_apply]

theorem bijective_bilateralShiftCLM :
    Function.Bijective (bilateralShiftCLM (𝕜 := 𝕜)) := by
  refine ⟨?_, ?_⟩
  · apply Function.LeftInverse.injective (g := bilateralBackwardCLM)
    intro x
    simpa using DFunLike.congr_fun bilateralBackward_comp_bilateralShift x
  · apply Function.RightInverse.surjective (g := bilateralBackwardCLM)
    intro x
    simpa using DFunLike.congr_fun bilateralShift_comp_bilateralBackward x

theorem mem_unitary_bilateralShiftCLM :
    bilateralShiftCLM (𝕜 := 𝕜) ∈ unitary (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) := by
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, adjoint_bilateralShiftCLM]
  constructor
  · ext x i
    simp [mul_apply_eq_comp, bilateralBackwardCLM_apply, bilateralShiftCLM_apply,
      bilateralBackwardFun_apply, bilateralShiftFun_apply]
  · ext x i
    simp [mul_apply_eq_comp, bilateralBackwardCLM_apply, bilateralShiftCLM_apply,
      bilateralBackwardFun_apply, bilateralShiftFun_apply]

end MathlibExt.Analysis.InnerProductSpace.BilateralShiftOperator
