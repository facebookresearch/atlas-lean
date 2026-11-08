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
# The unilateral shift on `ℓ²(ℕ, 𝕜)`

The unilateral (forward) shift `S` on `ℓ²(ℕ, 𝕜)` inserts a zero in
coordinate `0` and shifts every other coordinate up by one:
`(S x) 0 = 0`, `(S x) (n + 1) = x n`. Its adjoint is the backward
shift `B`, `(B x) n = x (n + 1)`. The shift is the textbook example
of an isometry that is not unitary: `B ∘ S = 1` while
`S ∘ B = 1 - rankOne e₀ e₀`, where `e₀` is the first standard basis
vector, so `S` is injective but not surjective. The spectra of `S`
and `B` (proved in `LpShiftOperatorSpectrum.lean`) are the closed unit
ball in the scalar field: the disc for `ℂ` and the interval `[-1, 1]` for `ℝ`.

These are new derived supporting results. The archived Hilbert-space and
spectral material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean` supplies
related context, rather than an exact unilateral-shift target or proof.
The construction reuses Mathlib's `ℓ²` space, coordinate vectors, inner product,
adjoint and rank-one operator APIs.

## Main declarations

* `shiftCLM` : the unilateral shift as a bounded operator on `ℓ²(ℕ, 𝕜)`.
* `backwardCLM` : the backward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`.
* `shiftCLM_apply`, `backwardCLM_apply` : their pointwise actions.
* `norm_shiftCLM_apply` : the shift is an isometry,
  `‖S x‖ = ‖x‖`.
* `norm_shiftCLM` : `‖S‖ = 1`.
* `adjoint_shiftCLM` : `S† = B`.
* `backward_comp_shift` : `B ∘L S = 1`.
* `shift_comp_backward` : `S ∘L B = 1 - rankOne e₀ e₀`.
* `not_surjective_shiftCLM` : `S` is not surjective.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

open Filter Topology Set
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The forward-shift function on sequences: insert `0` at `0` and shift up by one. -/
def shiftFun (x : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => x n

/-- The backward-shift function on sequences: drop coordinate `0` and shift down by one. -/
def backwardFun (x : ℕ → 𝕜) (i : ℕ) : 𝕜 := x (i + 1)

@[simp] theorem shiftFun_zero (x : ℕ → 𝕜) : shiftFun x 0 = 0 := rfl

@[simp] theorem shiftFun_succ (x : ℕ → 𝕜) (n : ℕ) : shiftFun x (n + 1) = x n := rfl

omit [RCLike 𝕜] in
@[simp] theorem backwardFun_apply (x : ℕ → 𝕜) (i : ℕ) : backwardFun x i = x (i + 1) :=
  rfl

/-- The shifted sequence of an `ℓ²` sequence is in `ℓ²`: its squared
norms are the squared norms of the original sequence, shifted by one. -/
theorem memℓp_shiftFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (shiftFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖shiftFun (x : ℕ → 𝕜) (n + 1)‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [shiftFun_succ] using h
  exact (summable_nat_add_iff 1).mp h'

/-- The backward-shifted sequence of an `ℓ²` sequence is in `ℓ²`: its
squared norms are a tail of the squared norms of the original sequence. -/
theorem memℓp_backwardFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (backwardFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖backwardFun (x : ℕ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [backwardFun_apply] using (summable_nat_add_iff 1).mpr h
  exact h'

/-- The forward shift as a linear map. -/
noncomputable def shiftLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨shiftFun (x : ℕ → 𝕜), memℓp_shiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_add, shiftFun_zero, Pi.add_apply, add_zero]
    | succ n => simp only [lp.coeFn_add, shiftFun_succ, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_smul, shiftFun_zero, Pi.smul_apply, smul_zero]
    | succ n =>
        simp only [lp.coeFn_smul, shiftFun_succ, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]

/-- The backward shift as a linear map. -/
noncomputable def backwardLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨backwardFun (x : ℕ → 𝕜), memℓp_backwardFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, backwardFun_apply, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, backwardFun_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- Pointwise action of the forward-shift linear map. -/
theorem shiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    shiftLinMap x i = shiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- Pointwise action of the backward-shift linear map. -/
theorem backwardLinMap_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    backwardLinMap x i = backwardFun (x : ℕ → 𝕜) i :=
  rfl

/-- The squared norms of a shifted sequence sum to the squared norms of
the original sequence. -/
theorem tsum_shiftFun_norm (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖shiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal =
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖shiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    memℓp_shiftFun.summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [shiftFun_zero, shiftFun_succ, norm_zero,
    Real.zero_rpow (by simp : (2 : ℝ≥0∞).toReal ≠ 0), zero_add]

/-- The squared norms of a backward-shifted sequence sum to at most the
squared norms of the original sequence: they are a tail sum. -/
theorem tsum_backwardFun_norm_le (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖backwardFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal ≤
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [backwardFun_apply]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- The forward shift preserves norms. -/
theorem norm_shiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) : ‖shiftLinMap x‖ = ‖x‖ := by
  have hpow : ‖shiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal = ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (shiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_shiftFun_norm x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

/-- The backward shift does not increase norms. -/
theorem norm_backwardLinMap_apply_le (x : ℓ²(ℕ, 𝕜)) : ‖backwardLinMap x‖ ≤ ‖x‖ := by
  have hpow : ‖backwardLinMap x‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (backwardLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_backwardFun_norm_le x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact le_of_sq_le_sq hpow (norm_nonneg _)

/-- The unilateral shift as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def shiftCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  shiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact le_of_eq (norm_shiftLinMap_apply x))

/-- The backward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def backwardCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  backwardLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_backwardLinMap_apply_le x)

/-- Pointwise action of the unilateral shift. -/
theorem shiftCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    shiftCLM x i = shiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- Pointwise action of the backward shift. -/
theorem backwardCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    backwardCLM x i = backwardFun (x : ℕ → 𝕜) i :=
  rfl

/-- The unilateral shift is an isometry: `‖S x‖ = ‖x‖`. -/
theorem norm_shiftCLM_apply (x : ℓ²(ℕ, 𝕜)) : ‖shiftCLM x‖ = ‖x‖ :=
  norm_shiftLinMap_apply x

/-- The unilateral shift is an isometry of `ℓ²(ℕ, 𝕜)`. -/
theorem isometry_shiftCLM : Isometry (shiftCLM (𝕜 := 𝕜)) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_shiftCLM_apply]

/-- The operator norm of the unilateral shift is `1`. -/
theorem norm_shiftCLM : ‖shiftCLM (𝕜 := 𝕜)‖ = 1 := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le _ (by norm_num : (0 : ℝ) ≤ 1)
      (fun x => by rw [one_mul]; exact le_of_eq (norm_shiftLinMap_apply x))
  · have hle : ‖shiftCLM (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ ≤
        ‖shiftCLM‖ * ‖(lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜))‖ :=
      ContinuousLinearMap.le_opNorm (σ₁₂ := RingHom.id 𝕜) (f := shiftCLM)
        (x := (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜)))
    rw [norm_shiftCLM_apply, lp.norm_single (by simp : (0 : ℝ≥0∞) < 2), norm_one,
      mul_one] at hle
    exact hle

/-- The operator norm of the backward shift is at most `1`. -/
theorem norm_backwardCLM_le : ‖backwardCLM (𝕜 := 𝕜)‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ (by norm_num : (0 : ℝ) ≤ 1)
    (fun x => by rw [one_mul]; exact norm_backwardLinMap_apply_le x)

/-- The adjoint of the unilateral shift is the backward shift. -/
theorem adjoint_shiftCLM : (shiftCLM (𝕜 := 𝕜))† = backwardCLM := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hs : Summable (fun i => ⟪(x : ℕ → 𝕜) i, (shiftCLM y : ℕ → 𝕜) i⟫_𝕜) :=
    lp.summable_inner x (shiftCLM y)
  rw [hs.tsum_eq_zero_add]
  simp [shiftCLM_apply, backwardCLM_apply]

/-- The backward shift is a left inverse of the unilateral shift. -/
theorem backward_comp_shift : backwardCLM ∘L shiftCLM = (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, backwardCLM_apply, shiftCLM_apply,
    backwardFun_apply, shiftFun_succ, one_apply_eq_self]

/-- The unilateral shift is injective. -/
theorem injective_shiftCLM : Function.Injective (shiftCLM (𝕜 := 𝕜)) := by
  apply Function.LeftInverse.injective (g := backwardCLM)
  intro x
  simpa using DFunLike.congr_fun backward_comp_shift x

/-- Pointwise action of `S ∘ B`: it keeps every coordinate except `0`,
which it sends to `0`. -/
theorem shift_comp_backward_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    (shiftCLM ∘L backwardCLM) x i = if i = 0 then 0 else x i := by
  cases i with
  | zero =>
      rw [ite_eq_left rfl]
      simp only [ContinuousLinearMap.comp_apply, shiftCLM_apply, shiftFun_zero]
  | succ n =>
      rw [ite_eq_right (Nat.succ_ne_zero n)]
      simp only [ContinuousLinearMap.comp_apply, shiftCLM_apply, shiftFun_succ,
        backwardCLM_apply, backwardFun_apply]

/-- `S ∘ B = 1 - rankOne e₀ e₀`, where `e₀` is the first standard basis
vector: `S ∘ B` is the orthogonal projection onto `{e₀}ᗮ`. -/
theorem shift_comp_backward :
    shiftCLM ∘L backwardCLM =
      (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) -
        InnerProductSpace.rankOne 𝕜 (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜))
          (lp.single 2 0 (1 : 𝕜) : ℓ²(ℕ, 𝕜)) := by
  ext x i
  rw [shift_comp_backward_apply]
  cases i with
  | zero =>
      rw [ite_eq_left rfl]
      simp only [sub_apply, one_apply_eq_self,
        lp.coeFn_sub, InnerProductSpace.rankOne_apply, lp.inner_single_left,
        RCLike.inner_apply, map_one, Pi.sub_apply, lp.coeFn_smul,
        Pi.smul_apply, lp.coeFn_single, Pi.single_eq_same, smul_eq_mul, mul_one,
        sub_self]
  | succ n =>
      rw [ite_eq_right (Nat.succ_ne_zero n)]
      simp only [sub_apply, one_apply_eq_self,
        lp.coeFn_sub, InnerProductSpace.rankOne_apply, lp.inner_single_left,
        RCLike.inner_apply, map_one, Pi.sub_apply, lp.coeFn_smul,
        Pi.smul_apply, lp.coeFn_single, Pi.single_eq_of_ne (Nat.succ_ne_zero n),
        smul_eq_mul, mul_zero, sub_zero]

/-- The unilateral shift is not surjective: `e₀` is not in its range,
since every vector in the range has `0` in coordinate `0`. -/
theorem not_surjective_shiftCLM : ¬ Function.Surjective (shiftCLM (𝕜 := 𝕜)) := by
  intro h
  obtain ⟨x, hx⟩ := h (lp.single 2 0 (1 : 𝕜))
  have h0 := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) hx) 0
  simp [shiftCLM_apply, lp.single_apply] at h0

end MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
