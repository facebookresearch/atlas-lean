/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Toeplitz operators on `ℓ²(ℕ, 𝕜)` with absolutely summable symbol

A Toeplitz operator on `ℓ²(ℕ, 𝕜)` is the operator whose matrix is constant on
diagonals: for a symbol `a : ℤ → 𝕜`,
`(Tₐ x)ᵢ = ∑'ⱼ, a (i - j) * x j`.
The classical instance is the unilateral shift (symbol `δ₁`), and the
backward shift is the symbol `δ₋₁`. Here we treat the cleanly bounded case
of an absolutely summable symbol:

* `toeplitzSlice k` is the `k`-th diagonal slice: for `k ≥ 0` it is the
  `k`-fold forward shift, for `k < 0` it is the `(-k)`-fold backward shift.
  It has norm at most `1`, and its adjoint is the slice at `-k`.
* `toeplitzOperator a ha` is `∑' k, a k • toeplitzSlice k`, a norm-convergent
  series when `a` is absolutely summable (`∑' k, ‖a k‖ < ∞`).
* Boundedness: `‖Tₐ‖ ≤ ∑' k, ‖a k‖`, from the triangle inequality.
* Adjoint: `(Tₐ)† = T_{a*}`, where `a* k = star (a (-k))`, since
  `(toeplitzSlice k)† = toeplitzSlice (-k)`.
* Self-adjointness: `Tₐ` is self-adjoint iff `star (a (-k)) = a k` for all `k`.
* Compactness: `Tₐ` is compact iff `a = 0`. A nonzero symbol gives a
  non-compact operator: the images `Tₐ eₙ` of the standard basis vectors
  have a coordinate `a k₀ ≠ 0` and converge coordinatewise to `0`, so no
  subsequence can converge in norm. This is in sharp contrast with the
  Hankel operators of batch 128, which are always compact for an
  absolutely summable symbol.
* Delta symbols: `‖T_{δ_m • c}‖ = ‖c‖` for every `m : ℤ`.

This is a companion to the Hilbert-space / compact-operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`. It is
not one of the 72 v1 targets, and it is not in the pinned Mathlib or in base
MathlibExt: base MathlibExt has only finite Toeplitz *matrices*
(`MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean`, `Matrix.Toeplitz`), with
no operator, boundedness, adjoint, or compactness statement. It is distinct
from batch 128 (`HankelOperator.lean`), which treats the anti-diagonal
slices `a (i + j)`; the diagonal slices, the adjoint symbol, and the
compact-iff-zero dichotomy here are new.

## Main declarations

* `toeplitzSlice k` : the `k`-th diagonal slice, as a bounded operator.
* `toeplitzOperator a ha` : the Toeplitz operator with symbol `a`.
* `toeplitzOperator_apply` : `(Tₐ x) i = ∑' j, a (i - j) * x j`.
* `norm_toeplitzOperator_le` : `‖Tₐ‖ ≤ ∑' k, ‖a k‖`.
* `adjoint_toeplitzOperator` : `(Tₐ)† = T_{a*}`.
* `isSelfAdjoint_toeplitzOperator_iff` : self-adjointness iff `star (a (-k)) = a k`.
* `isCompactOperator_toeplitzOperator_iff` : compactness iff `a = 0`.
* `norm_toeplitzOperator_delta` : `‖T_{δ_m • c}‖ = ‖c‖`.
-/

@[expose] public section

open Filter Topology Set
open scoped _root_.lp ENNReal BigOperators InnerProductSpace InnerProduct

namespace MathlibExt.Analysis.InnerProductSpace.ToeplitzOperator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Norm squared of an `ℓ²(ℕ, 𝕜)` vector is the sum of the squared coordinate
norms. -/
private theorem toeplitz_normSq_eq_tsum (f : ℓ²(ℕ, 𝕜)) :
    ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (E := fun _ : ℕ => 𝕜) f
  rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num] at h
  have h2 : ‖f‖ ^ (2 : ℝ) = ‖f‖ ^ 2 := by rw [Real.rpow_two]
  rw [h2] at h
  rw [h]
  apply tsum_congr
  intro i
  rw [Real.rpow_two]

/-- Summability of squared coordinate norms from `Memℓp`. -/
private theorem toeplitz_summable_normSq_of_memℓp {f : ℕ → 𝕜} (hf : Memℓp f 2) :
    Summable fun i => ‖f i‖ ^ 2 := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hf
  simpa using h

/-- `Memℓp` at `2` from summability of squared norms. -/
private theorem toeplitz_memℓp_of_summable_normSq {f : ℕ → 𝕜}
    (hf : Summable fun i => ‖f i‖ ^ 2) : Memℓp f 2 := by
  apply (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  simpa using hf

/-- The `k`-th diagonal slice function: shift coordinates by `k`, killing
the coordinates that fall off the end. For `k ≥ 0` this is the `k`-fold
forward shift; for `k < 0` it is the `(-k)`-fold backward shift. -/
def toeplitzSliceFun (k : ℤ) (x : ℕ → 𝕜) (i : ℕ) : 𝕜 :=
  if k ≤ (i : ℤ) then x (((i : ℤ) - k).toNat) else 0

@[simp] theorem toeplitzSliceFun_apply (k : ℤ) (x : ℕ → 𝕜) (i : ℕ) :
    toeplitzSliceFun k x i = if k ≤ (i : ℤ) then x (((i : ℤ) - k).toNat) else 0 := rfl

/-- A slice vanishes off its range. -/
private theorem toeplitzSliceFun_eq_zero_of_not_le {k : ℤ} {x : ℕ → 𝕜} {i : ℕ}
    (h : ¬ k ≤ (i : ℤ)) : toeplitzSliceFun k x i = 0 := by
  simp [toeplitzSliceFun_apply, h]

/-- For `k ≥ 0`, the slice at `j + k` picks out coordinate `j`. -/
private theorem toeplitzSliceFun_add_of_nonneg {k : ℤ} (hk : 0 ≤ k) (x : ℕ → 𝕜) (j : ℕ) :
    toeplitzSliceFun k x (j + k.toNat) = x j := by
  have hm : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  have hpos : k ≤ ((j + k.toNat : ℕ) : ℤ) := by
    have h2 : ((j + k.toNat : ℕ) : ℤ) = (j : ℤ) + k := by
      rw [Nat.cast_add, hm]
    rw [h2]
    exact le_add_of_nonneg_left (Nat.cast_nonneg j)
  rw [toeplitzSliceFun_apply, ite_eq_left hpos]
  congr 1
  have h1 : ((j + k.toNat : ℕ) : ℤ) - k = (j : ℤ) := by
    rw [Nat.cast_add, hm]; ring
  rw [h1]
  exact Int.toNat_natCast j

/-- For `k ≤ 0`, the slice is a plain index shift by `(-k)`. -/
private theorem toeplitzSliceFun_of_nonpos {k : ℤ} (hk : k ≤ 0) (x : ℕ → 𝕜) (i : ℕ) :
    toeplitzSliceFun k x i = x (i + (-k).toNat) := by
  have hm : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (neg_nonneg.mpr hk)
  rw [toeplitzSliceFun_apply, ite_eq_left (le_trans hk (Nat.cast_nonneg i))]
  congr 1
  have h1 : (i : ℤ) - k = ((i + (-k).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_add, hm]; ring
  rw [h1]
  exact Int.toNat_natCast _

/-- Summability of the squared norms of a sliced sequence. -/
private theorem toeplitz_summable_normSq_sliceFun {k : ℤ} {x : ℓ²(ℕ, 𝕜)} :
    Summable fun i => ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2 := by
  by_cases hk : 0 ≤ k
  · -- The sliced norms are a reindexing of the original norms.
    have hHas : HasSum (fun i => ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2) (‖x‖ ^ 2) := by
      apply (Function.Injective.hasSum_iff (g := fun j => j + k.toNat)
        (by intro j₁ j₂ h; simpa using h) ?_).mp
      · have hcomp : (fun i => ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2) ∘
            (fun j => j + k.toNat) = fun j => ‖(x : ℕ → 𝕜) j‖ ^ 2 := by
          funext j
          simp only [Function.comp_apply]
          rw [toeplitzSliceFun_add_of_nonneg hk]
        rw [hcomp]
        rw [toeplitz_normSq_eq_tsum x]
        exact (toeplitz_summable_normSq_of_memℓp (lp.memℓp x)).hasSum
      · intro i hi
        by_cases hle : k ≤ (i : ℤ)
        · exfalso
          apply hi
          refine ⟨i - k.toNat, ?_⟩
          have hm : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
          have hmi : k.toNat ≤ i := by
            have hle' : ((k.toNat : ℤ)) ≤ (i : ℤ) := by rw [hm]; exact hle
            exact_mod_cast hle'
          dsimp only
          omega
        · rw [toeplitzSliceFun_eq_zero_of_not_le hle]
          simp
    exact hHas.summable
  · have hk' : k ≤ 0 := le_of_lt (not_le.mp hk)
    have heq : (fun i => ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2) =
        fun i => ‖(x : ℕ → 𝕜) (i + (-k).toNat)‖ ^ 2 := by
      funext i
      rw [toeplitzSliceFun_of_nonpos hk']
    rw [heq]
    exact (summable_nat_add_iff ((-k).toNat)).mpr
      (toeplitz_summable_normSq_of_memℓp (lp.memℓp x))

/-- The `ℓ²` norm of a sliced sequence is at most the norm of the original. -/
private theorem toeplitz_tsum_normSq_slice_le {k : ℤ} (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2 ≤ ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ 2 := by
  by_cases hk : 0 ≤ k
  · have hHas : HasSum (fun i => ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2) (‖x‖ ^ 2) := by
      apply (Function.Injective.hasSum_iff (g := fun j => j + k.toNat)
        (by intro j₁ j₂ h; simpa using h) ?_).mp
      · have hcomp : (fun i => ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2) ∘
            (fun j => j + k.toNat) = fun j => ‖(x : ℕ → 𝕜) j‖ ^ 2 := by
          funext j
          simp only [Function.comp_apply]
          rw [toeplitzSliceFun_add_of_nonneg hk]
        rw [hcomp]
        rw [toeplitz_normSq_eq_tsum x]
        exact (toeplitz_summable_normSq_of_memℓp (lp.memℓp x)).hasSum
      · intro i hi
        by_cases hle : k ≤ (i : ℤ)
        · exfalso
          apply hi
          refine ⟨i - k.toNat, ?_⟩
          have hm : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
          have hmi : k.toNat ≤ i := by
            have hle' : ((k.toNat : ℤ)) ≤ (i : ℤ) := by rw [hm]; exact hle
            exact_mod_cast hle'
          dsimp only
          omega
        · rw [toeplitzSliceFun_eq_zero_of_not_le hle]
          simp
    rw [hHas.tsum_eq, toeplitz_normSq_eq_tsum]
  · have hk' : k ≤ 0 := le_of_lt (not_le.mp hk)
    have heq : (fun i => ‖toeplitzSliceFun k (x : ℕ → 𝕜) i‖ ^ 2) =
        fun i => ‖(x : ℕ → 𝕜) (i + (-k).toNat)‖ ^ 2 := by
      funext i
      rw [toeplitzSliceFun_of_nonpos hk']
    rw [heq]
    have hsum := toeplitz_summable_normSq_of_memℓp (lp.memℓp x)
    have h := hsum.sum_add_tsum_nat_add ((-k).toNat)
    calc ∑' i, ‖(x : ℕ → 𝕜) (i + (-k).toNat)‖ ^ 2
        ≤ (∑ i ∈ Finset.range ((-k).toNat), ‖(x : ℕ → 𝕜) i‖ ^ 2) +
            ∑' i, ‖(x : ℕ → 𝕜) (i + (-k).toNat)‖ ^ 2 :=
          le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => by positivity)
      _ = ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ 2 := h

/-- The slice of an `ℓ²` sequence is in `ℓ²`. -/
theorem toeplitz_memℓp_sliceFun {k : ℤ} {x : ℓ²(ℕ, 𝕜)} :
    Memℓp (toeplitzSliceFun k (x : ℕ → 𝕜)) 2 :=
  toeplitz_memℓp_of_summable_normSq toeplitz_summable_normSq_sliceFun

/-- The `k`-th diagonal slice as a linear map. -/
noncomputable def toeplitzSliceLinMap (k : ℤ) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨toeplitzSliceFun k (x : ℕ → 𝕜), toeplitz_memℓp_sliceFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, Pi.add_apply, toeplitzSliceFun_apply]
    split_ifs with hi <;> simp
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, toeplitzSliceFun_apply,
      RingHom.id_apply]
    split_ifs with hi <;> simp

/-- Pointwise action of the slice linear map. -/
theorem toeplitzSliceLinMap_apply (k : ℤ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    toeplitzSliceLinMap k x i = toeplitzSliceFun k (x : ℕ → 𝕜) i := rfl

/-- A slice does not increase norms. -/
theorem norm_toeplitzSliceLinMap_apply_le (k : ℤ) (x : ℓ²(ℕ, 𝕜)) :
    ‖toeplitzSliceLinMap k x‖ ≤ ‖x‖ := by
  have hpow : ‖toeplitzSliceLinMap k x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [toeplitz_normSq_eq_tsum, toeplitz_normSq_eq_tsum]
    exact toeplitz_tsum_normSq_slice_le x
  exact le_of_sq_le_sq hpow (norm_nonneg _)

/-- The `k`-th diagonal slice as a bounded operator. -/
noncomputable def toeplitzSlice (k : ℤ) : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  (toeplitzSliceLinMap k).mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_toeplitzSliceLinMap_apply_le k x)

/-- Pointwise action of the slice operator. -/
theorem toeplitzSlice_apply (k : ℤ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    toeplitzSlice k x i = toeplitzSliceFun k (x : ℕ → 𝕜) i := rfl

/-- The operator norm of a slice is at most `1`. -/
theorem norm_toeplitzSlice_le (k : ℤ) : ‖toeplitzSlice (𝕜 := 𝕜) k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]
    exact norm_toeplitzSliceLinMap_apply_le k x)

/-- A slice is adjoint to the slice at the negated index: the diagonal
symmetry exchanges the two sides of the inner product. -/
theorem toeplitzSlice_inner_symm (k : ℤ) (x y : ℓ²(ℕ, 𝕜)) :
    ⟪toeplitzSlice k x, y⟫_𝕜 = ⟪x, toeplitzSlice (-k) y⟫_𝕜 := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  by_cases hk : 0 ≤ k
  · -- The first `k` terms of the left sum vanish; shifting by `k` gives
    -- `∑' j, ⟪x j, y (j + k)⟫`, which is also the right side.
    have hF : Summable fun i => ⟪toeplitzSlice k x i, y i⟫_𝕜 :=
      lp.summable_inner (toeplitzSlice k x) y
    have hshift : ∑' i, ⟪toeplitzSlice k x i, y i⟫_𝕜 =
        ∑' i, ⟪toeplitzSlice k x (i + k.toNat), y (i + k.toNat)⟫_𝕜 := by
      have h := hF.sum_add_tsum_nat_add (k.toNat)
      have hzero : ∑ i ∈ Finset.range (k.toNat), ⟪toeplitzSlice k x i, y i⟫_𝕜 = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hik : ¬ k ≤ (i : ℤ) := by
          rw [Finset.mem_range] at hi
          have hm : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
          have hlt : (i : ℤ) < (k.toNat : ℤ) := by exact_mod_cast hi
          rw [hm] at hlt
          omega
        rw [toeplitzSlice_apply, toeplitzSliceFun_eq_zero_of_not_le hik]
        simp
      rw [hzero, zero_add] at h
      exact h.symm
    rw [hshift]
    apply tsum_congr
    intro j
    rw [toeplitzSlice_apply, toeplitzSliceFun_add_of_nonneg hk,
      toeplitzSlice_apply, toeplitzSliceFun_of_nonpos (neg_nonpos.mpr hk)]
    simp only [neg_neg]
  · have hk' : k ≤ 0 := le_of_lt (not_le.mp hk)
    -- The first `(-k)` terms of the right sum vanish; shifting by `(-k)`
    -- gives `∑' i, ⟪x (i + (-k)), y i⟫`, which is also the left side.
    have hG : Summable fun i => ⟪(x : ℕ → 𝕜) i, toeplitzSlice (-k) y i⟫_𝕜 :=
      lp.summable_inner x (toeplitzSlice (-k) y)
    have hshift : ∑' i, ⟪(x : ℕ → 𝕜) i, toeplitzSlice (-k) y i⟫_𝕜 =
        ∑' i, ⟪(x : ℕ → 𝕜) (i + (-k).toNat),
          toeplitzSlice (-k) y (i + (-k).toNat)⟫_𝕜 := by
      have h := hG.sum_add_tsum_nat_add ((-k).toNat)
      have hzero : ∑ i ∈ Finset.range ((-k).toNat),
          ⟪(x : ℕ → 𝕜) i, toeplitzSlice (-k) y i⟫_𝕜 = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hik : ¬ -k ≤ (i : ℤ) := by
          rw [Finset.mem_range] at hi
          have hm : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (neg_nonneg.mpr hk')
          have hlt : (i : ℤ) < ((-k).toNat : ℤ) := by exact_mod_cast hi
          rw [hm] at hlt
          omega
        rw [toeplitzSlice_apply, toeplitzSliceFun_eq_zero_of_not_le hik]
        simp
      rw [hzero, zero_add] at h
      exact h.symm
    have hLHS : ∑' i, ⟪toeplitzSlice k x i, y i⟫_𝕜 =
        ∑' i, ⟪(x : ℕ → 𝕜) (i + (-k).toNat), y i⟫_𝕜 := by
      apply tsum_congr
      intro i
      rw [toeplitzSlice_apply, toeplitzSliceFun_of_nonpos hk']
    rw [hLHS, hshift]
    apply tsum_congr
    intro j
    rw [toeplitzSlice_apply, toeplitzSliceFun_add_of_nonneg (neg_nonneg.mpr hk')]

/-- A slice is adjoint to the slice at the negated index. -/
theorem adjoint_toeplitzSlice (k : ℤ) :
    (toeplitzSlice (𝕜 := 𝕜) k)† = toeplitzSlice (𝕜 := 𝕜) (-k) := by
  exact ((ContinuousLinearMap.eq_adjoint_iff (toeplitzSlice (𝕜 := 𝕜) (-k))
    (toeplitzSlice (𝕜 := 𝕜) k)).mpr (fun x y => by
      rw [toeplitzSlice_inner_symm (-k)]
      simp only [neg_neg])).symm

/-- The slice operators weighted by `a` are summable in operator norm when
`a` is absolutely summable. -/
theorem toeplitz_summable_slices {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    Summable fun k => (a k) • toeplitzSlice (𝕜 := 𝕜) k := by
  apply Summable.of_norm_bounded ha
  intro k
  calc ‖(a k) • toeplitzSlice (𝕜 := 𝕜) k‖ = ‖a k‖ * ‖toeplitzSlice (𝕜 := 𝕜) k‖ :=
        norm_smul _ _
    _ ≤ ‖a k‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (norm_toeplitzSlice_le k) (norm_nonneg _)
    _ = ‖a k‖ := mul_one _

/-- The Toeplitz operator with symbol `a`. Defined as the norm-convergent
series `∑' k, a k • toeplitzSlice k` over the diagonal slices. -/
noncomputable def toeplitzOperator (a : ℤ → 𝕜) (_ha : Summable fun k => ‖a k‖) :
    ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  ∑' k, (a k) • toeplitzSlice (𝕜 := 𝕜) k

/-- The Toeplitz operator is the sum of its slices. -/
theorem toeplitz_hasSum_slices {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    HasSum (fun k => (a k) • toeplitzSlice (𝕜 := 𝕜) k) (toeplitzOperator a ha) :=
  (toeplitz_summable_slices ha).hasSum

/-- Pointwise action of the Toeplitz operator:
`(Tₐ x) i = ∑' j, a (i - j) * x j`. -/
theorem toeplitzOperator_apply {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖)
    (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    toeplitzOperator a ha x i = ∑' j : ℕ, a ((i : ℤ) - (j : ℤ)) * x j := by
  have hsumm : Summable fun k => ((a k) • toeplitzSlice (𝕜 := 𝕜) k) x := by
    apply Summable.of_norm_bounded (ha.mul_right ‖x‖)
    intro k
    calc ‖((a k) • toeplitzSlice (𝕜 := 𝕜) k) x‖
        ≤ ‖(a k) • toeplitzSlice (𝕜 := 𝕜) k‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖a k‖ * ‖toeplitzSlice (𝕜 := 𝕜) k‖ * ‖x‖ := by rw [norm_smul]
      _ ≤ ‖a k‖ * 1 * ‖x‖ := by
          gcongr
          exact norm_toeplitzSlice_le k
      _ = ‖a k‖ * ‖x‖ := by ring
  have htsum_x : ∑' k, ((a k) • toeplitzSlice (𝕜 := 𝕜) k) x =
      toeplitzOperator a ha x := by
    have hHasX : HasSum (fun k => ((a k) • toeplitzSlice (𝕜 := 𝕜) k) x)
        (toeplitzOperator a ha x) :=
      (toeplitz_hasSum_slices ha).map (ContinuousLinearMap.apply 𝕜 (ℓ²(ℕ, 𝕜)) x)
        (ContinuousLinearMap.apply 𝕜 (ℓ²(ℕ, 𝕜)) x).continuous
    exact hHasX.tsum_eq
  have hcoord : (toeplitzOperator a ha x) i =
      ∑' k, a k * toeplitzSliceFun k (x : ℕ → 𝕜) i := by
    have h2 : (toeplitzOperator a ha x) i =
        ∑' k, (((a k) • toeplitzSlice (𝕜 := 𝕜) k) x) i := by
      rw [← htsum_x]
      show (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 i)
          (∑' k, ((a k) • toeplitzSlice (𝕜 := 𝕜) k) x) =
        ∑' k, (((a k) • toeplitzSlice (𝕜 := 𝕜) k) x) i
      rw [ContinuousLinearMap.map_tsum (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 i) hsumm]
      apply tsum_congr
      intro k
      rfl
    rw [h2]
    apply tsum_congr
    intro k
    simp [toeplitzSlice_apply, lp.coeFn_smul]
  rw [hcoord]
  -- Reindex `k ↦ i - k` (i.e. `j = i - k`): the terms with `k > i` vanish.
  have hF : Summable fun k => a k * toeplitzSliceFun k (x : ℕ → 𝕜) i := by
    apply Summable.of_norm_bounded (ha.mul_right ‖x‖)
    intro k
    rw [norm_mul]
    by_cases hik : k ≤ (i : ℤ)
    · rw [toeplitzSliceFun_apply, ite_eq_left hik]
      exact mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num) x (((i : ℤ) - k).toNat)) (norm_nonneg _)
    · rw [toeplitzSliceFun_apply, ite_eq_right hik, norm_zero, mul_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hHasF : HasSum (fun k => a k * toeplitzSliceFun k (x : ℕ → 𝕜) i)
      (toeplitzOperator a ha x i) := by
    rw [hcoord]
    exact hF.hasSum
  have hReindex : HasSum (fun j : ℕ => a ((i : ℤ) - (j : ℤ)) * x j)
      (toeplitzOperator a ha x i) := by
    have h2 : (fun j : ℕ => a ((i : ℤ) - (j : ℤ)) * x j) =
        (fun k => a k * toeplitzSliceFun k (x : ℕ → 𝕜) i) ∘
          (fun j : ℕ => (i : ℤ) - (j : ℤ)) := by
      funext j
      simp only [Function.comp_apply]
      rw [toeplitzSliceFun_apply,
        ite_eq_left (by omega : (i : ℤ) - (j : ℤ) ≤ (i : ℤ))]
      have h3 : (i : ℤ) - ((i : ℤ) - (j : ℤ)) = (j : ℤ) := by ring
      rw [h3, Int.toNat_natCast]
    rw [h2]
    exact (Function.Injective.hasSum_iff (g := fun j : ℕ => (i : ℤ) - (j : ℤ))
      (fun j₁ j₂ h => by
        have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by linarith
        exact_mod_cast hcast)
      (fun k hk => by
        by_cases hle : k ≤ (i : ℤ)
        · exfalso
          apply hk
          refine ⟨((i : ℤ) - k).toNat, ?_⟩
          show (i : ℤ) - ((((i : ℤ) - k).toNat : ℕ) : ℤ) = k
          rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
          ring
        · rw [toeplitzSliceFun_eq_zero_of_not_le hle, mul_zero])).mpr hHasF
  exact hHasF.tsum_eq.trans hReindex.tsum_eq.symm

/-- The zero symbol gives the zero operator. -/
theorem toeplitzOperator_zero : toeplitzOperator (0 : ℤ → 𝕜) (by simp) = 0 := by
  show (∑' k, (0 : ℤ → 𝕜) k • toeplitzSlice (𝕜 := 𝕜) k) = 0
  have hfun : (fun k => (0 : ℤ → 𝕜) k • toeplitzSlice (𝕜 := 𝕜) k) =
      fun _ => (0 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
    funext k
    rw [Pi.zero_apply]
    exact zero_smul 𝕜 (toeplitzSlice (𝕜 := 𝕜) k)
  rw [hfun, tsum_zero]

/-- Operator-norm bound: `‖Tₐ‖ ≤ ∑' k, ‖a k‖`. -/
theorem norm_toeplitzOperator_le {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    ‖toeplitzOperator a ha‖ ≤ ∑' k, ‖a k‖ :=
  (toeplitz_hasSum_slices ha).norm_le_of_bounded ha.hasSum (fun k => by
    calc ‖(a k) • toeplitzSlice (𝕜 := 𝕜) k‖ = ‖a k‖ * ‖toeplitzSlice (𝕜 := 𝕜) k‖ :=
          norm_smul _ _
      _ ≤ ‖a k‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_toeplitzSlice_le k) (norm_nonneg _)
      _ = ‖a k‖ := mul_one _)

/-- The adjoint symbol: `a* k = star (a (-k))`. -/
def toeplitzAdjointSymbol (a : ℤ → 𝕜) : ℤ → 𝕜 := fun k => star (a (-k))

/-- The adjoint symbol of an absolutely summable symbol is absolutely
summable. -/
theorem summable_norm_toeplitzAdjointSymbol {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    Summable fun k => ‖toeplitzAdjointSymbol a k‖ := by
  have h := ha.comp_injective (Equiv.neg ℤ).injective
  simpa [toeplitzAdjointSymbol, Function.comp_def, norm_star] using h

/-- Adjoint of a Toeplitz operator: `(Tₐ)† = T_{a*}`. -/
theorem adjoint_toeplitzOperator {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    (toeplitzOperator (𝕜 := 𝕜) a ha)† =
      toeplitzOperator (toeplitzAdjointSymbol a)
        (summable_norm_toeplitzAdjointSymbol ha) := by
  have hAdj : HasSum (fun k => ((a k) • toeplitzSlice (𝕜 := 𝕜) k)†)
      ((toeplitzOperator a ha)†) := by
    have hcont := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := ℓ²(ℕ, 𝕜))
      (F := ℓ²(ℕ, 𝕜))).continuous.tendsto (toeplitzOperator a ha)
    refine (hcont.comp (toeplitz_hasSum_slices ha)).congr'
      (Filter.Eventually.of_forall fun s => ?_)
    exact map_sum (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := ℓ²(ℕ, 𝕜))
      (F := ℓ²(ℕ, 𝕜))) _ _
  calc (toeplitzOperator (𝕜 := 𝕜) a ha)†
      = ∑' k, ((a k) • toeplitzSlice (𝕜 := 𝕜) k)† := hAdj.tsum_eq.symm
    _ = ∑' k, star (a k) • toeplitzSlice (𝕜 := 𝕜) (-k) := by
        apply tsum_congr
        intro k
        rw [map_smulₛₗ, adjoint_toeplitzSlice]
        simp only [starRingEnd_apply]
    _ = ∑' k, star (a (-k)) • toeplitzSlice (𝕜 := 𝕜) k := by
        rw [← (Equiv.neg ℤ).tsum_eq (fun k => star (a k) • toeplitzSlice (𝕜 := 𝕜) (-k))]
        apply tsum_congr
        intro k
        simp only [Equiv.neg_apply, neg_neg]
    _ = toeplitzOperator (toeplitzAdjointSymbol a)
          (summable_norm_toeplitzAdjointSymbol ha) := rfl

/-- The Toeplitz operator applied to a standard basis vector. -/
theorem toeplitzOperator_apply_single {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖)
    (j i : ℕ) :
    toeplitzOperator a ha (lp.single 2 j (1 : 𝕜)) i = a ((i : ℤ) - (j : ℤ)) := by
  rw [toeplitzOperator_apply ha,
    tsum_eq_single j (fun j' hj' => by simp [lp.single_apply, hj'])]
  simp [lp.single_apply]

/-- Self-adjointness of a Toeplitz operator iff the symbol satisfies
`star (a (-k)) = a k` for all `k`. -/
theorem isSelfAdjoint_toeplitzOperator_iff {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    IsSelfAdjoint (toeplitzOperator a ha) ↔ ∀ k : ℤ, star (a (-k)) = a k := by
  constructor
  · intro h
    have hAdj : (toeplitzOperator a ha)† =
        toeplitzOperator (toeplitzAdjointSymbol a)
          (summable_norm_toeplitzAdjointSymbol ha) := adjoint_toeplitzOperator ha
    have hstar : (toeplitzOperator a ha)† = toeplitzOperator a ha := h
    have hEq : toeplitzOperator (toeplitzAdjointSymbol a)
        (summable_norm_toeplitzAdjointSymbol ha) = toeplitzOperator a ha := by
      rw [← hAdj, hstar]
    have hcoord : ∀ i : ℕ, star (a (-(i : ℤ))) = a (i : ℤ) := by
      intro i
      have h2 : toeplitzOperator (toeplitzAdjointSymbol a)
          (summable_norm_toeplitzAdjointSymbol ha) (lp.single 2 0 (1 : 𝕜)) i =
          toeplitzOperator a ha (lp.single 2 0 (1 : 𝕜)) i := by rw [hEq]
      rw [toeplitzOperator_apply_single, toeplitzOperator_apply_single] at h2
      simp only [toeplitzAdjointSymbol, Nat.cast_zero, sub_zero] at h2
      exact h2
    intro k
    by_cases hk : 0 ≤ k
    · have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
      have h1 := hcoord k.toNat
      rw [show (-((k.toNat : ℤ))) = -k by rw [hcast]] at h1
      rw [hcast] at h1
      exact h1
    · have hk' : k < 0 := not_le.mp hk
      -- Apply the `ℕ` identity at `(-k).toNat` and conjugate.
      have hcast : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hk'))
      have h1 := hcoord (-k).toNat
      rw [show (-(((-k).toNat : ℤ))) = k by rw [hcast]; ring] at h1
      rw [hcast] at h1
      -- `h1 : star (a k) = a (-k)`; conjugate to get the goal.
      have h2 := congrArg star h1
      rw [star_star] at h2
      exact h2.symm
  · intro hsym
    show (toeplitzOperator a ha)† = toeplitzOperator a ha
    rw [adjoint_toeplitzOperator]
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    rw [toeplitzOperator_apply, toeplitzOperator_apply]
    apply tsum_congr
    intro j
    show star (a (-((i : ℤ) - (j : ℤ)))) * x j = a ((i : ℤ) - (j : ℤ)) * x j
    rw [hsym]

/-- A Toeplitz operator with a `star`-fixed adjoint symbol is self-adjoint. -/
theorem isSelfAdjoint_toeplitzOperator_of_forall_star {a : ℤ → 𝕜}
    (ha : Summable fun k => ‖a k‖) (hstar : ∀ k, star (a (-k)) = a k) :
    IsSelfAdjoint (toeplitzOperator a ha) :=
  (isSelfAdjoint_toeplitzOperator_iff ha).mpr hstar

/-- A symbol is `a (i - n) → 0` as `n → ∞`, for fixed `i`: the symbol
vanishes along the cofinite filter. -/
private theorem tendsto_toeplitzSymbol_sub_nat {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖)
    (i : ℕ) :
    Tendsto (fun n : ℕ => a ((i : ℤ) - (n : ℤ))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfin : {k : ℤ | ε ≤ ‖a k‖}.Finite := by
    have hev : ∀ᶠ k in Filter.cofinite, ‖a k‖ < ε :=
      ha.tendsto_cofinite_zero (Iio_mem_nhds hε)
    rw [Filter.eventually_cofinite] at hev
    simpa [not_lt] using hev
  obtain ⟨B, hB⟩ := hfin.bddBelow
  refine ⟨((i : ℤ) - B).toNat + 1, fun n hn => ?_⟩
  rw [dist_eq_norm, sub_zero]
  by_contra hcon
  have hmem : (i : ℤ) - (n : ℤ) ∈ {k : ℤ | ε ≤ ‖a k‖} := not_lt.mp hcon
  have hle : B ≤ (i : ℤ) - (n : ℤ) := hB hmem
  have hn2 : (((i : ℤ) - B).toNat + 1 : ℕ) ≤ n := hn
  have hn3 : ((((i : ℤ) - B).toNat + 1 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
  push_cast at hn3
  have hkey : (i : ℤ) - (n : ℤ) < B := by omega
  exact (lt_irrefl B (hle.trans_lt hkey))

/-- A Toeplitz operator with a nonzero symbol is not compact: the images
of the standard basis vectors converge coordinatewise to `0` but keep a
nonzero coordinate. -/
theorem not_isCompactOperator_toeplitzOperator_of_ne {a : ℤ → 𝕜}
    (ha : Summable fun k => ‖a k‖) {k₀ : ℤ} (hk₀ : a k₀ ≠ 0) :
    ¬ IsCompactOperator (toeplitzOperator a ha) := by
  intro hcomp
  obtain ⟨K, hK, hsub⟩ :=
    hcomp.image_subset_compact_of_bounded
      (Metric.isBounded_closedBall (x := (0 : ℓ²(ℕ, 𝕜))) (r := 1))
  have hmem : ∀ n : ℕ, toeplitzOperator a ha (lp.single 2 n (1 : 𝕜)) ∈ K := by
    intro n
    apply hsub
    refine ⟨lp.single 2 n (1 : 𝕜), ?_, rfl⟩
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    simp
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun n => hmem n)
  have hy0 : y = 0 := by
    apply lp.ext
    funext i
    have hcoord : Tendsto (fun n => toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)) i)
        atTop (𝓝 (y i)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h2 : Tendsto (fun n => toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)) - y)
          atTop (𝓝 0) := by
        have h := hlim.sub (tendsto_const_nhds (x := y))
        simpa using h
      have h3 : Tendsto (fun n => ‖toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)) - y‖)
          atTop (𝓝 0) := by
        have h := (continuous_norm.tendsto (0 : ℓ²(ℕ, 𝕜))).comp h2
        simpa only [Function.comp_def, norm_zero] using h
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun n => by
          have h := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by simp)
            (toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)) - y) i
          simpa using h)
    have hzero : Tendsto (fun n => toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)) i)
        atTop (𝓝 0) := by
      have h := (tendsto_toeplitzSymbol_sub_nat ha i).comp hφ.tendsto_atTop
      refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
      show a ((i : ℤ) - ((φ n : ℕ) : ℤ)) =
        toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)) i
      rw [toeplitzOperator_apply_single]
    have h : y i = 0 := tendsto_nhds_unique hcoord hzero
    rw [h]
    simp
  have hnorm : ‖a k₀‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    have hlim2 : Tendsto (fun n => ‖toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜))‖ ^ 2)
        atTop (𝓝 (‖y‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto y).comp hlim
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim2
    filter_upwards [Filter.eventually_ge_atTop ((-k₀).toNat)] with n hn
    -- The coordinate `i = k₀ + n` of `T e_{φ n}` is `a k₀`.
    have hle : ‖a k₀‖ ^ 2 ≤
        ∑' i, ‖toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)) i‖ ^ 2 := by
      have hterm : ‖toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜))
          ((k₀ + (φ n : ℤ)).toNat)‖ ^ 2 = ‖a k₀‖ ^ 2 := by
        rw [toeplitzOperator_apply_single]
        have hidx : ((k₀ + (φ n : ℤ)).toNat : ℤ) - (φ n : ℤ) = k₀ := by
          have hnn : 0 ≤ k₀ + (φ n : ℤ) := by
            by_cases hk : 0 ≤ k₀
            · exact add_nonneg hk (Nat.cast_nonneg _)
            · have hk' : k₀ < 0 := not_le.mp hk
              have hmk : ((-k₀).toNat : ℤ) = -k₀ :=
                Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hk'))
              have hφn : ((-k₀).toNat : ℤ) ≤ (φ n : ℤ) := by
                have hleφ : n ≤ φ n := hφ.id_le n
                have hle2 : (-k₀).toNat ≤ φ n := le_trans hn hleφ
                exact_mod_cast hle2
              rw [hmk] at hφn
              linarith
          rw [Int.toNat_of_nonneg hnn]
          ring
        rw [hidx]
      rw [← hterm]
      exact Summable.le_tsum
        (toeplitz_summable_normSq_of_memℓp
          (lp.memℓp (toeplitzOperator a ha (lp.single 2 (φ n) (1 : 𝕜)))))
        ((k₀ + (φ n : ℤ)).toNat) (fun j _ => by positivity)
    rw [← toeplitz_normSq_eq_tsum] at hle
    exact hle
  have h0 : ‖(0 : ℓ²(ℕ, 𝕜))‖ ^ 2 = 0 := by simp
  rw [hy0, h0] at hnorm
  have hsq : ‖a k₀‖ ^ 2 = 0 := le_antisymm hnorm (by positivity)
  exact hk₀ (norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq))

/-- A Toeplitz operator is compact iff its symbol is zero. -/
theorem isCompactOperator_toeplitzOperator_iff {a : ℤ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    IsCompactOperator (toeplitzOperator a ha) ↔ a = 0 := by
  constructor
  · intro hcomp
    by_contra hne
    obtain ⟨k₀, hk₀⟩ : ∃ k, a k ≠ 0 := Function.ne_iff.mp hne
    exact not_isCompactOperator_toeplitzOperator_of_ne ha hk₀ hcomp
  · intro h
    subst h
    rw [toeplitzOperator_zero]
    refine ⟨{0}, isCompact_singleton, ?_⟩
    rw [show (0 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) ⁻¹' {0} = Set.univ from by
      ext x; simp]
    exact Filter.univ_mem

/-- The delta symbol at `m` with value `c`. -/
def toeplitzDelta (m : ℤ) (c : 𝕜) : ℤ → 𝕜 := fun k => if k = m then c else 0

/-- A delta symbol is absolutely summable. -/
theorem summable_norm_toeplitzDelta (m : ℤ) (c : 𝕜) :
    Summable fun k => ‖toeplitzDelta m c k‖ := by
  refine summable_of_ne_finset_zero (s := {m}) ?_
  intro k hk
  simp only [Finset.mem_singleton] at hk
  simp [toeplitzDelta, hk]

/-- The `ℓ¹` norm of a delta symbol is `‖c‖`. -/
theorem tsum_norm_toeplitzDelta (m : ℤ) (c : 𝕜) :
    ∑' k, ‖toeplitzDelta m c k‖ = ‖c‖ := by
  rw [tsum_eq_single m]
  · simp [toeplitzDelta]
  · intro k hk
    simp [toeplitzDelta, hk]

/-- The operator norm of a Toeplitz operator with a delta symbol is `‖c‖`. -/
theorem norm_toeplitzOperator_delta (m : ℤ) (c : 𝕜) :
    ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)‖ = ‖c‖ := by
  apply le_antisymm
  · calc ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)‖
        ≤ ∑' k, ‖toeplitzDelta m c k‖ := norm_toeplitzOperator_le _
      _ = ‖c‖ := tsum_norm_toeplitzDelta m c
  · by_cases hm : 0 ≤ m
    · -- Witness vector `e₀`, coordinate `m`.
      have h1 : ‖c‖ ≤
          ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)
            (lp.single 2 0 (1 : 𝕜))‖ := by
        have hcoord : ‖c‖ = ‖toeplitzOperator (toeplitzDelta m c)
            (summable_norm_toeplitzDelta m c) (lp.single 2 0 (1 : 𝕜)) m.toNat‖ := by
          rw [toeplitzOperator_apply_single]
          have hidx : ((m.toNat : ℤ) - ((0 : ℕ) : ℤ)) = m := by
            rw [Nat.cast_zero, sub_zero]
            exact Int.toNat_of_nonneg hm
          rw [hidx]
          simp [toeplitzDelta]
        rw [hcoord]
        exact lp.norm_apply_le_norm (by norm_num) _ _
      calc ‖c‖ ≤ ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)
            (lp.single 2 0 (1 : 𝕜))‖ := h1
        _ ≤ ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)‖ := by
            have hle := ContinuousLinearMap.le_opNorm
              (toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c))
              (lp.single 2 0 (1 : 𝕜))
            rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one] at hle
            exact hle
    · have hm' : m < 0 := not_le.mp hm
      -- Witness vector `e_{(-m)}`, coordinate `0`.
      have h1 : ‖c‖ ≤
          ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)
            (lp.single 2 (-m).toNat (1 : 𝕜))‖ := by
        have hcoord : ‖c‖ = ‖toeplitzOperator (toeplitzDelta m c)
            (summable_norm_toeplitzDelta m c) (lp.single 2 (-m).toNat (1 : 𝕜)) 0‖ := by
          rw [toeplitzOperator_apply_single]
          have hidx : (((0 : ℕ) : ℤ) - (((-m).toNat : ℕ) : ℤ)) = m := by
            rw [Nat.cast_zero, zero_sub,
              Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hm')), neg_neg]
          rw [hidx]
          simp [toeplitzDelta]
        rw [hcoord]
        exact lp.norm_apply_le_norm (by norm_num) _ _
      calc ‖c‖ ≤ ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)
            (lp.single 2 (-m).toNat (1 : 𝕜))‖ := h1
        _ ≤ ‖toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c)‖ := by
            have hle := ContinuousLinearMap.le_opNorm
              (toeplitzOperator (toeplitzDelta m c) (summable_norm_toeplitzDelta m c))
              (lp.single 2 (-m).toNat (1 : 𝕜))
            rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, mul_one] at hle
            exact hle

end MathlibExt.Analysis.InnerProductSpace.ToeplitzOperator
