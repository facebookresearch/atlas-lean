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
# Hankel operators on `ℓ²(ℕ, 𝕜)` with absolutely summable symbol

A Hankel operator on `ℓ²(ℕ, 𝕜)` is the operator whose matrix is constant on
antidiagonals: for a symbol `a : ℕ → 𝕜`,
`(Hₐ x)ᵢ = ∑'ⱼ, a (i + j) * x j`.
The classical instance is the Hilbert matrix `a k = 1 / (k + 1)`, whose symbol
is *not* absolutely summable, so it is outside the scope of this file.
Here we treat absolutely summable symbols:

* `hankelSlice k` is the `k`-th anti-diagonal slice `Eₖ`, which reverses the
  first `k + 1` coordinates and kills the rest. It is a self-adjoint
  partial isometry of norm at most `1`.
* `hankelOperator a ha` is `∑' k, a k • hankelSlice k`, a norm-convergent
  series when `a` is absolutely summable (`∑' k, ‖a k‖ < ∞`).
* Boundedness: `‖Hₐ‖ ≤ ∑' k, ‖a k‖`, from the triangle inequality.
* Adjoint: `(Hₐ)† = H_{star a}`, since each slice is self-adjoint.
* Compactness: `Hₐ` is the norm limit of its finite partial sums, and each
  partial sum has finite-dimensional range (contained in the span of the
  first `N` standard basis vectors), hence is compact.

This is a companion to the Hilbert-space / compact-operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`. It is
not one of the 72 v1 targets. The matrix API in
`MathlibExt/LinearAlgebra/Matrix/Hankel.lean` defines the infinite matrix
`Matrix.hankel` on `ℕ × ℕ` and the finite matrix `Matrix.hankelFin`.
This file treats bounded Hankel operators on `ℓ²` with an `ℓ¹` symbol.
Boundedness comes from the anti-diagonal slice decomposition and the
triangle inequality, and compactness from the finite partial sums.
No Schur test is stated or proved here. An `ℓ¹`-symbol Hankel operator
need not be Hilbert–Schmidt, and no Hilbert–Schmidt norm is introduced here.

## Main declarations

* `hankelSlice k` : the `k`-th anti-diagonal slice, as a bounded operator.
* `hankelOperator a ha` : the Hankel operator with symbol `a`.
* `hankelOperator_apply` : `(Hₐ x) i = ∑' j, a (i + j) * x j`.
* `norm_hankelOperator_le` : `‖Hₐ‖ ≤ ∑' k, ‖a k‖`.
* `adjoint_hankelOperator` : `(Hₐ)† = H_{star a}`.
* `isSelfAdjoint_hankelOperator_of_forall_star` : `Hₐ` is self-adjoint for a
  real-valued (i.e. `star`-fixed) symbol.
* `isCompactOperator_hankelOperator` : `Hₐ` is a compact operator.
-/

@[expose] public section

open Filter Topology Set
open scoped _root_.lp ENNReal BigOperators InnerProductSpace InnerProduct

namespace MathlibExt.Analysis.InnerProductSpace.HankelOperator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `k`-th anti-diagonal slice function: reverse the first `k + 1`
coordinates, kill the rest. -/
def hankelSliceFun (k : ℕ) (x : ℕ → 𝕜) (i : ℕ) : 𝕜 :=
  if i ≤ k then x (k - i) else 0

@[simp] theorem hankelSliceFun_apply (k : ℕ) (x : ℕ → 𝕜) (i : ℕ) :
    hankelSliceFun k x i = if i ≤ k then x (k - i) else 0 := rfl

/-- The slice of an `ℓ²` sequence is in `ℓ²`. -/
theorem hankel_memℓp_sliceFun {k : ℕ} {x : ℓ²(ℕ, 𝕜)} :
    Memℓp (hankelSliceFun k (x : ℕ → 𝕜)) 2 := by
  apply (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  refine summable_of_ne_finset_zero (s := Finset.range (k + 1)) ?_
  intro i hi
  simp only [Finset.mem_range, not_lt] at hi
  simp [hankelSliceFun, show ¬ i ≤ k from by omega]

/-- The `k`-th anti-diagonal slice as a linear map. -/
noncomputable def hankelSliceLinMap (k : ℕ) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨hankelSliceFun k (x : ℕ → 𝕜), hankel_memℓp_sliceFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, Pi.add_apply, hankelSliceFun_apply]
    split_ifs with hi <;> simp
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hankelSliceFun_apply,
      RingHom.id_apply]
    split_ifs with hi <;> simp

/-- Pointwise action of the slice linear map. -/
theorem hankelSliceLinMap_apply (k : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    hankelSliceLinMap k x i = hankelSliceFun k (x : ℕ → 𝕜) i := rfl

/-- The (squared) norms of a sliced sequence sum to at most the squared
norms of the original sequence: only the first `k + 1` coordinates survive,
in reverse order. -/
theorem hankel_tsum_normSq_slice_le {k : ℕ} (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖hankelSliceFun k (x : ℕ → 𝕜) i‖ ^ 2 ≤ ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ 2 := by
  have hsum : ∑' i, ‖hankelSliceFun k (x : ℕ → 𝕜) i‖ ^ 2 =
      ∑ j ∈ Finset.range (k + 1), ‖(x : ℕ → 𝕜) j‖ ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range (k + 1))]
    · rw [← Finset.sum_range_reflect (fun j => ‖(x : ℕ → 𝕜) j‖ ^ 2) (k + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      have hik : i ≤ k := by omega
      simp [hankelSliceFun, hik]
    · intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      have hik : ¬ i ≤ k := by omega
      simp [hankelSliceFun, hik]
  rw [hsum]
  have hsumm := (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp (lp.memℓp x)
  have hsumm' : Summable fun i => ‖(x : ℕ → 𝕜) i‖ ^ 2 := by
    simpa using hsumm
  exact hsumm'.sum_le_tsum (Finset.range (k + 1)) (fun i _ => by positivity)

/-- A slice does not increase norms. -/
theorem norm_hankelSliceLinMap_apply_le (k : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    ‖hankelSliceLinMap k x‖ ≤ ‖x‖ := by
  have hpow : ‖hankelSliceLinMap k x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have hslice := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
      (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      (hankelSliceLinMap k x)
    have hx := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
      (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hslice hx
    rw [hslice, hx]
    exact hankel_tsum_normSq_slice_le x
  exact le_of_sq_le_sq hpow (norm_nonneg _)

/-- The `k`-th anti-diagonal slice as a bounded operator. -/
noncomputable def hankelSlice (k : ℕ) : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  (hankelSliceLinMap k).mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_hankelSliceLinMap_apply_le k x)

/-- Pointwise action of the slice operator. -/
theorem hankelSlice_apply (k : ℕ) (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    hankelSlice k x i = hankelSliceFun k (x : ℕ → 𝕜) i := rfl

/-- The operator norm of a slice is at most `1`. -/
theorem norm_hankelSlice_le (k : ℕ) : ‖hankelSlice (𝕜 := 𝕜) k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]
    exact norm_hankelSliceLinMap_apply_le k x)

/-- A slice is symmetric for the inner product: the anti-diagonal symmetry
is a finite-sum reflection. -/
theorem hankelSlice_inner_symm (k : ℕ) (x y : ℓ²(ℕ, 𝕜)) :
    ⟪hankelSlice k x, y⟫_𝕜 = ⟪x, hankelSlice k y⟫_𝕜 := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have key1 : ∀ z w : ℓ²(ℕ, 𝕜),
      ∑' i, ⟪hankelSlice k z i, w i⟫_𝕜 =
        ∑ j ∈ Finset.range (k + 1), ⟪z (k - j), w j⟫_𝕜 := by
    intro z w
    rw [tsum_eq_sum (s := Finset.range (k + 1))]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [hankelSlice_apply, hankelSliceFun_apply,
        ite_eq_left (by omega : i ≤ k)]
    · intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [hankelSlice_apply, hankelSliceFun_apply,
        ite_eq_right (by omega : ¬ i ≤ k)]
      simp
  have key2 : ∀ z w : ℓ²(ℕ, 𝕜),
      ∑' i, ⟪z i, hankelSlice k w i⟫_𝕜 =
        ∑ j ∈ Finset.range (k + 1), ⟪z j, w (k - j)⟫_𝕜 := by
    intro z w
    rw [tsum_eq_sum (s := Finset.range (k + 1))]
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [hankelSlice_apply, hankelSliceFun_apply,
        ite_eq_left (by omega : i ≤ k)]
    · intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [hankelSlice_apply, hankelSliceFun_apply,
        ite_eq_right (by omega : ¬ i ≤ k)]
      simp
  rw [key1, key2]
  -- reflect the finite sum: `∑ j ∈ range (k+1), ⟪x (k-j), y j⟫`
  -- equals `∑ j ∈ range (k+1), ⟪x j, y (k-j)⟫`.
  rw [← Finset.sum_range_reflect (fun j => ⟪x (k - j), y j⟫_𝕜) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hjk : j ≤ k := by omega
  have h2 : k - (k - j) = j := Nat.sub_sub_self hjk
  have h3 : (k + 1) - 1 - j = k - j := by omega
  rw [h3, h2]

/-- A slice is self-adjoint. -/
theorem adjoint_hankelSlice (k : ℕ) :
    (hankelSlice (𝕜 := 𝕜) k)† = hankelSlice (𝕜 := 𝕜) k :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr (hankelSlice_inner_symm k)).symm

/-- The slice operators weighted by `a` are summable in operator norm when
`a` is absolutely summable. -/
theorem hankel_summable_slices {a : ℕ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    Summable fun k => (a k) • hankelSlice (𝕜 := 𝕜) k := by
  apply Summable.of_norm_bounded ha
  intro k
  calc ‖(a k) • hankelSlice (𝕜 := 𝕜) k‖ = ‖a k‖ * ‖hankelSlice (𝕜 := 𝕜) k‖ :=
        norm_smul _ _
    _ ≤ ‖a k‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (norm_hankelSlice_le k) (norm_nonneg _)
    _ = ‖a k‖ := mul_one _

/-- The Hankel operator with symbol `a`. Defined as the norm-convergent
series `∑' k, a k • hankelSlice k` over the anti-diagonal slices. -/
noncomputable def hankelOperator (a : ℕ → 𝕜) (_ha : Summable fun k => ‖a k‖) :
    ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  ∑' k, (a k) • hankelSlice (𝕜 := 𝕜) k

/-- The Hankel operator is the sum of its slices. -/
theorem hankel_hasSum_slices {a : ℕ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    HasSum (fun k => (a k) • hankelSlice (𝕜 := 𝕜) k) (hankelOperator a ha) :=
  (hankel_summable_slices ha).hasSum

/-- Pointwise action of the Hankel operator: `(Hₐ x) i = ∑' j, a (i + j) * x j`. -/
theorem hankelOperator_apply {a : ℕ → 𝕜} (ha : Summable fun k => ‖a k‖)
    (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    hankelOperator a ha x i = ∑' j, a (i + j) * x j := by
  have hsumm : Summable fun k => ((a k) • hankelSlice (𝕜 := 𝕜) k) x := by
    apply Summable.of_norm_bounded (ha.mul_right ‖x‖)
    intro k
    calc ‖((a k) • hankelSlice (𝕜 := 𝕜) k) x‖
        ≤ ‖(a k) • hankelSlice (𝕜 := 𝕜) k‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖a k‖ * ‖hankelSlice (𝕜 := 𝕜) k‖ * ‖x‖ := by rw [norm_smul]
      _ ≤ ‖a k‖ * 1 * ‖x‖ := by
          gcongr
          exact norm_hankelSlice_le k
      _ = ‖a k‖ * ‖x‖ := by ring
  have hT : Tendsto (fun N => ∑ k ∈ Finset.range N, ((a k) • hankelSlice (𝕜 := 𝕜) k) x)
      atTop (𝓝 (hankelOperator a ha x)) := by
    have h := (hankel_hasSum_slices ha).tendsto_sum_nat
    have hc := (ContinuousLinearMap.apply 𝕜 (ℓ²(ℕ, 𝕜)) x).continuous.tendsto
      (hankelOperator a ha)
    have hcomp := hc.comp h
    refine hcomp.congr (fun N => ?_)
    simp only [Function.comp_def, ContinuousLinearMap.apply_apply, FunLike.coe_sum,
      Finset.sum_apply]
  have htsum_x : ∑' k, ((a k) • hankelSlice (𝕜 := 𝕜) k) x = hankelOperator a ha x :=
    tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat hT
  have hcoord : (hankelOperator a ha x) i = ∑' k, a k * hankelSliceFun k (x : ℕ → 𝕜) i := by
    have h2 : (hankelOperator a ha x) i =
        ∑' k, (((a k) • hankelSlice (𝕜 := 𝕜) k) x) i := by
      rw [← htsum_x]
      show (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 i)
          (∑' k, ((a k) • hankelSlice (𝕜 := 𝕜) k) x) =
        ∑' k, (((a k) • hankelSlice (𝕜 := 𝕜) k) x) i
      rw [ContinuousLinearMap.map_tsum (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 2 i) hsumm]
      apply tsum_congr
      intro k
      rfl
    rw [h2]
    apply tsum_congr
    intro k
    simp [hankelSlice_apply, lp.coeFn_smul]
  rw [hcoord]
  -- Shift the series: terms with `k < i` vanish, and `k = i + j` gives the
  -- Hankel entry `a (i + j) * x j`.
  have hF : Summable fun k => a k * hankelSliceFun k (x : ℕ → 𝕜) i := by
    apply Summable.of_norm_bounded (ha.mul_right ‖x‖)
    intro k
    rw [norm_mul]
    by_cases hik : i ≤ k
    · rw [hankelSliceFun_apply, ite_eq_left hik]
      exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) x (k - i))
        (norm_nonneg _)
    · rw [hankelSliceFun_apply, ite_eq_right hik, norm_zero, mul_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hshift : ∑' k, a k * hankelSliceFun k (x : ℕ → 𝕜) i =
      ∑' k, (fun k => a k * hankelSliceFun k (x : ℕ → 𝕜) i) (k + i) := by
    have h := hF.sum_add_tsum_nat_add i
    have hzero : ∑ k ∈ Finset.range i, a k * hankelSliceFun k (x : ℕ → 𝕜) i = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [hankelSliceFun_apply, ite_eq_right (by omega : ¬ i ≤ k)]
      simp
    rw [hzero, zero_add] at h
    exact h.symm
  rw [hshift]
  apply tsum_congr
  intro j
  simp only [hankelSliceFun_apply, ite_eq_left (by omega : i ≤ i + j),
    Nat.add_sub_cancel_left, add_comm j i]

/-- The zero symbol gives the zero operator. -/
theorem hankelOperator_zero : hankelOperator (0 : ℕ → 𝕜) (by simp) = 0 := by
  show (∑' k, (0 : ℕ → 𝕜) k • hankelSlice (𝕜 := 𝕜) k) = 0
  have hfun : (fun k => (0 : ℕ → 𝕜) k • hankelSlice (𝕜 := 𝕜) k) =
      fun _ => (0 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
    funext k
    rw [Pi.zero_apply]
    exact zero_smul 𝕜 (hankelSlice (𝕜 := 𝕜) k)
  rw [hfun, tsum_zero]

/-- Operator-norm bound: `‖Hₐ‖ ≤ ∑' k, ‖a k‖`. -/
theorem norm_hankelOperator_le {a : ℕ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    ‖hankelOperator a ha‖ ≤ ∑' k, ‖a k‖ :=
  (hankel_hasSum_slices ha).norm_le_of_bounded ha.hasSum (fun k => by
    calc ‖(a k) • hankelSlice (𝕜 := 𝕜) k‖ = ‖a k‖ * ‖hankelSlice (𝕜 := 𝕜) k‖ :=
          norm_smul _ _
      _ ≤ ‖a k‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_hankelSlice_le k) (norm_nonneg _)
      _ = ‖a k‖ := mul_one _)

/-- Adjoint of a Hankel operator: `(Hₐ)† = H_{star a}`, by passing the
adjoint through the finite partial sums and taking the limit. -/
theorem adjoint_hankelOperator {a : ℕ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    (hankelOperator (𝕜 := 𝕜) a ha)† =
      hankelOperator (star a) (by simpa using ha) := by
  have h1 : Tendsto (fun N => ∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k)
      atTop (𝓝 (hankelOperator a ha)) :=
    (hankel_hasSum_slices ha).tendsto_sum_nat
  have h2 : Tendsto (fun N => (∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k)†)
      atTop (𝓝 ((hankelOperator (𝕜 := 𝕜) a ha)†)) := by
    have hc := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := ℓ²(ℕ, 𝕜))
      (F := ℓ²(ℕ, 𝕜))).continuous.tendsto (hankelOperator a ha)
    exact hc.comp h1
  have h3 : ∀ N, (∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k)† =
      ∑ k ∈ Finset.range N, (star a) k • hankelSlice (𝕜 := 𝕜) k := by
    intro N
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [map_smulₛₗ, starRingEnd_apply, adjoint_hankelSlice, Pi.star_apply]
  have h4 : Tendsto (fun N => ∑ k ∈ Finset.range N, (star a) k • hankelSlice (𝕜 := 𝕜) k)
      atTop (𝓝 (hankelOperator (star a) (by simpa using ha))) :=
    (hankel_hasSum_slices (by simpa using ha)).tendsto_sum_nat
  have h2' : Tendsto (fun N => ∑ k ∈ Finset.range N, (star a) k • hankelSlice (𝕜 := 𝕜) k)
      atTop (𝓝 ((hankelOperator (𝕜 := 𝕜) a ha)†)) :=
    h2.congr' (Filter.Eventually.of_forall h3)
  exact tendsto_nhds_unique h2' h4

/-- A Hankel operator with a real-valued (`star`-fixed) symbol is
self-adjoint. -/
theorem isSelfAdjoint_hankelOperator_of_forall_star {a : ℕ → 𝕜}
    (ha : Summable fun k => ‖a k‖) (hstar : ∀ k, star (a k) = a k) :
    IsSelfAdjoint (hankelOperator a ha) := by
  show (hankelOperator (𝕜 := 𝕜) a ha)† = hankelOperator a ha
  rw [adjoint_hankelOperator]
  show (∑' k, (star a) k • hankelSlice (𝕜 := 𝕜) k) =
    ∑' k, a k • hankelSlice (𝕜 := 𝕜) k
  simp only [Pi.star_apply, hstar]

/-- A slice lands in the span of the first `k + 1` standard basis vectors. -/
private theorem hankelSlice_mem_span (k : ℕ) (x : ℓ²(ℕ, 𝕜)) :
    hankelSlice (𝕜 := 𝕜) k x ∈
      Submodule.span 𝕜 (Set.range (fun i : Fin (k + 1) => lp.single 2 (i : ℕ) (1 : 𝕜))) := by
  have hdecomp : hankelSlice (𝕜 := 𝕜) k x =
      ∑ i ∈ Finset.range (k + 1), ((hankelSlice (𝕜 := 𝕜) k x) i) • lp.single 2 i (1 : 𝕜) := by
    apply lp.ext
    funext j
    rw [lp.coeFn_sum]
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply,
      Finset.sum_apply, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hj : j ∈ Finset.range (k + 1)
    · rw [ite_eq_left hj]
      simp
    · rw [ite_eq_right hj]
      simp only [Finset.mem_range, not_lt] at hj
      rw [hankelSlice_apply, hankelSliceFun_apply, ite_eq_right (by omega : ¬ j ≤ k)]
  rw [hdecomp]
  apply Submodule.sum_mem
  intro i hi
  simp only [Finset.mem_range] at hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

/-- A finite partial sum of the slice series has finite-dimensional range,
hence is a compact operator. -/
theorem hankel_isCompactOperator_partialSum {a : ℕ → 𝕜} (N : ℕ) :
    IsCompactOperator ((∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k :
      ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))) := by
  let V : Submodule 𝕜 (ℓ²(ℕ, 𝕜)) :=
    Submodule.span 𝕜 (Set.range (fun i : Fin N => lp.single 2 (i : ℕ) (1 : 𝕜)))
  have hVfin : FiniteDimensional 𝕜 ↥V :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  have hVproper : ProperSpace ↥V := FiniteDimensional.proper 𝕜 ↥V
  have hmem : ∀ x, (∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k) x ∈ V := by
    intro x
    rw [FunLike.coe_sum, Finset.sum_apply]
    apply Submodule.sum_mem
    intro k hk
    simp only [Finset.mem_range] at hk
    apply Submodule.smul_mem
    have hsub : (Submodule.span 𝕜
        (Set.range (fun i : Fin (k + 1) => lp.single 2 (i : ℕ) (1 : 𝕜)))) ≤ V := by
      apply Submodule.span_mono
      intro z hz
      obtain ⟨i, rfl⟩ := hz
      exact ⟨⟨(i : ℕ), by omega⟩, by rfl⟩
    exact hsub (hankelSlice_mem_span k x)
  have hfactor : (∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k) =
      V.subtypeL ∘L (ContinuousLinearMap.codRestrict
        (∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k) V hmem) := by
    ext x
    rfl
  rw [hfactor, ContinuousLinearMap.coe_comp]
  exact (isCompactOperator_of_locallyCompactSpace_rng V.subtypeL).comp_clm _

/-- A Hankel operator with an absolutely summable symbol is compact:
it is the norm limit of its finite partial sums, each of which has
finite-dimensional range. -/
theorem isCompactOperator_hankelOperator {a : ℕ → 𝕜} (ha : Summable fun k => ‖a k‖) :
    IsCompactOperator (hankelOperator a ha) := by
  have hT : Tendsto (fun N => ∑ k ∈ Finset.range N, (a k) • hankelSlice (𝕜 := 𝕜) k)
      atTop (𝓝 (hankelOperator a ha)) :=
    (hankel_hasSum_slices ha).tendsto_sum_nat
  apply isCompactOperator_of_tendsto hT
  exact Filter.Eventually.of_forall fun N => hankel_isCompactOperator_partialSum N

end MathlibExt.Analysis.InnerProductSpace.HankelOperator
