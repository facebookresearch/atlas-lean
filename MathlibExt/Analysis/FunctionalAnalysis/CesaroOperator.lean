/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.PSeries
public import MathlibExt.Analysis.Series.HardyInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The Cesàro operator on `ℓ²(ℕ, 𝕜)`

The Cesàro operator sends a square-summable sequence `x` to the sequence of
its prefix averages:
`(C x) n = (x 0 + ⋯ + x n) / (n + 1)`.
It is a bounded operator on `ℓ²(ℕ, 𝕜)` with `‖C‖ ≤ 2`, by Hardy's inequality
for series (in `MathlibExt`, `MetaMathlibExt.hardy_inequality`, at `p = 2`).
It is injective, but neither surjective nor self-adjoint nor compact.

This is a companion to the Fejér / Cesàro-summation material of the v1 book
`IntroductionToFunctionalAnalysis` (the Fejér kernel and Cesàro means of
Fourier series were ported in batch 1); the operator on `ℓ²` is a different
object, and it is not one of the 72 v1 targets. It is not in the pinned
Mathlib or in base MathlibExt.

Classical reference: G. H. Hardy, *Note on a theorem of Hilbert*,
Math. Z. 6 (1920), 314–317 (Hardy's inequality, which gives boundedness);
see also Brown, Halmos and Shields, *Cesàro operators*, Acta Sci. Math.
26 (1965), 125–137 (spectral theory; the spectrum is not proved here).

## Main declarations

* `cesaroCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)` : the Cesàro operator.
* `cesaroCLM_apply` : `(C x) n = (∑ k ∈ range (n + 1), x k) / (n + 1)`.
* `norm_cesaroCLM_le` : `‖C‖ ≤ 2`.
* `one_le_norm_cesaroCLM` : `1 ≤ ‖C‖`.
* `cesaroCLM_injective` : `C` is injective.
* `notMem_range_cesaroCLM` : `C` is not surjective.
* `cesaro_adjoint_apply` : `(C† y) n = ∑' k, y (n + k) / (n + k + 1)`.
* `not_isSelfAdjoint_cesaroCLM` : `C` is not self-adjoint.
* `not_isCompactOperator_cesaroCLM` : `C` is not compact.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.CesaroOperator

open Filter Topology Finset
open scoped ENNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The space `ℓ²(ℕ, 𝕜)`. -/
abbrev CesaroSpace (𝕜 : Type*) [RCLike 𝕜] := lp (fun _ : ℕ => 𝕜) 2

/-- The `n`-th Cesàro mean (prefix average) of a sequence. -/
def cesaroMean (x : ℕ → 𝕜) (n : ℕ) : 𝕜 :=
  (∑ k ∈ Finset.range (n + 1), x k) / ((n : 𝕜) + 1)

/-- The denominator `(n : 𝕜) + 1` is nonzero. -/
lemma cesaro_den_ne_zero (n : ℕ) : ((n : 𝕜) + 1) ≠ 0 := by
  rw [← Nat.cast_add_one (R := 𝕜) n]
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)

/-- The norm of the denominator is `n + 1`. -/
lemma norm_cesaro_den (n : ℕ) : ‖((n : 𝕜) + 1)‖ = (n : ℝ) + 1 := by
  rw [← Nat.cast_add_one (R := 𝕜) n, norm_natCast]
  norm_cast

/-- A Cesàro mean is bounded by the average of the norms. -/
lemma norm_cesaroMean_le (x : ℕ → 𝕜) (n : ℕ) :
    ‖cesaroMean x n‖ ≤ (∑ k ∈ Finset.range (n + 1), ‖x k‖) / ((n : ℝ) + 1) := by
  rw [cesaroMean, norm_div, norm_cesaro_den]
  exact div_le_div_of_nonneg_right (norm_sum_le _ _) (by positivity)

/-- The squared norms of the Cesàro means of an `ℓ²` sequence are summable,
by Hardy's inequality at `p = 2`. -/
lemma summable_norm_sq_cesaroMean (x : CesaroSpace 𝕜) :
    Summable fun n => ‖cesaroMean (x : ℕ → 𝕜) n‖ ^ (2 : ℝ) := by
  have hx : Summable fun n => ‖(x : ℕ → 𝕜) n‖ ^ (2 : ℝ) := by
    have h := (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by simp)
    simpa using h
  obtain ⟨hsumm, _⟩ := MetaMathlibExt.hardy_inequality
    (a := fun n => ‖(x : ℕ → 𝕜) n‖) (p := 2) (by norm_num) (fun _ => norm_nonneg _)
    (by simpa [Real.rpow_two] using hx)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hsumm
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_cesaroMean_le _ _) (by norm_num)

/-- The Cesàro means of an `ℓ²` sequence form an `ℓ²` sequence. -/
lemma memℓp_cesaroMean (x : CesaroSpace 𝕜) : Memℓp (cesaroMean (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  simpa using summable_norm_sq_cesaroMean x

/-- The Cesàro operator as a linear map. -/
def cesaroLinearMap : CesaroSpace 𝕜 →ₗ[𝕜] CesaroSpace 𝕜 where
  toFun x := ⟨cesaroMean (x : ℕ → 𝕜), memℓp_cesaroMean x⟩
  map_add' x y := by
    ext n
    simp only [cesaroMean, lp.coeFn_add, Pi.add_apply]
    rw [Finset.sum_add_distrib, add_div]
  map_smul' c x := by
    ext n
    simp only [cesaroMean, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum, mul_div_assoc]

/-- The Cesàro operator is bounded by `2`. -/
lemma norm_cesaroLinearMap_le (x : CesaroSpace 𝕜) :
    ‖cesaroLinearMap (𝕜 := 𝕜) x‖ ≤ 2 * ‖x‖ := by
  have hx : Summable fun n => ‖(x : ℕ → 𝕜) n‖ ^ (2 : ℝ) := by
    have h := (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by simp)
    simpa using h
  obtain ⟨hsumm, hle⟩ := MetaMathlibExt.hardy_inequality
    (a := fun n => ‖(x : ℕ → 𝕜) n‖) (p := 2) (by norm_num) (fun _ => norm_nonneg _)
    (by simpa [Real.rpow_two] using hx)
  have hnormx : ‖x‖ ^ (2 : ℝ) = ∑' n, ‖(x : ℕ → 𝕜) n‖ ^ (2 : ℝ) :=
    lp.norm_rpow_eq_tsum (by simp) _
  apply lp.norm_le_of_tsum_le (p := (2 : ℝ≥0∞)) (by simp) (by positivity)
  have hto : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [hto]
  calc ∑' n, ‖cesaroLinearMap (𝕜 := 𝕜) x n‖ ^ (2 : ℝ)
      ≤ ∑' n, ((∑ k ∈ Finset.range (n + 1), ‖(x : ℕ → 𝕜) k‖) / ((n : ℝ) + 1)) ^ (2 : ℝ) :=
        Summable.tsum_le_tsum
          (fun n => Real.rpow_le_rpow (norm_nonneg _) (norm_cesaroMean_le _ _) (by norm_num))
          (summable_norm_sq_cesaroMean x) hsumm
    _ ≤ (2 / (2 - 1)) ^ (2 : ℝ) * ∑' n, ‖(x : ℕ → 𝕜) n‖ ^ (2 : ℝ) := hle
    _ = (2 * ‖x‖) ^ (2 : ℝ) := by
        rw [← hnormx, Real.mul_rpow (by norm_num) (norm_nonneg _)]
        norm_num

/-- The Cesàro operator as a continuous linear map. -/
def cesaroCLM : CesaroSpace 𝕜 →L[𝕜] CesaroSpace 𝕜 :=
  LinearMap.mkContinuous cesaroLinearMap 2 (fun x => norm_cesaroLinearMap_le x)

/-- The evaluation formula for the Cesàro operator. -/
theorem cesaroCLM_apply (x : CesaroSpace 𝕜) (n : ℕ) :
    cesaroCLM (𝕜 := 𝕜) x n = (∑ k ∈ Finset.range (n + 1), (x : ℕ → 𝕜) k) / ((n : 𝕜) + 1) :=
  rfl

/-- The partial sums of `x` are recovered from `C x`. -/
lemma cesaro_sum_eq (x : CesaroSpace 𝕜) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (x : ℕ → 𝕜) k) = ((n : 𝕜) + 1) * cesaroCLM (𝕜 := 𝕜) x n := by
  rw [cesaroCLM_apply]
  field_simp

/-- The Cesàro operator applied to `x` equals the linear map applied to `x`. -/
lemma cesaroCLM_eq (x : CesaroSpace 𝕜) :
    cesaroCLM (𝕜 := 𝕜) x = cesaroLinearMap (𝕜 := 𝕜) x :=
  rfl

/-- The Cesàro operator has operator norm at most `2`. -/
theorem norm_cesaroCLM_le : ‖cesaroCLM (𝕜 := 𝕜)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound (cesaroCLM (𝕜 := 𝕜)) (by norm_num)
  intro x
  rw [cesaroCLM_eq]
  exact norm_cesaroLinearMap_le x

/-- The first basis vector `e₀` of `ℓ²(ℕ, 𝕜)`. -/
def cesaroE0 : CesaroSpace 𝕜 := lp.single (E := fun _ : ℕ => 𝕜) 2 0 (1 : 𝕜)

/-- The coordinates of `e₀`. -/
lemma cesaroE0_apply (n : ℕ) : cesaroE0 (𝕜 := 𝕜) n = if n = 0 then 1 else 0 := by
  by_cases h : n = 0
  · subst h
    simp [cesaroE0]
  · simp [cesaroE0, h]

/-- The norm of `e₀` is `1`. -/
lemma norm_cesaroE0 : ‖cesaroE0 (𝕜 := 𝕜)‖ = 1 := by
  rw [cesaroE0, lp.norm_single (E := fun _ : ℕ => 𝕜) (p := (2 : ℝ≥0∞)) (by simp)]
  simp

/-- The Cesàro operator has operator norm at least `1`, seen on `e₀`. -/
theorem one_le_norm_cesaroCLM : 1 ≤ ‖cesaroCLM (𝕜 := 𝕜)‖ := by
  have h1 : ‖cesaroCLM (𝕜 := 𝕜) cesaroE0 0‖ ≤ ‖cesaroCLM (𝕜 := 𝕜) cesaroE0‖ :=
    lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by simp) _ _
  have h2 : cesaroCLM (𝕜 := 𝕜) cesaroE0 0 = 1 := by
    rw [cesaroCLM_apply]
    simp [cesaroE0_apply]
  have h3 : ‖cesaroCLM (𝕜 := 𝕜) cesaroE0‖ ≤ ‖cesaroCLM (𝕜 := 𝕜)‖ * ‖cesaroE0 (𝕜 := 𝕜)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h4 : ‖cesaroE0 (𝕜 := 𝕜)‖ = 1 := norm_cesaroE0
  rw [h2, norm_one] at h1
  rw [h4, mul_one] at h3
  exact h1.trans h3

/-- One step of the inversion of the Cesàro operator: `x (n+1)` is a
difference of two consecutive values of `C x`. -/
lemma cesaro_preimage_succ (x : CesaroSpace 𝕜) (n : ℕ) :
    (x : ℕ → 𝕜) (n + 1) =
      ((n : 𝕜) + 2) * cesaroCLM (𝕜 := 𝕜) x (n + 1) -
        ((n : 𝕜) + 1) * cesaroCLM (𝕜 := 𝕜) x n := by
  have h1 := cesaro_sum_eq x (n + 1)
  have h2 := cesaro_sum_eq x n
  rw [Finset.sum_range_succ] at h1
  rw [h2] at h1
  push_cast at h1 ⊢
  linear_combination h1

/-- The Cesàro operator is injective. -/
theorem cesaroCLM_injective : Function.Injective (cesaroCLM (𝕜 := 𝕜)) := by
  intro x y h
  have hC : ∀ m, cesaroCLM (𝕜 := 𝕜) x m = cesaroCLM (𝕜 := 𝕜) y m := fun m => by rw [h]
  ext n
  induction n with
  | zero =>
    have hx := cesaro_sum_eq x 0
    have hy := cesaro_sum_eq y 0
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_mul] at hx hy
    rw [hx, hy, hC]
  | succ n _ =>
    rw [cesaro_preimage_succ x n, cesaro_preimage_succ y n, hC, hC]

/-- The sequence `y n = (-1)^n / (n + 1)`. -/
def cesaroNonRange : CesaroSpace 𝕜 :=
  ⟨fun n => (-1 : 𝕜) ^ n / ((n : 𝕜) + 1), by
    apply memℓp_gen
    have hto : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [hto]
    have hnorm : ∀ n : ℕ, ‖(-1 : 𝕜) ^ n / ((n : 𝕜) + 1)‖ = 1 / ((n : ℝ) + 1) := by
      intro n
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_cesaro_den, one_div]
    have hs : Summable fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ (2 : ℝ) := by
      have h1 : Summable fun n : ℕ => (1 / (n : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 / (n : ℝ) ^ 2)) 1).mpr h1
      refine h2.congr (fun n => ?_)
      rw [Real.rpow_two, div_pow, one_pow]
      norm_cast
    exact hs.congr fun n => by rw [hnorm n]⟩

/-- The coordinates of `cesaroNonRange`. -/
lemma cesaroNonRange_apply (n : ℕ) :
    cesaroNonRange (𝕜 := 𝕜) n = (-1 : 𝕜) ^ n / ((n : 𝕜) + 1) :=
  rfl

/-- The Cesàro operator is not surjective: `y n = (-1)^n / (n + 1)` is not
in its range, since a preimage would have to be `x (n + 1) = -2 (-1)^n`,
which is not square-summable. -/
theorem notMem_range_cesaroCLM : cesaroNonRange (𝕜 := 𝕜) ∉ Set.range (cesaroCLM (𝕜 := 𝕜)) := by
  rintro ⟨x, hx⟩
  have hCx : ∀ m, cesaroCLM (𝕜 := 𝕜) x m = cesaroNonRange (𝕜 := 𝕜) m := fun m => by rw [hx]
  have hform : ∀ n : ℕ, (x : ℕ → 𝕜) (n + 1) = -2 * (-1 : 𝕜) ^ n := by
    intro n
    have hpre := cesaro_preimage_succ x n
    rw [hCx (n + 1), hCx n, cesaroNonRange_apply (n + 1), cesaroNonRange_apply n] at hpre
    have hne1 : ((n : 𝕜) + 1) ≠ 0 := cesaro_den_ne_zero n
    have hne2 : ((n : 𝕜) + 2) ≠ 0 := by
      have h : ((n + 2 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at h
      exact h
    have hca : ((n + 1 : ℕ) : 𝕜) + 1 = (n : 𝕜) + 2 := by push_cast; ring
    rw [hca] at hpre
    have key1 : ((n : 𝕜) + 2) * ((-1 : 𝕜) ^ (n + 1) / ((n : 𝕜) + 2)) = (-1 : 𝕜) ^ (n + 1) := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _ hne2
    have key2 : ((n : 𝕜) + 1) * ((-1 : 𝕜) ^ n / ((n : 𝕜) + 1)) = (-1 : 𝕜) ^ n := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ _ hne1
    rw [key1, key2, pow_succ] at hpre
    rw [hpre]
    ring
  have hnorm : ∀ n : ℕ, ‖(x : ℕ → 𝕜) (n + 1)‖ = 2 := by
    intro n
    rw [hform n, norm_mul, norm_neg, norm_pow, norm_neg, norm_one, one_pow]
    norm_num
  have hsumm := (lp.memℓp x).summable (p := (2 : ℝ≥0∞)) (by simp)
  have hlim := hsumm.tendsto_atTop_zero
  have hev := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hNlt, hNge⟩ := (hev.and (eventually_ge_atTop 1)).exists
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hbig : ‖(x : ℕ → 𝕜) (m + 1)‖ ^ (2 : ℝ≥0∞).toReal = 4 := by
    rw [hnorm m]
    simp
    norm_num
  have hlt : ‖(x : ℕ → 𝕜) (m + 1)‖ ^ (2 : ℝ≥0∞).toReal < 1 := hNlt
  rw [hbig] at hlt
  norm_num at hlt

/-- The Cesàro operator applied to a basis vector. -/
lemma cesaroCLM_single_apply (n k : ℕ) :
    cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)) k =
      if n ≤ k then 1 / ((k : 𝕜) + 1) else 0 := by
  rw [cesaroCLM_apply]
  by_cases h : n ≤ k
  · simp only [h, ite_true]
    have hsum : (∑ j ∈ Finset.range (k + 1),
        lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜) j) = 1 := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hbne
        simp only [lp.coeFn_single, Pi.single_apply, hbne, ite_false]
      · intro hcon
        exact absurd (Finset.mem_range.mpr (by omega : n < k + 1)) hcon
    rw [hsum]
  · simp only [h, ite_false]
    have hsum : (∑ j ∈ Finset.range (k + 1),
        lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜) j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjn : j ≠ n := by
        have hj' := Finset.mem_range.mp hj
        omega
      simp only [lp.coeFn_single, Pi.single_apply, hjn, ite_false]
    rw [hsum, zero_div]

/-- The adjoint of the Cesàro operator, coordinatewise: the adjoint is the
tail-sum operator `(C† y) n = ∑' k, y (n + k) / (n + k + 1)`. -/
theorem cesaro_adjoint_apply (y : CesaroSpace 𝕜) (n : ℕ) :
    ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := 𝕜)) y n =
      ∑' k, (y : ℕ → 𝕜) (n + k) / (((n + k : ℕ) : 𝕜) + 1) := by
  have hsingle : ∀ (f : CesaroSpace 𝕜), inner 𝕜 (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)) (f)
      = f n := by
    intro f
    rw [lp.inner_single_left]
    simp [RCLike.inner_apply]
  have hstep1 : inner 𝕜 (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)) (ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := 𝕜)) y)
      = inner 𝕜 (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜))) (y) := by
    calc inner 𝕜 (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)) (ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := 𝕜)) y)
          = starRingEnd 𝕜 (inner 𝕜 (ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := 𝕜)) y)
              (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜))) := (inner_conj_symm _ _).symm
        _ = starRingEnd 𝕜 (inner 𝕜 y
              (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)))) := by
          rw [ContinuousLinearMap.adjoint_inner_left]
        _ = inner 𝕜 (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜))) y :=
          inner_conj_symm _ _
  have hstep2 : inner 𝕜 (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜))) (y)
      = ∑' k, inner 𝕜 (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)) k) ((y : ℕ → 𝕜) k) :=
    lp.inner_eq_tsum _ _
  have hterm : ∀ k : ℕ, inner 𝕜 (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)) k) ((y : ℕ → 𝕜) k) = if n ≤ k then (y : ℕ → 𝕜) k / ((k : 𝕜) + 1) else 0 := by
    intro k
    rw [RCLike.inner_apply, cesaroCLM_single_apply]
    by_cases h : n ≤ k
    · simp only [h, ite_true]
      have hstar : starRingEnd 𝕜 (1 / ((k : 𝕜) + 1)) = 1 / ((k : 𝕜) + 1) := by simp
      rw [hstar, mul_one_div]
    · simp only [h, ite_false]
      simp
  have hs : HasSum (fun k => if n ≤ k then (y : ℕ → 𝕜) k / ((k : 𝕜) + 1) else 0)
      (inner 𝕜 (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜))) (y)) := by
    rw [hstep2]
    exact (lp.hasSum_inner _ _).congr_fun fun k => (hterm k).symm
  have hs2 : HasSum (fun k => (y : ℕ → 𝕜) (n + k) / (((n + k : ℕ) : 𝕜) + 1))
      (inner 𝕜 (cesaroCLM (𝕜 := 𝕜) (lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜))) (y)) := by
    have hsum0 : (∑ i ∈ Finset.range n,
        (if n ≤ i then (y : ℕ → 𝕜) i / ((i : 𝕜) + 1) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hni : ¬ n ≤ i := by
        have hi' := Finset.mem_range.mp hi
        omega
      simp only [hni, ite_false]
    have h := (hasSum_nat_add_iff
      (f := fun k => if n ≤ k then (y : ℕ → 𝕜) k / ((k : 𝕜) + 1) else 0) (k := n)).mpr
      (by simpa [hsum0] using hs)
    refine HasSum.congr_fun h (fun k => ?_)
    show (y : ℕ → 𝕜) (n + k) / (((n + k : ℕ) : 𝕜) + 1)
        = (if n ≤ k + n then (y : ℕ → 𝕜) (k + n) / (((k + n : ℕ) : 𝕜) + 1) else 0)
    rw [add_comm n k]
    simp only [Nat.le_add_left, ite_true]
  rw [← hsingle, hstep1]
  exact hs2.tsum_eq.symm

/-- The adjoint fixes `e₀`. -/
theorem cesaro_adjoint_single_zero :
    ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := 𝕜)) cesaroE0 = cesaroE0 := by
  ext n
  rw [cesaro_adjoint_apply]
  cases n with
  | zero =>
    rw [show (∑' k, (cesaroE0 (𝕜 := 𝕜) : ℕ → 𝕜) (0 + k) / (((0 + k : ℕ) : 𝕜) + 1)) =
        ∑' k, (cesaroE0 (𝕜 := 𝕜) : ℕ → 𝕜) k / ((k : 𝕜) + 1) from by simp]
    rw [tsum_eq_single 0 (fun k hk => ?_)]
    · simp [cesaroE0_apply]
    · rw [cesaroE0_apply]
      simp [hk]
  | succ n =>
    have hfun : ∀ k : ℕ, (cesaroE0 (𝕜 := 𝕜) : ℕ → 𝕜) (n + 1 + k) /
        (((n + 1 + k : ℕ) : 𝕜) + 1) = 0 := by
      intro k
      rw [cesaroE0_apply]
      simp only [show (n + 1 + k ≠ 0) from by omega, ite_false, zero_div]
    rw [show (∑' k, (cesaroE0 (𝕜 := 𝕜) : ℕ → 𝕜) (n + 1 + k) / (((n + 1 + k : ℕ) : 𝕜) + 1))
        = 0 from by rw [tsum_congr hfun]; exact tsum_zero]
    · simp [cesaroE0_apply]

/-- The second coordinate of `C e₀` is `1 / 2`. -/
theorem cesaroCLM_e0_apply_one : cesaroCLM (𝕜 := 𝕜) cesaroE0 1 = 1 / 2 := by
  rw [cesaroCLM_apply]
  simp [cesaroE0_apply]
  field_simp
  norm_num

/-- The Cesàro operator is not self-adjoint: its adjoint fixes `e₀`, but
`(C e₀) 1 = 1 / 2`. -/
theorem not_isSelfAdjoint_cesaroCLM : ¬ IsSelfAdjoint (cesaroCLM (𝕜 := 𝕜)) := by
  intro h
  have h' : star (cesaroCLM (𝕜 := 𝕜)) = cesaroCLM (𝕜 := 𝕜) := h
  rw [ContinuousLinearMap.star_eq_adjoint] at h'
  have h1 : ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := 𝕜)) cesaroE0 = cesaroE0 := cesaro_adjoint_single_zero
  have h2 : cesaroCLM (𝕜 := 𝕜) cesaroE0 1 = 1 / 2 := cesaroCLM_e0_apply_one
  have h3 : (ContinuousLinearMap.adjoint (cesaroCLM (𝕜 := 𝕜)) cesaroE0) 1 = (cesaroCLM (𝕜 := 𝕜) cesaroE0) 1 := by
    rw [h']
  rw [h1, h2] at h3
  simp [cesaroE0_apply] at h3


/-- The test vectors for non-compactness: `1 / √N` on the first `N`
coordinates. -/
def cesaroTest (N : ℕ) : CesaroSpace 𝕜 :=
  ∑ i ∈ Finset.range N, ((Real.sqrt N : ℝ) : 𝕜)⁻¹ • lp.single (E := fun _ : ℕ => 𝕜) 2 i (1 : 𝕜)

/-- The coordinates of the test vectors. -/
lemma cesaroTest_apply (N : ℕ) (j : ℕ) :
    cesaroTest (𝕜 := 𝕜) N j = if j < N then ((Real.sqrt N : ℝ) : 𝕜)⁻¹ else 0 := by
  simp only [cesaroTest, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.coeFn_single, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hj : j < N
  · simp only [hj, ite_true, mul_one]
  · simp only [hj, ite_false, mul_zero]

/-- The norm of the inverse square root, as a real number. -/
lemma norm_cesaroTest_sqrt (N : ℕ) :
    ‖((Real.sqrt N : ℝ) : 𝕜)⁻¹‖ = (Real.sqrt N)⁻¹ := by
  rw [norm_inv, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Every test vector with `1 ≤ N` is a unit vector. -/
lemma norm_cesaroTest (N : ℕ) (hN : 1 ≤ N) : ‖cesaroTest (𝕜 := 𝕜) N‖ = 1 := by
  rw [lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by simp)]
  have hterm : ∀ j ∈ Finset.range N, ‖cesaroTest (𝕜 := 𝕜) N j‖ ^ (2 : ℝ) = 1 / N := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    rw [cesaroTest_apply]
    simp only [hjN, ite_true]
    rw [norm_cesaroTest_sqrt, Real.rpow_two, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N),
      inv_eq_one_div]
  have hzero : ∀ j ∉ Finset.range N, ‖cesaroTest (𝕜 := 𝕜) N j‖ ^ (2 : ℝ) = 0 := by
    intro j hj
    have hjn : ¬ j < N := by simpa using hj
    rw [cesaroTest_apply]
    simp only [hjn, ite_false, norm_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
  have htsum : ∑' j, ‖cesaroTest (𝕜 := 𝕜) N j‖ ^ (2 : ℝ) = 1 := by
    rw [tsum_eq_sum (s := Finset.range N) hzero]
    calc ∑ j ∈ Finset.range N, ‖cesaroTest (𝕜 := 𝕜) N j‖ ^ (2 : ℝ)
        = ∑ j ∈ Finset.range N, (1 / N : ℝ) :=
          Finset.sum_congr rfl (fun j hj => hterm j hj)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          exact mul_one_div_cancel (by exact_mod_cast (by omega : N ≠ 0))
  have hto : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [hto]
  rw [htsum]
  exact Real.one_rpow _

/-- On the first `N` coordinates, the Cesàro operator applied to the test
vector is constant. -/
lemma cesaroCLM_test_apply_lt {N : ℕ} {n : ℕ} (hn : n < N) :
    cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n = ((Real.sqrt N : ℝ) : 𝕜)⁻¹ := by
  rw [cesaroCLM_apply]
  have hsum : (∑ k ∈ Finset.range (n + 1), cesaroTest (𝕜 := 𝕜) N k)
      = ((n : 𝕜) + 1) * ((Real.sqrt N : ℝ) : 𝕜)⁻¹ := by
    calc ∑ k ∈ Finset.range (n + 1), cesaroTest (𝕜 := 𝕜) N k
        = ∑ k ∈ Finset.range (n + 1), ((Real.sqrt N : ℝ) : 𝕜)⁻¹ := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkN : k < N := lt_of_lt_of_le (Finset.mem_range.mp hk) (by omega : n + 1 ≤ N)
          simp only [cesaroTest_apply, hkN, ite_true]
      _ = ((n : 𝕜) + 1) * ((Real.sqrt N : ℝ) : 𝕜)⁻¹ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  rw [hsum]
  exact mul_div_cancel_left₀ _ (cesaro_den_ne_zero n)

/-- Past coordinate `N`, the Cesàro operator applied to the test vector is
`N / (√N (n + 1))`. -/
lemma cesaroCLM_test_apply_ge {N : ℕ} {n : ℕ} (hn : N ≤ n) :
    cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n
      = (N : 𝕜) * ((Real.sqrt N : ℝ) : 𝕜)⁻¹ / ((n : 𝕜) + 1) := by
  rw [cesaroCLM_apply]
  have hsum : (∑ k ∈ Finset.range (n + 1), cesaroTest (𝕜 := 𝕜) N k)
      = (N : 𝕜) * ((Real.sqrt N : ℝ) : 𝕜)⁻¹ := by
    calc ∑ k ∈ Finset.range (n + 1), cesaroTest (𝕜 := 𝕜) N k
        = ∑ k ∈ Finset.range N, cesaroTest (𝕜 := 𝕜) N k := by
          apply (Finset.sum_subset _ _).symm
          · intro k hk
            simp only [Finset.mem_range] at hk ⊢
            omega
          · intro k _ hk
            have hkn : ¬ k < N := by simpa using hk
            simp only [cesaroTest_apply, hkn, ite_false]
      _ = ∑ k ∈ Finset.range N, ((Real.sqrt N : ℝ) : 𝕜)⁻¹ := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [cesaroTest_apply, Finset.mem_range.mp hk, ite_true]
      _ = (N : 𝕜) * ((Real.sqrt N : ℝ) : 𝕜)⁻¹ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]

/-- For `1 ≤ N`, the squared norm of `C` applied to a test vector is at least
`5 / 4`: the first `N` coordinates contribute `1`, and the next `N` contribute at least
`1 / 4`. -/
lemma five_div_four_le_norm_sq_cesaro_test (N : ℕ) (hN : 1 ≤ N) :
    (5 : ℝ) / 4 ≤ ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N)‖ ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hsum : Summable fun n => ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n‖ ^ (2 : ℝ) := by
    have h := (lp.memℓp (cesaroCLM (𝕜 := 𝕜) (cesaroTest N))).summable
      (p := (2 : ℝ≥0∞)) (by simp)
    simpa using h
  have hle : ∑ n ∈ Finset.range (2 * N),
      ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n‖ ^ (2 : ℝ)
      ≤ ∑' n, ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n‖ ^ (2 : ℝ) :=
    hsum.sum_le_tsum (Finset.range (2 * N)) (fun _ _ => by positivity)
  have hfirst : ∑ n ∈ Finset.range N,
      ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n‖ ^ (2 : ℝ) = 1 := by
    calc ∑ n ∈ Finset.range N, ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n‖ ^ (2 : ℝ)
        = ∑ n ∈ Finset.range N, (1 / N : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [cesaroCLM_test_apply_lt (Finset.mem_range.mp hn), norm_cesaroTest_sqrt,
            Real.rpow_two, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N), inv_eq_one_div]
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          exact mul_one_div_cancel hN'
  have hsecond : (1 : ℝ) / 4 ≤ ∑ n ∈ Finset.range N,
      ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) (N + n)‖ ^ (2 : ℝ) := by
    calc (1 : ℝ) / 4 = ∑ n ∈ Finset.range N, (1 / (4 * N) : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
      _ ≤ ∑ n ∈ Finset.range N, ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) (N + n)‖ ^ (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnN : n < N := Finset.mem_range.mp hn
          rw [cesaroCLM_test_apply_ge (by omega : N ≤ N + n)]
          have hnormeq : ‖(N : 𝕜) * ((Real.sqrt N : ℝ) : 𝕜)⁻¹ / (((N + n : ℕ) : 𝕜) + 1)‖ ^ (2 : ℝ)
              = (N : ℝ) / (((N : ℝ) + n + 1)) ^ 2 := by
            rw [norm_div, norm_mul]
            have h1 : ‖((N : ℕ) : 𝕜)‖ = (N : ℝ) := by simp
            have h2 : ‖(((N + n : ℕ) : 𝕜) + 1)‖ = (N : ℝ) + n + 1 := by
              rw [norm_cesaro_den (N + n)]
              push_cast
              ring
            rw [h1, h2, norm_cesaroTest_sqrt, Real.rpow_two, div_pow, mul_pow, inv_pow,
              Real.sq_sqrt (Nat.cast_nonneg N)]
            field_simp
          rw [hnormeq]
          have hle1 : ((N : ℝ) + n + 1) ≤ 2 * N := by
            have h1 : (n : ℝ) + 1 ≤ (N : ℝ) := by
              exact_mod_cast (Nat.lt_iff_add_one_le.mp hnN)
            linarith
          have hle2 : (((N : ℝ) + n + 1)) ^ 2 ≤ (2 * N) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hle1 2
          have h3 : (N : ℝ) / (2 * N) ^ 2 = 1 / (4 * N) := by
            field_simp
            norm_num
          calc (1 : ℝ) / (4 * N) = (N : ℝ) / (2 * N) ^ 2 := h3.symm
            _ ≤ (N : ℝ) / (((N : ℝ) + n + 1)) ^ 2 :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hle2
  have hfin : (5 : ℝ) / 4 ≤ ∑ n ∈ Finset.range (2 * N),
      ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n‖ ^ (2 : ℝ) := by
    rw [two_mul, Finset.sum_range_add, hfirst]
    linarith [hsecond]
  have hnorm : ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N)‖ ^ (2 : ℝ)
      = ∑' n, ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N) n‖ ^ (2 : ℝ) :=
    lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by simp) _
  have hsq : ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N)‖ ^ 2
      = ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest N)‖ ^ (2 : ℝ) := by
    rw [Real.rpow_two]
  rw [hsq, hnorm]
  exact hfin.trans hle

/-- The coordinates of `C` applied to the test vectors tend to `0`. -/
lemma tendsto_cesaro_test_coord_zero (n : ℕ) :
    Filter.Tendsto (fun N => cesaroCLM (𝕜 := 𝕜) (cesaroTest (N + 1)) n) Filter.atTop
      (𝓝 0) := by
  have hev : ∀ᶠ N in Filter.atTop,
      ((Real.sqrt ((N + 1 : ℕ) : ℝ) : 𝕜))⁻¹ = cesaroCLM (𝕜 := 𝕜) (cesaroTest (N + 1)) n := by
    filter_upwards [Filter.eventually_gt_atTop n] with N hN
    rw [cesaroCLM_test_apply_lt (by omega : n < N + 1)]
  have h2 : Filter.Tendsto (fun N : ℕ => ((Real.sqrt ((N + 1 : ℕ) : ℝ) : 𝕜))⁻¹) Filter.atTop
      (𝓝 0) := by
    have hR : Filter.Tendsto (fun N : ℕ => ((Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ : ℝ))
        Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
    have hC : Filter.Tendsto
        (fun N : ℕ => (((Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ : ℝ) : 𝕜)) Filter.atTop
        (𝓝 ((0 : ℝ) : 𝕜)) :=
      (RCLike.continuous_ofReal.tendsto 0).comp hR
    simpa using hC
  exact h2.congr' hev

/-- The Cesàro operator is not compact: the test vectors `cesaroTest (N + 1)` are
unit vectors. `C` applied to them has squared norm at least `5 / 4`, but converges
coordinatewise to `0`, so no subsequence can converge in norm. -/
theorem not_isCompactOperator_cesaroCLM : ¬ IsCompactOperator (cesaroCLM (𝕜 := 𝕜)) := by
  intro hcomp
  have hball : Bornology.IsBounded (Metric.closedBall (0 : CesaroSpace 𝕜) 1) :=
    Metric.isBounded_closedBall
  obtain ⟨K, hK, hsub⟩ := hcomp.image_subset_compact_of_bounded hball
  have hmem : ∀ N : ℕ, cesaroCLM (𝕜 := 𝕜) (cesaroTest (N + 1)) ∈ K := by
    intro N
    apply hsub
    exact ⟨cesaroTest (N + 1), by
      simp [Metric.mem_closedBall, dist_eq_norm, sub_zero,
        norm_cesaroTest (N + 1) (Nat.succ_pos N)], rfl⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun N => hmem N)
  have hy0 : y = 0 := by
    ext n
    have hcoord : Filter.Tendsto
        (fun N => cesaroCLM (𝕜 := 𝕜) (cesaroTest (φ N + 1)) n) Filter.atTop (𝓝 (y n)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h2 : Filter.Tendsto (fun N => cesaroCLM (𝕜 := 𝕜) (cesaroTest (φ N + 1)) - y)
          Filter.atTop (𝓝 0) := by
        have h := hlim.sub (tendsto_const_nhds (x := y))
        simpa using h
      have h3 : Filter.Tendsto
          (fun N => ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest (φ N + 1)) - y‖) Filter.atTop
          (𝓝 0) := by
        have h := (continuous_norm.tendsto (0 : CesaroSpace 𝕜)).comp h2
        simpa only [Function.comp_def, norm_zero] using h
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun N => by
          have h := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by simp)
            (cesaroCLM (𝕜 := 𝕜) (cesaroTest (φ N + 1)) - y) n
          simpa using h)
    have hzero : Filter.Tendsto
        (fun N => cesaroCLM (𝕜 := 𝕜) (cesaroTest (φ N + 1)) n) Filter.atTop (𝓝 0) :=
      (tendsto_cesaro_test_coord_zero n).comp hφ.tendsto_atTop
    have h : y n = 0 := tendsto_nhds_unique hcoord hzero
    rw [h]
    simp
  have hnorm : (5 : ℝ) / 4 ≤ ‖y‖ ^ 2 := by
    have hlim2 : Filter.Tendsto
        (fun N => ‖cesaroCLM (𝕜 := 𝕜) (cesaroTest (φ N + 1))‖ ^ 2) Filter.atTop
        (𝓝 (‖y‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto y).comp hlim
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim2
      (Filter.Eventually.of_forall fun N => five_div_four_le_norm_sq_cesaro_test (φ N + 1) (Nat.succ_pos _))
  rw [hy0] at hnorm
  norm_num at hnorm

end
end MathlibExt.Analysis.FunctionalAnalysis.CesaroOperator
