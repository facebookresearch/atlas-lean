/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Independence.Integration

/-!
# Quadratic variation of Brownian motion along uniform partitions

For a pre-Brownian motion `B` (Mathlib's `IsPreBrownianReal`) and the uniform partition
`t_k = t k / n` of `[0, t]`, the quadratic sums `∑_{k < n} (B t_{k+1} - B t_k)²` converge to `t`
in `L²` and in probability (`[B]_t = t`). The weighted version, with weights `φ(B t_k)` for a
bounded measurable `φ`, is the form used in the proof of Itô's formula.

## Main definitions

* `ProbabilityTheory.weightedQVError φ B t n`:
  `∑_{k < n} φ(B t_k) ((B t_{k+1} - B t_k)² - t / n)`.

## Main results

* `ProbabilityTheory.integral_weightedQVError_sq_le`: `E[weightedQVError²] ≤ 2 C² t² / n` when
  `|φ| ≤ C`, `B` is adapted to a filtration `F` and its increments are independent of the past.
* `ProbabilityTheory.tendsto_eLpNorm_weightedQVError`: hence `weightedQVError φ B t n → 0` in
  `L²`.
* `ProbabilityTheory.IsPreBrownianReal.indep_natural`: the increments of a pre-Brownian motion
  with measurable coordinates are independent of its natural filtration.
* `ProbabilityTheory.IsPreBrownianReal.tendsto_eLpNorm_sum_sq_sub`,
  `ProbabilityTheory.IsPreBrownianReal.tendstoInMeasure_sum_sq`: **the quadratic variation**
  `∑_{k < n} (B t_{k+1} - B t_k)² → t` in `L²` and in probability, for every pre-Brownian motion.

## Implementation notes

The proof expands the square: cross terms vanish because `(B t_{k+1} - B t_k)² - t / n` has mean
zero and is independent of `F t_k`, and the diagonal terms use the Gaussian fourth moment
`E Z⁴ = 3 v²` for `Z ~ N(0, v)`, so `E[(Z² - v)²] = 2 v²`. Times are in `ℝ≥0`; only uniform
partitions are treated (almost sure convergence along every refining sequence of partitions is
not covered).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Theorem 1.5.8 (quadratic variation of continuous square-integrable martingales) and the
  proof of Theorem 3.3.3.
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Exercise 2.17.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

/-- The weighted quadratic-variation error along the uniform partition of `[0, t]` into `n`
cells: `∑_{k < n} φ(B (t k / n)) ((B (t (k + 1) / n) - B (t k / n))² - t / n)`. -/
noncomputable def weightedQVError {Ω : Type*} (φ : ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, φ (B (t * k / n) ω) *
    ((B (t * (k + 1) / n) ω - B (t * k / n) ω) ^ 2 - ((t : ℝ) / n))

private lemma gaussian_fourth (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  change (∫ x, ((fun x : ℝ ↦ x) ^ 4) x ∂gaussianReal 0 v) = _
  rw [← iteratedDeriv_mgf_zero (by simp), mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  have h1 : deriv (fun t : ℝ ↦ Real.exp (v * t ^ 2 / 2)) =
      fun t ↦ v * t * Real.exp (v * t ^ 2 / 2) := by
    ext t
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
      Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul,
      deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
    ring
  have h2 : deriv (fun t : ℝ ↦ v * t * Real.exp (v * t ^ 2 / 2)) =
      fun t ↦ (v + (v : ℝ) ^ 2 * t ^ 2) * Real.exp (v * t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), h1]
    simp
    ring
  have h3 : deriv (fun t : ℝ ↦ (v + (v : ℝ) ^ 2 * t ^ 2) *
      Real.exp (v * t ^ 2 / 2)) =
      fun t ↦ (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) *
        Real.exp (v * t ^ 2 / 2) := by
    ext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), h1]
    simp
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_one, h1, h2, h3]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), h1]
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  simp [deriv_fun_pow]

private lemma gaussian_centered_stats (v : ℝ≥0) :
    MemLp (fun x : ℝ ↦ x ^ 2 - (v : ℝ)) 2 (gaussianReal 0 v) ∧
    (∫ x : ℝ, (x ^ 2 - (v : ℝ)) ∂gaussianReal 0 v) = 0 ∧
    (∫ x : ℝ, (x ^ 2 - (v : ℝ)) ^ 2 ∂gaussianReal 0 v) =
      2 * (v : ℝ) ^ 2 := by
  have h4 : MemLp (fun x : ℝ ↦ x) 4 (gaussianReal 0 v) :=
    memLp_id_gaussianReal 4
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    change (↑(4 : ℝ≥0) : ℝ≥0∞)⁻¹ + (↑(4 : ℝ≥0) : ℝ≥0∞)⁻¹ =
      (↑(2 : ℝ≥0) : ℝ≥0∞)⁻¹
    rw [← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
    norm_num⟩
  have h2 : MemLp (fun x : ℝ ↦ x ^ 2) 2 (gaussianReal 0 v) := by
    convert (h4.mul h4 : MemLp _ 2 _) using 1
    ext x
    simp [pow_two]
  have hi2 := h2.integrable (by norm_num)
  have hi4 : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 v) := by
    convert h2.integrable_sq using 1
    ext x
    ring
  have hm2 : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
    simpa [variance_eq_integral measurable_id'.aemeasurable] using h
  refine ⟨h2.sub (memLp_const _), ?_, ?_⟩
  · rw [integral_sub hi2 (integrable_const _), hm2]
    simp
  · have he : (fun x : ℝ ↦ (x ^ 2 - (v : ℝ)) ^ 2) =
        fun x ↦ x ^ 4 - (2 * (v : ℝ)) * x ^ 2 + (v : ℝ) ^ 2 := by
      ext x
      ring
    rw [he]
    have his : Integrable (fun x : ℝ ↦ x ^ 4 - 2 * (v : ℝ) * x ^ 2)
        (gaussianReal 0 v) := by
      convert hi4.sub (hi2.const_mul (2 * (v : ℝ))) using 1
    rw [integral_add his
        (integrable_const ((v : ℝ) ^ 2)),
      integral_sub hi4 (hi2.const_mul (2 * (v : ℝ))), integral_const_mul, gaussian_fourth, hm2]
    simp
    ring

private lemma increment_stats
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n k : ℕ) :
    MemLp (fun ω ↦ (B (t * (k + 1) / n) ω - B (t * k / n) ω) ^ 2 -
      ((t : ℝ) / n)) 2 P ∧
    (∫ ω, ((B (t * (k + 1) / n) ω - B (t * k / n) ω) ^ 2 -
      ((t : ℝ) / n)) ∂P) = 0 ∧
    (∫ ω, ((B (t * (k + 1) / n) ω - B (t * k / n) ω) ^ 2 -
      ((t : ℝ) / n)) ^ 2 ∂P) = 2 * ((t : ℝ) / n) ^ 2 := by
  have hv : nndist (t * (k + 1) / n : ℝ≥0).1 (t * k / n : ℝ≥0).1 = t / n := by
    apply NNReal.coe_injective
    change (nndist ((t * (k + 1) / n : ℝ≥0) : ℝ)
      ((t * k / n : ℝ≥0) : ℝ) : ℝ) = ((t / n : ℝ≥0) : ℝ)
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_add, NNReal.coe_one, coe_nndist, Real.dist_eq]
    rw [show (t : ℝ) * ((k : ℝ) + 1) / n - (t : ℝ) * k / n =
      (t : ℝ) / n by ring, abs_of_nonneg (by positivity)]
  have hl := hB.hasLaw_sub (t * (k + 1) / n) (t * k / n)
  rw [hv] at hl
  have hs := gaussian_centered_stats (t / n)
  refine ⟨?_, ?_, ?_⟩
  · convert hl.memLp_comp hs.1 using 1
    ext ω
    simp
  · convert (hl.integral_comp (f := fun x : ℝ ↦ x ^ 2 - ((t : ℝ) / n))
      (by fun_prop)).trans hs.2.1 using 1
    simp only [Function.comp_def, Pi.sub_apply]
  · convert (hl.integral_comp (f := fun x : ℝ ↦ (x ^ 2 - ((t : ℝ) / n)) ^ 2)
      (by fun_prop)).trans hs.2.2 using 1 <;>
      simp only [Function.comp_def, Pi.sub_apply, NNReal.coe_div, NNReal.coe_natCast]

private lemma indep_past
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (s t : ℝ≥0) (hst : s ≤ t) {f : Ω → ℝ} (hf : Measurable[F s] f)
    (g : ℝ → ℝ) (hg : Measurable g) :
    IndepFun f (fun ω ↦ g (B t ω - B s ω)) P := by
  apply (IndepFun_iff_Indep _ _ _).2
  exact indep_of_indep_of_le (hInd s t hst).symm hf.comap_le
    (hg.comp (comap_measurable _)).comap_le

private lemma weighted_cell_memLp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, |φ x| ≤ C)
    (t : ℝ≥0) (n k : ℕ) :
    MemLp (fun ω ↦ φ (B (t * k / n) ω) *
      ((B (t * (k + 1) / n) ω - B (t * k / n) ω) ^ 2 - ((t : ℝ) / n))) 2 P := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφC 0)
  have hm (u : ℝ≥0) : Measurable (B u) := (hBF u).mono (F.le u) le_rfl
  refine ((increment_stats hB t n k).1.const_mul C).of_le (by fun_prop) ?_
  filter_upwards [] with ω
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hφC _) (abs_nonneg _)

private lemma orthogonal_sum_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (hf : ∀ k, MemLp (f k) 2 P) (A : ℝ)
    (hd : ∀ k, ∫ ω, f k ω ^ 2 ∂P ≤ A)
    (hc : ∀ j k, j < k → ∫ ω, f j ω * f k ω ∂P = 0) (m : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range m, f k ω) ^ 2 ∂P ≤ m * A := by
  have hS (m : ℕ) : MemLp (fun ω ↦ ∑ k ∈ Finset.range m, f k ω) 2 P :=
    memLp_finsetSum _ (fun k _ ↦ hf k)
  induction m with
  | zero => simp
  | succ m ih =>
    have hcross : (∫ ω, (∑ k ∈ Finset.range m, f k ω) * f m ω ∂P) = 0 := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun k _ ↦ ?_)]
      · apply Finset.sum_eq_zero
        intro k hk
        exact hc k m (Finset.mem_range.1 hk)
      · convert (hf k).integrable_mul (hf m) using 1
    have hexp : (fun ω ↦ (∑ k ∈ Finset.range (m + 1), f k ω) ^ 2) =
        fun ω ↦ (∑ k ∈ Finset.range m, f k ω) ^ 2 + f m ω ^ 2 +
          2 * ((∑ k ∈ Finset.range m, f k ω) * f m ω) := by
      ext ω
      rw [Finset.sum_range_succ]
      ring
    have hi : Integrable (fun ω ↦ (∑ k ∈ Finset.range m, f k ω) * f m ω) P := by
      convert (hS m).integrable_mul (hf m) using 1
    have his : Integrable (fun ω ↦ (∑ k ∈ Finset.range m, f k ω) ^ 2 +
        f m ω ^ 2) P := by
      convert (hS m).integrable_sq.add (hf m).integrable_sq using 1
    rw [hexp, integral_add his
      (hi.const_mul 2), integral_add (hS m).integrable_sq (hf m).integrable_sq,
      integral_const_mul, hcross]
    simp only [mul_zero, add_zero, Nat.cast_add, Nat.cast_one]
    nlinarith [hd m]

private lemma weighted_error_memLp
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, |φ x| ≤ C)
    (t : ℝ≥0) (n : ℕ) : MemLp (weightedQVError φ B t n) 2 P := by
  exact memLp_finsetSum _ (fun k _ ↦ weighted_cell_memLp hB hBF hφ hφC t n k)

/-- **Second moment of the weighted quadratic-variation error.** For a pre-Brownian motion `B`
adapted to `F` with increments independent of the past, and a measurable weight `φ` bounded by
`C`, `E[(∑_{k < n} φ(B_{t_k}) ((ΔB_k)² - Δt))²] ≤ 2 C² t² / n` on the uniform partition
`t_k = t k / n` (`n ≥ 1`). -/
theorem integral_weightedQVError_sq_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) (t : ℝ≥0) {n : ℕ}
    (hn : 0 < n) :
    ∫ ω, weightedQVError φ B t n ω ^ 2 ∂P ≤ 2 * C ^ 2 * (t : ℝ) ^ 2 / n := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let u (k : ℕ) : ℝ≥0 := t * k / n
  let D (k : ℕ) (ω : Ω) : ℝ := (B (u (k + 1)) ω - B (u k) ω) ^ 2 - (t : ℝ) / n
  let a (k : ℕ) (ω : Ω) : ℝ := φ (B (u k) ω)
  let f (k : ℕ) (ω : Ω) : ℝ := a k ω * D k ω
  have hu {j k : ℕ} (hjk : j ≤ k) : u j ≤ u k := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) t.coe_nonneg) (by positivity)
  have hm (k : ℕ) : Measurable (B (u k)) := (hBF _).mono (F.le _) le_rfl
  have hD (k : ℕ) : Measurable (D k) := by
    dsimp [D]
    fun_prop
  have hf (k : ℕ) : MemLp (f k) 2 P := by
    simpa only [f, a, D, u, Nat.cast_add, Nat.cast_one] using
      weighted_cell_memLp hB hBF hφ hφC t n k
  have hd (k : ℕ) : ∫ ω, f k ω ^ 2 ∂P ≤ C ^ 2 * (2 * ((t : ℝ) / n) ^ 2) := by
    have hstats : MemLp (D k) 2 P ∧ (∫ ω, D k ω ∂P) = 0 ∧
        (∫ ω, D k ω ^ 2 ∂P) = 2 * ((t : ℝ) / n) ^ 2 := by
      simpa only [D, u, Nat.cast_add, Nat.cast_one] using increment_stats hB t n k
    have hiD := hstats.1.integrable_sq
    calc
      _ ≤ ∫ ω, C ^ 2 * D k ω ^ 2 ∂P := by
        apply integral_mono (hf k).integrable_sq (hiD.const_mul (C ^ 2))
        intro ω
        dsimp [f]
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact sq_le_sq.2 ((hφC _).trans (le_abs_self C))
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact hstats.2.2
  have hc (j k : ℕ) (hjk : j < k) : ∫ ω, f j ω * f k ω ∂P = 0 := by
    have hp : Measurable[F (u k)] (fun ω ↦ f j ω * a k ω) := by
      have hj : Measurable[F (u k)] (B (u j)) :=
        (hBF _).mono (F.mono (hu hjk.le)) le_rfl
      have hj1 : Measurable[F (u k)] (B (u (j + 1))) :=
        (hBF _).mono (F.mono (hu hjk)) le_rfl
      have hk : Measurable[F (u k)] (B (u k)) := hBF _
      dsimp [f, a, D]
      fun_prop
    have hind := indep_past hInd (u k) (u (k + 1)) (hu (Nat.le_succ k)) hp
      (fun x : ℝ ↦ x ^ 2 - (t : ℝ) / n) (by fun_prop)
    calc
      _ = ∫ ω, (f j ω * a k ω) * D k ω ∂P := by
        congr 1
        ext ω
        dsimp [f]
        ring
      _ = (∫ ω, f j ω * a k ω ∂P) * ∫ ω, D k ω ∂P :=
        hind.integral_fun_mul_eq_mul_integral
          ((hp.mono (F.le _) le_rfl).aestronglyMeasurable) (hD k).aestronglyMeasurable
      _ = 0 := by
        have hz : (∫ ω, D k ω ∂P) = 0 := by
          simpa only [D, u, Nat.cast_add, Nat.cast_one] using
            (increment_stats hB t n k).2.1
        rw [hz, mul_zero]
  have hb := orthogonal_sum_bound f hf _ hd hc n
  simp only [f, a, D, u, Nat.cast_add, Nat.cast_one] at hb
  change (∫ ω, weightedQVError φ B t n ω ^ 2 ∂P) ≤ _ at hb
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  convert hb using 1
  field_simp

/-- **Weighted quadratic variation of Brownian motion.** Under the hypotheses of
`integral_weightedQVError_sq_le`, `∑_{k < n} φ(B_{t_k}) ((ΔB_k)² - Δt) → 0` in `L²(P)`. -/
theorem tendsto_eLpNorm_weightedQVError
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) (t : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm (weightedQVError φ B t n) 2 P) atTop (𝓝 0) := by
  have he (n : ℕ) : eLpNorm (weightedQVError φ B t n) 2 P =
      ENNReal.ofReal (Real.sqrt (∫ ω, weightedQVError φ B t n ω ^ 2 ∂P)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (weighted_error_memLp hB hBF hφ hφC t n)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      Real.sqrt_eq_rpow, one_div]
  have hlim : Tendsto (fun n : ℕ ↦ Real.sqrt (2 * C ^ 2 * (t : ℝ) ^ 2 / n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_div_atTop_nhds_zero_nat (2 * C ^ 2 * (t : ℝ) ^ 2))
  have hlim' := ENNReal.tendsto_ofReal hlim
  simp only [ENNReal.ofReal_zero] at hlim'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall (fun _ ↦ bot_le))
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  exact Real.sqrt_le_sqrt (integral_weightedQVError_sq_le hB hBF hInd hφ hφC t hn)

/-! ### The natural filtration and the classical quadratic variation -/

/-- **Increments are independent of the past.** For a pre-Brownian motion with measurable
coordinates, each increment `B t - B s` (`s ≤ t`) is independent of the natural filtration at
time `s` (a consequence of `IsPreBrownianReal.indepFun_shift`, the weak Markov property). -/
theorem IsPreBrownianReal.indep_natural {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (s t : ℝ≥0)
    (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable) s) P := by
  have h := hB.indepFun_shift s
  rw [IndepFun_iff_Indep] at h
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · have heq : (fun ω ↦ B t ω - B s ω) =
        (fun x : ℝ≥0 → ℝ ↦ x (t - s)) ∘ (fun ω u ↦ B (s + u) ω - B s ω) := by
      funext ω
      simp [add_tsub_cancel_of_le hst]
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply (t - s)).comap_le
  · refine iSup₂_le fun j hj ↦ ?_
    have heq : B j = (fun x : Set.Iic s → ℝ ↦ x ⟨j, hj⟩) ∘ (fun ω (u : Set.Iic s) ↦ B u ω) := rfl
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- A process with measurable coordinates is adapted to its natural filtration. -/
theorem adapted_natural_of_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t)) :
    Adapted (Filtration.natural B (fun t ↦ (hBm t).stronglyMeasurable)) B := fun i ↦
  Measurable.of_comap_le (le_iSup₂_of_le (f := fun j (_ : j ≤ i) ↦
    MeasurableSpace.comap (B j) inferInstance) i le_rfl le_rfl)

/-- **Quadratic variation of Brownian motion**, `[B]_t = t`: along the uniform partitions of
`[0, t]`, `∑_{k < n} (B (t (k + 1) / n) - B (t k / n))² → t` in `L²(P)`, for every pre-Brownian
motion `B` (no filtration and no measurability of the coordinates is assumed; Øksendal 2003,
Exercise 2.17; Karatzas–Shreve 1991, Theorem 1.5.8 treats continuous square-integrable
martingales in probability). -/
theorem IsPreBrownianReal.tendsto_eLpNorm_sum_sq_sub {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ eLpNorm (fun ω ↦ ∑ k ∈ Finset.range n,
      (B (t * (k + 1) / n) ω - B (t * k / n) ω) ^ 2 - t) 2 P) atTop (𝓝 0) := by
  -- a measurable modification and its natural filtration
  set B' : ℝ≥0 → Ω → ℝ := fun t ↦ (hB.aemeasurable t).mk (B t)
  have hB'm : ∀ t, Measurable (B' t) := fun t ↦ (hB.aemeasurable t).measurable_mk
  have hBB' : ∀ t, B t =ᵐ[P] B' t := fun t ↦ (hB.aemeasurable t).ae_eq_mk
  have hB' : IsPreBrownianReal B' P := hB.congr hBB'
  have h := tendsto_eLpNorm_weightedQVError hB' (adapted_natural_of_measurable hB'm)
    (hB'.indep_natural hB'm) (φ := fun _ ↦ 1) measurable_const (C := 1)
    (fun _ ↦ (abs_one).le) t
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine eLpNorm_congr_ae ?_
  have hae : ∀ᵐ ω ∂P, ∀ k : ℕ, B (t * k / n) ω = B' (t * k / n) ω ∧
      B (t * (k + 1) / n) ω = B' (t * (k + 1) / n) ω :=
    ae_all_iff.2 fun k ↦ (hBB' _).and (hBB' _)
  filter_upwards [hae] with ω hω
  simp only [weightedQVError, one_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, (hω _).1, (hω _).2]
  rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne')]

/-- **Quadratic variation of Brownian motion in probability**: along the uniform partitions of
`[0, t]`, `∑_{k < n} (B (t (k + 1) / n) - B (t k / n))² → t` in probability. -/
theorem IsPreBrownianReal.tendstoInMeasure_sum_sq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ ∑ k ∈ Finset.range n,
      (B (t * (k + 1) / n) ω - B (t * k / n) ω) ^ 2) atTop (fun _ ↦ (t : ℝ)) :=
  tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hB.tendsto_eLpNorm_sum_sq_sub t)

end ProbabilityTheory
