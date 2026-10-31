/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegral
public import MathlibExt.Probability.BrownianQuadraticVariation
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Union
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Itô's formula for Brownian motion

For a Brownian motion `B` adapted to a filtration `F` with increments independent of the past,
jointly measurable in `(t, ω)`, and `f` of class `C²` with bounded `f'` and `f''`,
`f (B t) = f (B 0) + ∫_0^t f'(B u) dB u + (1/2) ∫_0^t f''(B u) du` almost surely, with the Itô
integral `ProbabilityTheory.itoIntegral` of `MathlibExt.Probability.ItoIntegral`.

## Main definitions

* `ProbabilityTheory.leftPointProcess g B t n`: the left-point step process
  `∑_{k < n} g(B (t k / n)) 1_{(t k / n, t (k + 1) / n]}`.
* `ProbabilityTheory.ElementaryIntegrand.leftPoint`: the same process as an elementary integrand,
  for a bounded measurable `g` and an adapted `B`.

## Main results

* `ProbabilityTheory.tendsto_taylor_sum_sub`: along a continuous path `w` and uniform partitions
  on which the quadratic sums stay bounded, `f (w t) - f (w 0)` minus the second-order Taylor
  sums `∑_k (f'(w_k) Δw_k + (1/2) f''(w_k) Δw_k²)` tends to `0`.
* `ProbabilityTheory.tendsto_sum_riemann_uniform`: left-point Riemann sums of a continuous function
  on uniform partitions converge to its integral.
* `ProbabilityTheory.tendsto_lintegral_leftPointProcess_sub_sq`: for a Lipschitz `g`, the
  left-point step processes converge to `u ↦ g (B u)` in `L²(P ⊗ du)` on `(0, t] × Ω`.
* `ProbabilityTheory.ito_formula`: **Itô's formula**.

## Implementation notes

The proof follows Karatzas–Shreve: along the uniform partitions of `[0, t]`, the left-point Itô
sums of `f'(B)` converge in `L²` to the Itô integral (the integrand is Itô-approximable by the
left-point step processes because `f'` is Lipschitz), the weighted quadratic-variation errors
`∑_k f''(B t_k) ((ΔB_k)² - t / n)` and `∑_k ((ΔB_k)² - t / n)` converge to `0` in `L²`
(`MathlibExt.Probability.BrownianQuadraticVariation`), and along a common subsequence all three
converge almost surely; on a continuous path the second-order Taylor expansion and the Riemann
sums for `∫_0^t f''(B u) du` then give the formula.

Joint measurability of `(t, ω) ↦ B t ω` is a hypothesis: the Itô integral of `u ↦ f'(B u)` is
defined only for jointly measurable integrands (`ProbabilityTheory.IsItoApproximable`), and
without it the statement can fail (on a null set of discontinuous paths, the paths may be
non-measurable in `t`, and the Itô integral is then the junk value `0`). It holds, for instance,
when every path is continuous. The boundedness of `f'` and `f''` is the setting of the statement
in the references; unbounded derivatives (and localization) are not covered.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Theorem 3.3.3 (Itô's rule) and its proof, and Lemma 3.2.4.
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Theorem 4.1.2 and
  its proof.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

/-! ### Pathwise Taylor sums and Riemann sums -/

private lemma partition_mem {t : ℝ} (ht : 0 ≤ t) {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ n) : t * k / n ∈ Set.Icc (0 : ℝ) t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  constructor
  · positivity
  · exact (div_le_iff₀ hn').2 (mul_le_mul_of_nonneg_left hk' ht)

private lemma partition_step {t : ℝ} {n k : ℕ} :
    t * (k + 1) / n - t * k / n = t / n := by ring

private lemma compact_modulus {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| < δ → |g x - g y| < ε := by
  simpa only [Real.dist_eq] using
    Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) ε hε

private lemma taylor_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {x y : ℝ}
    (hxy : x ≠ y) : ∃ z ∈ Set.uIcc x y,
      f y - f x - deriv f x * (y - x) =
        (1 / 2) * deriv (deriv f) z * (y - x) ^ 2 := by
  obtain ⟨z, hz, he⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  have hd : derivWithin f (Set.uIcc x y) x = deriv f x :=
    (hf.differentiable (by norm_num)).differentiableAt.derivWithin
      ((uniqueDiffOn_uIcc hxy) x (Set.left_mem_uIcc))
  refine ⟨z, Set.uIoo_subset_uIcc_self hz, ?_⟩
  simp [taylorWithinEval_succ, iteratedDerivWithin_one, hd,
    iteratedDeriv_succ] at he
  nlinarith [he]

private lemma eventually_partition_close {g : ℝ → ℝ} (hg : Continuous g)
    {t : ℝ} (ht : 0 ≤ t) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ j in atTop, 0 < ns j ∧ ∀ k < ns j,
      |g (t * (k + 1) / ns j) - g (t * k / ns j)| < ε := by
  obtain ⟨δ, hδ, hmod⟩ := compact_modulus hg hε (a := 0) (b := t)
  have hmesh := (tendsto_const_div_atTop_nhds_zero_nat t).comp hns
  filter_upwards [hns.eventually (eventually_gt_atTop 0),
    hmesh.eventually (gt_mem_nhds hδ)] with j hn hj
  refine ⟨hn, fun k hk => ?_⟩
  have hnext : t * ((k : ℝ) + 1) / ns j ∈ Set.Icc (0 : ℝ) t := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      partition_mem ht hn (Nat.succ_le_of_lt hk)
  apply hmod _ hnext _ (partition_mem ht hn hk.le)
  rw [partition_step, abs_of_nonneg (by positivity)]
  exact hj

private lemma taylor_error_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {x y η : ℝ} (hη : 0 ≤ η)
    (hD : ∀ z ∈ Set.uIcc x y, |deriv (deriv f) z - deriv (deriv f) x| ≤ η) :
    |f y - f x - (deriv f x * (y - x) +
      (1 / 2) * deriv (deriv f) x * (y - x) ^ 2)| ≤ η * (y - x) ^ 2 := by
  by_cases hxy : x = y
  · subst y
    simp
  obtain ⟨z, hz, he⟩ := taylor_two hf hxy
  have hr : f y - f x - (deriv f x * (y - x) +
      (1 / 2) * deriv (deriv f) x * (y - x) ^ 2) =
      (1 / 2) * (deriv (deriv f) z - deriv (deriv f) x) * (y - x) ^ 2 := by
    nlinarith [he]
  rw [hr, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_nonneg (sq_nonneg (y - x))]
  have := mul_le_mul_of_nonneg_right (hD z hz) (sq_nonneg (y - x))
  nlinarith [mul_nonneg hη (sq_nonneg (y - x))]


/-- **Second-order Taylor sums along a continuous path.** For `f` of class `C²`, a continuous
path `w`, `t ≥ 0`, and a sequence of mesh counts `ns j → ∞` along which the quadratic sums
`∑_{k < ns j} (w (t (k + 1) / ns j) - w (t k / ns j))²` stay bounded, the telescoped increment
`f (w t) - f (w 0)` minus the second-order Taylor sums
`∑_k (f'(w_k) Δw_k + (1/2) f''(w_k) Δw_k²)` tends to `0`. -/
theorem tendsto_taylor_sum_sub {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {w : ℝ → ℝ}
    (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {M : ℝ}
    (hM : ∀ j, ∑ k ∈ Finset.range (ns j),
      (w (t * (k + 1) / ns j) - w (t * k / ns j)) ^ 2 ≤ M) :
    Tendsto (fun j ↦ f (w t) - f (w 0) - ∑ k ∈ Finset.range (ns j),
      (deriv f (w (t * k / ns j)) * (w (t * (k + 1) / ns j) - w (t * k / ns j)) +
        (1 / 2) * deriv (deriv f) (w (t * k / ns j)) *
          (w (t * (k + 1) / ns j) - w (t * k / ns j)) ^ 2)) atTop (𝓝 0) := by
  classical
  have hM0 : 0 ≤ M := (Finset.sum_nonneg (s := Finset.range (ns 0)) fun k _ => sq_nonneg
    (w (t * (k + 1) / ns 0) - w (t * k / ns 0))).trans (hM 0)
  have hD : Continuous (deriv (deriv f)) :=
    (hf.deriv' (n := 1)).continuous_deriv_one
  obtain ⟨R, hR⟩ := (isCompact_Icc.image hw).isBounded.subset_closedBall (0 : ℝ)
  have hW : ∀ s ∈ Set.Icc (0 : ℝ) t, w s ∈ Set.Icc (-R) R := by
    intro s hs
    have hb := hR (Set.mem_image_of_mem w hs)
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le, Set.mem_Icc] using hb
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (M + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := compact_modulus hD hη (a := -R) (b := R)
  filter_upwards [eventually_partition_close hw ht hns hδ] with j hj
  obtain ⟨hn, hclose⟩ := hj
  have hn0 : (ns j : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let a : ℕ → ℝ := fun k => w (t * k / ns j)
  let q : ℕ → ℝ := fun k => deriv f (a k) * (a (k + 1) - a k) +
    (1 / 2) * deriv (deriv f) (a k) * (a (k + 1) - a k) ^ 2
  have hcell : ∀ k ∈ Finset.range (ns j),
      |f (a (k + 1)) - f (a k) - q k| ≤ η * (a (k + 1) - a k) ^ 2 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    apply taylor_error_bound hf hη.le
    intro z hz
    have hzk : |z - a k| < δ :=
      (Set.abs_sub_left_of_mem_uIcc hz).trans_lt (by
        simpa only [a, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hclose k hk')
    have hx : a k ∈ Set.Icc (-R) R := hW _ (partition_mem ht hn hk'.le)
    have hy : a (k + 1) ∈ Set.Icc (-R) R :=
      hW _ (partition_mem ht hn (Nat.succ_le_of_lt hk'))
    exact (hmod z (Set.uIcc_subset_Icc hx hy hz) (a k) hx hzk).le
  have htel : (∑ k ∈ Finset.range (ns j), (f (a (k + 1)) - f (a k))) =
      f (w t) - f (w 0) := by
    rw [Finset.sum_range_sub (fun k => f (a k))]
    simp [a, mul_div_cancel_right₀ t hn0]
  have hsum : |f (w t) - f (w 0) - ∑ k ∈ Finset.range (ns j), q k| ≤ η * M := by
    rw [← htel, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ Finset.range (ns j),
          |f (a (k + 1)) - f (a k) - q k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (ns j), η * (a (k + 1) - a k) ^ 2 :=
        Finset.sum_le_sum hcell
      _ = η * ∑ k ∈ Finset.range (ns j), (a (k + 1) - a k) ^ 2 :=
        (Finset.mul_sum ..).symm
      _ ≤ η * M := mul_le_mul_of_nonneg_left (by
        simpa only [a, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hM j) hη.le
  have hηε : η * M < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by linarith : 0 < M + 1)).2 (by nlinarith)
  simpa only [Real.dist_eq, sub_zero, q, a, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    hsum.trans_lt hηε

/-- **Left-point Riemann sums of a continuous function** on the uniform partition of `[0, t]`
converge to the integral: `∑_{k < n} g (t k / n) (t / n) → ∫_0^t g` (`t ≥ 0`). -/
theorem tendsto_sum_riemann_uniform {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, g (t * k / n) * (t / n)) atTop
      (𝓝 (∫ u in (0 : ℝ)..t, g u)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (t + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := compact_modulus hg hη (a := 0) (b := t)
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_const_div_atTop_nhds_zero_nat t).eventually (gt_mem_nhds hδ)] with n hn hmesh
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let a : ℕ → ℝ := fun k => t * k / n
  have hlen : ∀ k, a (k + 1) - a k = t / n := by
    intro k
    dsimp [a]
    push_cast
    ring
  have hcell : ∀ k ∈ Finset.range n,
      |g (a k) * (t / n) - ∫ u in a k..a (k + 1), g u| ≤ η * (t / n) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have ha : a k ∈ Set.Icc (0 : ℝ) t := partition_mem ht hn hk'.le
    have hb : a (k + 1) ∈ Set.Icc (0 : ℝ) t :=
      partition_mem ht hn (Nat.succ_le_of_lt hk')
    have heq : (∫ u in a k..a (k + 1), g u - g (a k)) =
        (∫ u in a k..a (k + 1), g u) - g (a k) * (t / n) := by
      rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const, hlen]
      simp [smul_eq_mul, mul_comm]
    rw [abs_sub_comm, ← heq, ← Real.norm_eq_abs]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a k) (b := a (k + 1)) (C := η) (f := fun u => g u - g (a k)) ?_
    · simpa only [hlen, abs_of_nonneg (by positivity : 0 ≤ t / (n : ℝ))] using hbound
    intro u hu
    have hu' := Set.uIoc_subset_uIcc hu
    have humem := Set.uIcc_subset_Icc ha hb hu'
    have hudist : |u - a k| < δ := by
      refine (Set.abs_sub_left_of_mem_uIcc hu').trans_lt ?_
      rw [hlen, abs_of_nonneg (by positivity)]
      exact hmesh
    simpa only [Real.norm_eq_abs] using (hmod u humem (a k) ha hudist).le
  have hint : (∑ k ∈ Finset.range n, ∫ u in a k..a (k + 1), g u) =
      ∫ u in (0 : ℝ)..t, g u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hg.intervalIntegrable (a k) (a (k + 1)))]
    simp [a, hn0]
  have hsum : |(∑ k ∈ Finset.range n, g (a k) * (t / n)) -
      ∫ u in (0 : ℝ)..t, g u| ≤ η * t := by
    rw [← hint, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ Finset.range n,
          |g (a k) * (t / n) - ∫ u in a k..a (k + 1), g u| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, η * (t / n) := Finset.sum_le_sum hcell
      _ = η * t := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
  have hηε : η * t < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by linarith : 0 < t + 1)).2 (by nlinarith)
  simpa only [Real.dist_eq, a] using hsum.trans_lt hηε

/-! ### Left-point approximation of `g ∘ B` -/

/-- The left-point step process `∑_{k < n} g(B (t k / n)) 1_{(t k / n, t (k + 1) / n]}` of
`u ↦ g (B u)` on the uniform partition of `[0, t]` into `n` cells. -/
noncomputable def leftPointProcess {Ω : Type*} (g : ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (n : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin n, (Set.Ioc (t * (i : ℕ) / n) (t * ((i : ℕ) + 1) / n)).indicator
    (fun _ ↦ g (B (t * (i : ℕ) / n) ω)) u

private lemma partition_mono (t : ℝ≥0) (n : ℕ) :
    Monotone (fun k : ℕ ↦ t * k / n) := by
  intro i j hij
  dsimp
  gcongr

private lemma partition_cell (t u : ℝ≥0) {n : ℕ} (hn : n ≠ 0)
    (hu : u ∈ Set.Ioc 0 t) :
    ∃ i : Fin n, u ∈ Set.Ioc (t * (i : ℕ) / n) (t * ((i : ℕ) + 1) / n) := by
  have hu' : u ∈ Set.Ioc (t * (0 : ℕ) / n) (t * n / n) := by
    simpa [hn] using hu
  have h := Ioc_subset_biUnion_Ioc n (fun k : ℕ ↦ t * k / n) hu'
  simp only [Set.mem_iUnion, Finset.mem_range] at h
  obtain ⟨k, hk, hku⟩ := h
  exact ⟨⟨k, hk⟩, by simpa using hku⟩

private lemma leftPointProcess_on_cell {Ω : Type*} (g : ℝ → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t u : ℝ≥0) {n : ℕ} (i : Fin n)
    (hu : u ∈ Set.Ioc (t * (i : ℕ) / n) (t * ((i : ℕ) + 1) / n)) (ω : Ω) :
    leftPointProcess g B t n u ω = g (B (t * (i : ℕ) / n) ω) := by
  classical
  unfold leftPointProcess
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hu _
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    have hne : (j : ℕ) ≠ (i : ℕ) := fun h ↦ hji (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : t * ((j : ℕ) + 1) / n ≤ t * (i : ℕ) / n := by
        simpa using partition_mono t n (Nat.succ_le_of_lt hlt)
      exact (not_lt_of_ge (hj.2.trans hle)) hu.1
    · have hle : t * ((i : ℕ) + 1) / n ≤ t * (j : ℕ) / n := by
        simpa using partition_mono t n (Nat.succ_le_of_lt hgt)
      exact (not_lt_of_ge (hu.2.trans hle)) hj.1
  · simp

private lemma increment_moment {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s u : ℝ≥0) (hsu : s ≤ u) :
    (∫⁻ ω, ‖B s ω - B u ω‖ₑ ^ 2 ∂P) = (u - s : ℝ≥0) := by
  have h := hB.hasLaw_sub s u
  have : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hm : P[B s - B u] = 0 := by
    rw [h.integral_eq, integral_id_gaussianReal]
  have hv := (ofReal_variance h.hasGaussianLaw.memLp_two).symm
  rw [h.variance_eq, variance_id_gaussianReal] at hv
  have hm' : (∫ ω, B s ω - B u ω ∂P) = 0 := hm
  simp only [evariance, Pi.sub_apply, hm', sub_zero] at hv
  have hd : nndist (s : ℝ) (u : ℝ) = u - s := by
    apply NNReal.eq
    simp [NNReal.coe_sub hsu, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hsu))]
  simpa [hd] using hv

private lemma leftPointProcess_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} (hBm : Measurable fun p : ℝ≥0 × Ω ↦ B p.1 p.2)
    {g : ℝ → ℝ} (hgm : Measurable g) (t : ℝ≥0) (n : ℕ) :
    Measurable (fun p : Ω × ℝ ↦ leftPointProcess g B t n p.2.toNNReal p.1) := by
  classical
  apply Finset.measurable_sum
  intro i _
  let s := Set.Ioc (t * (i : ℕ) / n) (t * ((i : ℕ) + 1) / n)
  have hs : MeasurableSet ((fun p : Ω × ℝ ↦ p.2.toNNReal) ⁻¹' s) :=
    measurableSet_Ioc.preimage (measurable_real_toNNReal.comp measurable_snd)
  have hf : Measurable (fun p : Ω × ℝ ↦ g (B (t * (i : ℕ) / n) p.1)) :=
    hgm.comp (hBm.comp (measurable_const.prodMk measurable_fst))
  convert hf.indicator hs using 1
  ext p
  by_cases hp : p.2.toNNReal ∈ s <;> simp [s, Set.indicator, hp]

private lemma lipschitz_error {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * |x - y|) (x y : ℝ) :
    ‖g x - g y‖ₑ ^ 2 ≤ ENNReal.ofReal L ^ 2 * ‖x - y‖ₑ ^ 2 := by
  have he : ‖g x - g y‖ₑ ≤ ENNReal.ofReal L * ‖x - y‖ₑ := by
    simpa only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hL] using
      ENNReal.ofReal_le_ofReal (hg x y)
  simpa only [mul_pow] using pow_le_pow_left' he 2

private lemma error_moment_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * |x - y|) (t u : ℝ≥0)
    {n : ℕ} (hn : n ≠ 0) (hu : u ∈ Set.Ioc 0 t) :
    (∫⁻ ω, ‖leftPointProcess g B t n u ω - g (B u ω)‖ₑ ^ 2 ∂P) ≤
      ENNReal.ofReal L ^ 2 * (t / n : ℝ≥0) := by
  obtain ⟨i, hi⟩ := partition_cell t u hn hu
  simp_rw [leftPointProcess_on_cell g B t u i hi]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal L ^ 2 * ‖B (t * (i : ℕ) / n) ω - B u ω‖ₑ ^ 2 ∂P :=
      lintegral_mono (fun ω ↦ lipschitz_error hL hg _ _)
    _ = ENNReal.ofReal L ^ 2 * (u - t * (i : ℕ) / n : ℝ≥0) := by
      rw [lintegral_const_mul' _ _ (by finiteness), increment_moment hB _ _ hi.1.le]
    _ ≤ ENNReal.ofReal L ^ 2 * (t / n : ℝ≥0) := by
      gcongr
      apply tsub_le_iff_right.mpr
      calc
        u ≤ t * ((i : ℕ) + 1) / n := hi.2
        _ = t / n + t * (i : ℕ) / n := by ring

/-- **Left-point approximation of a Lipschitz function of Brownian motion.** For a pre-Brownian
motion `B` that is jointly measurable in `(u, ω)` and an `L`-Lipschitz `g`, the left-point step
processes of `u ↦ g (B u)` converge to it in `L²(P ⊗ du)` on `(0, t] × Ω`:
`E ∫_0^t |leftPointProcess g B t n u - g (B u)|² du → 0`. -/
theorem tendsto_lintegral_leftPointProcess_sub_sq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBm : Measurable fun p : ℝ≥0 × Ω ↦ B p.1 p.2)
    {g : ℝ → ℝ} {L : ℝ} (hg : ∀ x y, |g x - g y| ≤ L * |x - y|) (t : ℝ≥0) :
    Tendsto (fun n ↦ ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖leftPointProcess g B t n u.toNNReal ω - g (B u.toNNReal ω)‖ₑ ^ 2) ∂P) atTop (𝓝 0) := by
  have hL : 0 ≤ L := (abs_nonneg _).trans (by simpa using hg 1 0)
  have hgl : LipschitzWith L.toNNReal g :=
    LipschitzWith.of_dist_le_mul (K := L.toNNReal) (by
      intro x y
      simpa only [Real.dist_eq, Real.coe_toNNReal L hL] using hg x y)
  have hgm := hgl.continuous.measurable
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (n : ℕ) : Measurable (fun p : Ω × ℝ ↦
      ‖leftPointProcess g B t n p.2.toNNReal p.1 - g (B p.2.toNNReal p.1)‖ₑ ^ 2) := by
    exact ((leftPointProcess_measurable hBm hgm t n).sub
      (hgm.comp (hBm.comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)))).enorm.pow_const 2
  have hbound (n : ℕ) (hn : n ≠ 0) :
      (∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
        ‖leftPointProcess g B t n u.toNNReal ω - g (B u.toNNReal ω)‖ₑ ^ 2) ∂P) ≤
      (ENNReal.ofReal L ^ 2 * (t : ℝ≥0∞) ^ 2) * (n : ℝ≥0∞)⁻¹ := by
    rw [lintegral_lintegral_swap (hm n).aemeasurable]
    calc
      _ ≤ ∫⁻ u in Set.Ioc (0 : ℝ) t, ENNReal.ofReal L ^ 2 * (t / n : ℝ≥0) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro u hu
        apply error_moment_bound hB hL hg t u.toNNReal hn
        exact ⟨Real.toNNReal_pos.mpr hu.1, Real.toNNReal_le_iff_le_coe.mpr hu.2⟩
      _ = (ENNReal.ofReal L ^ 2 * (t : ℝ≥0∞) ^ 2) * (n : ℝ≥0∞)⁻¹ := by
        rw [setLIntegral_const, Real.volume_Ioc,
          ENNReal.coe_div (p := t) (show (n : ℝ≥0) ≠ 0 by exact_mod_cast hn)]
        simp only [sub_zero, ENNReal.ofReal_coe_nnreal, ENNReal.coe_natCast, div_eq_mul_inv]
        ring
  have hlim : Tendsto
      (fun n : ℕ ↦ (ENNReal.ofReal L ^ 2 * (t : ℝ≥0∞) ^ 2) * (n : ℝ≥0∞)⁻¹)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (a := ENNReal.ofReal L ^ 2 * (t : ℝ≥0∞) ^ 2) (Or.inr (by finiteness))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Filter.Eventually.of_forall (fun _ ↦ (zero_le : (0 : ℝ≥0∞) ≤ _))
  · filter_upwards [eventually_ne_atTop 0] with n hn
    exact hbound n hn

/-! ### Itô's formula -/

namespace ElementaryIntegrand

/-- The left-point elementary integrand `∑_{k < n} g(B (t k / n)) 1_{(t k / n, t (k + 1) / n]}`
of `u ↦ g (B u)` on the uniform partition of `[0, t]`, for a measurable `g` bounded by `C` and
an adapted `B`. -/
noncomputable def leftPoint {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hBF : Adapted F B) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (t : ℝ≥0) (n : ℕ) : ElementaryIntegrand F where
  n := n
  time := fun k ↦ t * k / n
  monotone_time := fun i j hij ↦ by
    have : ((i : ℕ) : ℝ≥0) ≤ (j : ℕ) := by exact_mod_cast hij
    dsimp only
    gcongr
  coeff := fun k ω ↦ g (B (t * (k.castSucc : ℕ) / n) ω)
  measurable_coeff := fun _ ↦ hg.comp (hBF _)
  bound := C
  abs_coeff_le := fun _ _ ↦ hgC _

private theorem time_le' {t : ℝ≥0} {n k : ℕ} (hk : k ≤ n) : t * k / n ≤ t := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · rw [div_le_iff₀ (by exact_mod_cast hn)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) bot_le

/-- The elementary Itô integral of `leftPoint` at time `t` is the left-point Itô sum
`∑_{k < n} g(B (t k / n)) (B (t (k + 1) / n) - B (t k / n))`. -/
theorem itoIntegral_leftPoint {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hBF : Adapted F B) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    (leftPoint F hBF hg hgC t n).itoIntegral B t ω = ∑ k ∈ Finset.range n,
      g (B (t * k / n) ω) * (B (t * (k + 1) / n) ω - B (t * k / n) ω) := by
  refine (Fin.sum_univ_eq_sum_range (fun k ↦ g (B (t * (k : ℕ) / n) ω) *
    (B (min (t * ((k + 1 : ℕ) : ℝ≥0) / n) t) ω - B (min (t * (k : ℕ) / n) t) ω)) n).trans ?_
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < n := Finset.mem_range.mp hk
  rw [min_eq_left (time_le' hk'), min_eq_left (time_le' hk'.le)]
  push_cast
  rfl

/-- The process of `leftPoint` is `leftPointProcess`. -/
theorem toProcess_leftPoint {Ω : Type*} {mΩ : MeasurableSpace Ω} (F : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hBF : Adapted F B) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (t : ℝ≥0) (n : ℕ) :
    (leftPoint F hBF hg hgC t n).toProcess = leftPointProcess g B t n := by
  funext u ω
  simp only [toProcess, leftPoint, leftPointProcess, Fin.val_castSucc, Fin.val_succ]
  push_cast
  rfl

end ElementaryIntegrand

private theorem sum_taylor_split (n : ℕ) (a b d : ℕ → ℝ) (Δ : ℝ) :
    ∑ k ∈ Finset.range n, (a k * d k + 1 / 2 * b k * d k ^ 2) =
      ∑ k ∈ Finset.range n, a k * d k + 1 / 2 * ∑ k ∈ Finset.range n, b k * (d k ^ 2 - Δ) +
        1 / 2 * ∑ k ∈ Finset.range n, b k * Δ := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

/-- **Itô's formula** for Brownian motion: for a Brownian motion `B` adapted to `F` with
increments independent of the past and jointly measurable in `(t, ω)`, and `f` of class `C²`
with `|f'| ≤ C` and `|f''| ≤ C`,
`f(B t) = f(B 0) + ∫_0^t f'(B u) dB u + (1/2) ∫_0^t f''(B u) du` almost surely, for every
`t ≥ 0` (Karatzas–Shreve 1991, Theorem 3.3.3). The last integral is a pathwise Riemann integral;
it is the integral of a continuous function on almost every path. -/
theorem ito_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    (hBm : Measurable fun p : ℝ≥0 × Ω ↦ B p.1 p.2)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (C : ℝ) (hf1 : ∀ x, |deriv f x| ≤ C)
    (hf2 : ∀ x, |deriv (deriv f) x| ≤ C) (t : ℝ≥0) :
    (fun ω ↦ f (B t ω)) =ᵐ[P]
      fun ω ↦ f (B 0 ω) + itoIntegral P F B (fun u ω' ↦ deriv f (B u ω')) t ω +
        (1 / 2) * ∫ u in (0 : ℝ)..t, deriv (deriv f) (B (Real.toNNReal u) ω) := by
  have hpre := hB.toIsPreBrownianReal
  have hprob := hpre.isGaussianProcess.isProbabilityMeasure
  have hd1 : ContDiff ℝ 1 (deriv f) := hf.iterate_deriv' 1 1
  have hd2 : Continuous (deriv (deriv f)) := (hf.iterate_deriv' 0 2).continuous
  have hd1c : Continuous (deriv f) := hd1.continuous
  have hLip : ∀ x y, |deriv f x - deriv f y| ≤ C * |x - y| := fun x y ↦ by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
      (fun z _ ↦ (hd1.differentiable one_ne_zero).differentiableAt) (fun z _ ↦ hf2 z)
      convex_univ (Set.mem_univ y) (Set.mem_univ x)
    simpa [Real.norm_eq_abs] using this
  set H : ℝ≥0 → Ω → ℝ := fun u ω ↦ deriv f (B u ω)
  have hHm : Measurable fun p : ℝ × Ω ↦ H p.1.toNNReal p.2 :=
    hd1c.measurable.comp (hBm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      measurable_snd))
  set K : ℕ → ElementaryIntegrand F := fun n ↦
    ElementaryIntegrand.leftPoint F hBF hd1c.measurable hf1 t n
  -- `L²` convergence of the left-point Itô sums
  have hA : Tendsto (fun n ↦ eLpNorm ((K n).itoIntegral B t - itoIntegral P F B H t) 2 P)
      atTop (𝓝 0) := by
    have hK : Tendsto (fun n ↦ integrandDist P (K n).toProcess H t) atTop (𝓝 0) := by
      simp only [integrandDist, K, ElementaryIntegrand.toProcess_leftPoint]
      exact tendsto_lintegral_leftPointProcess_sub_sq hpre hBm hLip t
    have hlim := tendsto_toL2_itoIntegral hpre hBF hInd hHm hK
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hlim
    refine hlim.congr' (Eventually.of_forall fun n ↦ eLpNorm_congr_ae ?_)
    have hm := (K n).memLp_itoIntegral hpre t
    simp only [toL2, hm, ↓reduceDIte]
    filter_upwards [hm.coeFn_toLp, itoIntegral_ae_eq P F B H t] with ω h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have hQ1 := tendsto_eLpNorm_weightedQVError (φ := fun _ : ℝ ↦ (1 : ℝ)) (C := 1) hpre hBF hInd
    measurable_const (fun _ ↦ (abs_one).le) t
  have hQ2 := tendsto_eLpNorm_weightedQVError hpre hBF hInd hd2.measurable hf2 t
  obtain ⟨n1, hn1, h1⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (f := fun n ↦ (K n).itoIntegral B t) (g := itoIntegral P F B H t) two_ne_zero
    hA).exists_seq_tendsto_ae
  obtain ⟨n2, hn2, h2⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (f := fun j ↦ weightedQVError (fun _ ↦ 1) B t (n1 j)) (g := 0) two_ne_zero
    (by simpa [Function.comp_def] using hQ1.comp hn1.tendsto_atTop)).exists_seq_tendsto_ae
  obtain ⟨n3, hn3, h3⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (f := fun j ↦ weightedQVError (deriv (deriv f)) B t (n1 (n2 j))) (g := 0) two_ne_zero
    (by simpa [Function.comp_def] using
      (hQ2.comp hn1.tendsto_atTop).comp hn2.tendsto_atTop)).exists_seq_tendsto_ae
  have hφ : StrictMono fun j ↦ n1 (n2 (n3 j)) := hn1.comp (hn2.comp hn3)
  filter_upwards [h1, h2, h3, hB.cont] with ω e1 e2 e3 hc
  set w : ℝ → ℝ := fun u ↦ B u.toNNReal ω with hwdef
  have hw : Continuous w := hc.comp continuous_real_toNNReal
  have hBw : ∀ x : ℝ≥0, B x ω = w x := fun x ↦ by simp [w]
  have hIt : ∀ N, (K N).itoIntegral B t ω = ∑ k ∈ Finset.range N,
      deriv f (w (t * k / N)) * (w (t * (k + 1) / N) - w (t * k / N)) := fun N ↦ by
    simp only [K, ElementaryIntegrand.itoIntegral_leftPoint, hBw]
    push_cast
    rfl
  have hQ : ∀ (φ' : ℝ → ℝ) N, weightedQVError φ' B t N ω = ∑ k ∈ Finset.range N,
      φ' (w (t * k / N)) * ((w (t * (k + 1) / N) - w (t * k / N)) ^ 2 - t / N) := fun φ' N ↦ by
    simp only [weightedQVError, hBw]
    push_cast
    rfl
  set N : ℕ → ℕ := fun j ↦ n1 (n2 (n3 j))
  have hN : Tendsto N atTop atTop := hφ.tendsto_atTop
  have e1' : Tendsto (fun j ↦ (K (N j)).itoIntegral B t ω) atTop
      (𝓝 (itoIntegral P F B H t ω)) := e1.comp (hn2.comp hn3).tendsto_atTop
  have e2' : Tendsto (fun j ↦ weightedQVError (fun _ ↦ 1) B t (N j) ω) atTop (𝓝 0) :=
    e2.comp hn3.tendsto_atTop
  obtain ⟨M, hM⟩ := e2'.bddAbove_range
  have hsq : ∀ j, ∑ k ∈ Finset.range (N j),
      (w (t * (k + 1) / N j) - w (t * k / N j)) ^ 2 ≤ M + t := fun j ↦ by
    have hle : weightedQVError (fun _ ↦ 1) B t (N j) ω ≤ M := hM ⟨j, rfl⟩
    rw [hQ] at hle
    simp only [one_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hle
    have hNt : (N j : ℝ) * (t / N j) ≤ t := by
      rcases Nat.eq_zero_or_pos (N j) with h0 | hpos
      · simp [h0]
      · rw [mul_div_cancel₀ _ (by exact_mod_cast hpos.ne')]
    linarith
  have hT := tendsto_taylor_sum_sub hf hw t.2 hN hsq
  have hR := (tendsto_sum_riemann_uniform (hd2.comp hw) t.2).comp hN
  have hQ2 : Tendsto (fun j ↦ weightedQVError (deriv (deriv f)) B t (N j) ω) atTop (𝓝 0) := e3
  have hsum := ((hT.add e1').add (hQ2.const_mul (1 / 2))).add (hR.const_mul (1 / 2))
  have hid : ∀ j, (f (w t) - f (w 0) - ∑ k ∈ Finset.range (N j),
      (deriv f (w (t * k / N j)) * (w (t * (k + 1) / N j) - w (t * k / N j)) +
        1 / 2 * deriv (deriv f) (w (t * k / N j)) *
          (w (t * (k + 1) / N j) - w (t * k / N j)) ^ 2)) +
      (K (N j)).itoIntegral B t ω + 1 / 2 * weightedQVError (deriv (deriv f)) B t (N j) ω +
      1 / 2 * ∑ k ∈ Finset.range (N j), deriv (deriv f) (w (t * k / N j)) * (t / N j) =
      f (w t) - f (w 0) := fun j ↦ by
    rw [hIt, hQ, sum_taylor_split (N j) (fun k ↦ deriv f (w (t * k / N j)))
      (fun k ↦ deriv (deriv f) (w (t * k / N j)))
      (fun k ↦ w (t * (k + 1) / N j) - w (t * k / N j)) (t / N j)]
    ring
  have hsum' := hsum.congr hid
  have hlim : f (w t) - f (w 0) = 0 + itoIntegral P F B H t ω + 1 / 2 * 0 +
      1 / 2 * ∫ u in (0 : ℝ)..t, deriv (deriv f) (B u.toNNReal ω) :=
    tendsto_nhds_unique tendsto_const_nhds hsum'
  have e0 : B 0 ω = w 0 := by simp [hBw]
  rw [hBw t, e0]
  linarith

end ProbabilityTheory
