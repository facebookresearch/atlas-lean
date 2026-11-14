/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import MathlibExt.Probability.Distributions.GaussianL2Limit

/-!
# Causal AR(1) moving-average representation

For innovations `ε : ℤ → Ω → ℝ` that are independent, identically distributed, square
integrable and mean zero, and for `|ρ| < 1`, the causal moving-average series
`X t = ∑' k, ρ ^ k * ε (t - k)` converges almost surely, satisfies the AR(1) recursion
`X t = ρ * X (t - 1) + ε t` almost surely, has mean zero, and has variance
`Var (ε 0) / (1 - ρ ^ 2)`.

Scope: the mean and the variance of `X t` do not depend on `t`. Neither the autocovariance at
nonzero lags (needed for second-order stationarity) nor equality of the laws of `X t` and `X 0`
is proved here.

## Main results

- `ar1MA_partial_succ`, `ar1MA_partial_recursion`: one-step identities for the truncations
  `ar1MAPartial ε ρ t N = ∑ k < N, ρ ^ k * ε (t - k)`.
- `ar1MA_partial_variance`, `ar1MA_partial_sub_variance`: variances of a truncation and of
  the difference of two truncations.
- `ar1MA_representation`: almost sure convergence, the almost sure recursion, mean zero, and
  the variance `Var (ε 0) / (1 - ρ ^ 2)` of `ar1MA ε ρ t = ∑' k, ρ ^ k * ε (t - k)`.

## Implementation notes

Almost sure convergence follows from the summable `L²` norms of the terms
(`MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top`). The truncations converge to the sum
in `L²` by the Fatou bound `MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto`, and the variance
passes to that limit through `ProbabilityTheory.tendsto_integral_mul_of_tendsto_eLpNorm`.

## References

- J. D. Hamilton, *Time Series Analysis*, Princeton University Press, 1994, Section 3.4.
- P. J. Brockwell and R. A. Davis, *Time Series: Theory and Methods*, 2nd ed., Springer,
  1991, Section 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Filter Topology
open scoped ENNReal

namespace MathlibExt.Probability.TimeSeries.AR1MovingAverage

/-- The truncated moving-average partial sum `∑_{k<N} ρ^k ε_{t-k}`. -/
noncomputable def ar1MAPartial {Ω : Type*} [MeasurableSpace Ω] (ε : ℤ → Ω → ℝ) (ρ : ℝ)
    (t : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.range N, ρ ^ k * ε (t - (k : ℤ)) ω

/-- The causal moving-average (MA(infinity)) sum `∑'_k ρ^k ε_{t-k}`. -/
noncomputable def ar1MA {Ω : Type*} [MeasurableSpace Ω] (ε : ℤ → Ω → ℝ) (ρ : ℝ)
    (t : ℤ) : Ω → ℝ :=
  fun ω => ∑' k : ℕ, ρ ^ k * ε (t - (k : ℤ)) ω

/-- Each MA summand is `MemLp 2`: scaling a finite-variance innovation. -/
private theorem ar1MA_term_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (ρ : ℝ) (hLp : ∀ t, MemLp (ε t) 2 μ) (t : ℤ) (k : ℕ) :
    MemLp (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ :=
  (hLp _).const_mul _

/-- Distinct MA summands are pairwise independent: distinct time indices give
independent innovations, and scaling preserves independence. -/
private theorem ar1MA_term_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (ρ : ℝ) (hIndep : iIndepFun ε μ) (t : ℤ) {i j : ℕ} (hij : i ≠ j) :
    IndepFun (fun ω => ρ ^ i * ε (t - (i : ℤ)) ω)
      (fun ω => ρ ^ j * ε (t - (j : ℤ)) ω) μ := by
  have hne : t - (i : ℤ) ≠ t - (j : ℤ) := by
    intro hcon
    apply hij
    omega
  have h := hIndep.indepFun hne
  have hφ : Measurable (fun x : ℝ => ρ ^ i * x) := measurable_id.const_mul _
  have hψ : Measurable (fun x : ℝ => ρ ^ j * x) := measurable_id.const_mul _
  exact h.comp hφ hψ

/-- Variance of one MA summand: scaling squares, then stationarity. -/
private theorem ar1MA_term_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (ρ : ℝ) (hVar : ∀ t, variance (ε t) μ = variance (ε 0) μ)
    (t : ℤ) (k : ℕ) :
    variance (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) μ
      = variance (ε 0) μ * ρ ^ (2 * k) := by
  have hpow : (ρ ^ k) ^ 2 = ρ ^ (2 * k) := by
    rw [← pow_mul, mul_comm k 2]
  rw [variance_const_mul, hVar, hpow]
  ring

/-- One more term: the length-`N+1` partial sum at `t` is the innovation at `t`
plus `ρ` times the length-`N` partial sum at `t - 1`. -/
theorem ar1MA_partial_succ {Ω : Type*} [MeasurableSpace Ω] (ε : ℤ → Ω → ℝ) (ρ : ℝ)
    (t : ℤ) (N : ℕ) :
    ar1MAPartial ε ρ t (N + 1) = fun ω => ε t ω + ρ * ar1MAPartial ε ρ (t - 1) N ω := by
  funext ω
  induction N with
  | zero =>
    simp [ar1MAPartial]
  | succ N IH =>
    simp only [ar1MAPartial] at IH ⊢
    rw [Finset.sum_range_succ]
    nth_rewrite 2 [Finset.sum_range_succ]
    rw [IH]
    have hterm : ρ ^ (N + 1) * ε (t - ((N + 1 : ℕ) : ℤ)) ω
        = ρ * (ρ ^ N * ε ((t - 1) - (N : ℤ)) ω) := by
      have hcast : (t - 1) - (N : ℤ) = t - ((N + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, pow_succ]
      ring
    rw [hterm, mul_add]
    ring

/-- Recursion with remainder: the length-`N` partial sum at `t` equals
`ρ` times itself at `t - 1`, plus the innovation at `t`, minus the dropped
tail term `ρ^N ε_{t-N}`. -/
theorem ar1MA_partial_recursion {Ω : Type*} [MeasurableSpace Ω] (ε : ℤ → Ω → ℝ) (ρ : ℝ)
    (t : ℤ) (N : ℕ) :
    ar1MAPartial ε ρ t N =
      fun ω => ρ * ar1MAPartial ε ρ (t - 1) N ω + ε t ω - ρ ^ N * ε (t - (N : ℤ)) ω := by
  funext ω
  have hsucc : ar1MAPartial ε ρ t (N + 1) ω
      = ε t ω + ρ * ar1MAPartial ε ρ (t - 1) N ω :=
    congrFun (ar1MA_partial_succ ε ρ t N) ω
  have hpeel : ar1MAPartial ε ρ t (N + 1) ω
      = ar1MAPartial ε ρ t N ω + ρ ^ N * ε (t - (N : ℤ)) ω := by
    simp only [ar1MAPartial]
    rw [Finset.sum_range_succ]
  change ar1MAPartial ε ρ t N ω
    = ρ * ar1MAPartial ε ρ (t - 1) N ω + ε t ω - ρ ^ N * ε (t - (N : ℤ)) ω
  linear_combination hsucc - hpeel

/-- Variance of a truncated moving-average sum: the geometric partial sum times
the innovation variance. -/
theorem ar1MA_partial_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : ρ ^ 2 ≠ 1)
    (hLp : ∀ t, MemLp (ε t) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ t, variance (ε t) μ = variance (ε 0) μ) (t : ℤ) (N : ℕ) :
    variance (ar1MAPartial ε ρ t N) μ =
      variance (ε 0) μ * (1 - ρ ^ (2 * N)) / (1 - ρ ^ 2) := by
  have hsum : ar1MAPartial ε ρ t N
      = ∑ k ∈ Finset.range N, (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) := by
    funext ω
    simp only [ar1MAPartial, Finset.sum_apply]
  have hmem : ∀ i ∈ Finset.range N, MemLp (fun ω => ρ ^ i * ε (t - (i : ℤ)) ω) 2 μ :=
    fun i _ => ar1MA_term_memLp ε ρ hLp t i
  have hpair : Set.Pairwise (↑(Finset.range N) : Set ℕ) fun i j =>
      IndepFun (fun ω => ρ ^ i * ε (t - (i : ℤ)) ω)
        (fun ω => ρ ^ j * ε (t - (j : ℤ)) ω) μ := by
    intro i _ j _ hij
    exact ar1MA_term_indep ε ρ hIndep t hij
  have hvar := IndepFun.variance_sum hmem hpair
  rw [hsum]
  refine hvar.trans ?_
  have hsumEq : (∑ i ∈ Finset.range N, variance (fun ω => ρ ^ i * ε (t - (i : ℤ)) ω) μ)
      = ∑ i ∈ Finset.range N, variance (ε 0) μ * ρ ^ (2 * i) :=
    Finset.sum_congr rfl (fun k _ => ar1MA_term_variance ε ρ hVar t k)
  rw [hsumEq, ← Finset.mul_sum, mul_div_assoc]
  congr 1
  simp only [pow_mul]
  have hgeom := geom_sum_mul (ρ ^ 2) N
  have h1 : (1 : ℝ) - ρ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  rw [eq_div_iff h1]
  linear_combination -hgeom

/-- L2 distance between two truncations: the variance of the difference is the
innovation variance times the geometric tail-block sum. -/
theorem ar1MA_partial_sub_variance {ρ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (hLp : ∀ t, MemLp (ε t) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ t, variance (ε t) μ = variance (ε 0) μ) (t : ℤ) {M N : ℕ} (hMN : N ≤ M) :
    variance (fun ω => ar1MAPartial ε ρ t M ω - ar1MAPartial ε ρ t N ω) μ =
      variance (ε 0) μ * ∑ k ∈ Finset.Ico N M, ρ ^ (2 * k) := by
  have hsum : (fun ω => ar1MAPartial ε ρ t M ω - ar1MAPartial ε ρ t N ω)
      = ∑ k ∈ Finset.Ico N M, (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) := by
    funext ω
    simp only [ar1MAPartial, Finset.sum_apply]
    rw [← Finset.sum_Ico_eq_sub _ hMN]
  have hmem : ∀ i ∈ Finset.Ico N M, MemLp (fun ω => ρ ^ i * ε (t - (i : ℤ)) ω) 2 μ :=
    fun i _ => ar1MA_term_memLp ε ρ hLp t i
  have hpair : Set.Pairwise (↑(Finset.Ico N M) : Set ℕ) fun i j =>
      IndepFun (fun ω => ρ ^ i * ε (t - (i : ℤ)) ω)
        (fun ω => ρ ^ j * ε (t - (j : ℤ)) ω) μ := by
    intro i _ j _ hij
    exact ar1MA_term_indep ε ρ hIndep t hij
  have hvar := IndepFun.variance_sum hmem hpair
  rw [hsum]
  refine hvar.trans ?_
  have hsumEq : (∑ i ∈ Finset.Ico N M, variance (fun ω => ρ ^ i * ε (t - (i : ℤ)) ω) μ)
      = ∑ i ∈ Finset.Ico N M, variance (ε 0) μ * ρ ^ (2 * i) :=
    Finset.sum_congr rfl (fun k _ => ar1MA_term_variance ε ρ hVar t k)
  rw [hsumEq, ← Finset.mul_sum]

/-- `L²` norm of one moving-average term. -/
private theorem ar1MA_term_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (ρ : ℝ) (hNorm : ∀ t, eLpNorm (ε t) 2 μ = eLpNorm (ε 0) 2 μ)
    (t : ℤ) (k : ℕ) :
    eLpNorm (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ =
      ENNReal.ofReal (|ρ| ^ k) * eLpNorm (ε 0) 2 μ := by
  have h1 : (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) = (ρ ^ k) • ε (t - (k : ℤ)) := rfl
  rw [h1, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_pow, hNorm]

/-- Each truncated moving-average sum is square integrable. -/
private theorem ar1MAPartial_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) (ρ : ℝ) (hLp : ∀ t, MemLp (ε t) 2 μ) (t : ℤ) (N : ℕ) :
    MemLp (ar1MAPartial ε ρ t N) 2 μ := by
  have h : ∀ k ∈ Finset.range N, MemLp (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ :=
    fun k _ => (hLp _).const_mul _
  unfold ar1MAPartial
  exact memLp_finsetSum _ h

/-- The moving-average series converges almost surely. -/
private theorem ar1MA_ae_summable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1) (hLp : ∀ t, MemLp (ε t) 2 μ)
    (hNorm : ∀ t, eLpNorm (ε t) 2 μ = eLpNorm (ε 0) 2 μ) (t : ℤ) :
    ∀ᵐ ω ∂μ, Summable (fun k : ℕ => ρ ^ k * ε (t - (k : ℤ)) ω) := by
  have hgeom : Summable (fun k : ℕ => |ρ| ^ k) :=
    summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  have hC : eLpNorm (ε 0) 2 μ ≠ ∞ := (hLp 0).eLpNorm_ne_top
  have hterm : ∀ k : ℕ, eLpNorm (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ
      = ENNReal.ofReal (|ρ| ^ k) * eLpNorm (ε 0) 2 μ :=
    fun k => ar1MA_term_eLpNorm ε ρ hNorm t k
  have hne : ∑' k : ℕ, eLpNorm (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ ≠ ∞ := by
    calc (∑' k : ℕ, eLpNorm (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ)
          = ∑' k : ℕ, (ENNReal.ofReal (|ρ| ^ k) * eLpNorm (ε 0) 2 μ) :=
            tsum_congr hterm
        _ = (∑' k : ℕ, ENNReal.ofReal (|ρ| ^ k)) * eLpNorm (ε 0) 2 μ :=
            ENNReal.tsum_mul_right
        _ = ENNReal.ofReal (∑' k : ℕ, |ρ| ^ k) * eLpNorm (ε 0) 2 μ := by
            congr 1
            exact (ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg (abs_nonneg ρ) k)
              hgeom).symm
        _ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  have hp12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
  have hae := summable_norm_of_tsum_eLpNorm_ne_top hp12 hne
  filter_upwards [hae] with ω hω
  exact Summable.of_norm hω

/-- Pathwise AR(1) recursion for a summable moving-average series. -/
private theorem ar1MA_recursion_of_summable {Ω : Type*} [MeasurableSpace Ω] (ε : ℤ → Ω → ℝ)
    (ρ : ℝ) (t : ℤ) (ω : Ω) (hs : Summable (fun k : ℕ => ρ ^ k * ε (t - (k : ℤ)) ω)) :
    ar1MA ε ρ t ω = ρ * ar1MA ε ρ (t - 1) ω + ε t ω := by
  change (∑' k : ℕ, ρ ^ k * ε (t - (k : ℤ)) ω)
      = ρ * (∑' k : ℕ, ρ ^ k * ε (t - 1 - (k : ℤ)) ω) + ε t ω
  have hterm : ∀ b : ℕ, ρ ^ (b + 1) * ε (t - ((b + 1 : ℕ) : ℤ)) ω
      = ρ * (ρ ^ b * ε (t - 1 - (b : ℤ)) ω) := by
    intro b
    have hidx : t - ((b + 1 : ℕ) : ℤ) = t - 1 - (b : ℤ) := by push_cast; ring
    rw [hidx, pow_succ]
    ring
  have h0 : ρ ^ 0 * ε (t - ((0 : ℕ) : ℤ)) ω = ε t ω := by simp
  calc (∑' k : ℕ, ρ ^ k * ε (t - (k : ℤ)) ω)
        = ρ ^ 0 * ε (t - ((0 : ℕ) : ℤ)) ω
          + ∑' b : ℕ, ρ ^ (b + 1) * ε (t - ((b + 1 : ℕ) : ℤ)) ω :=
          Summable.tsum_eq_zero_add hs
      _ = ε t ω + ∑' b : ℕ, ρ * (ρ ^ b * ε (t - 1 - (b : ℤ)) ω) := by
          rw [h0, tsum_congr hterm]
      _ = ε t ω + ρ * (∑' b : ℕ, ρ ^ b * ε (t - 1 - (b : ℤ)) ω) := by
          rw [tsum_mul_left]
      _ = ρ * (∑' k : ℕ, ρ ^ k * ε (t - 1 - (k : ℤ)) ω) + ε t ω := add_comm _ _

/-- The moving-average sum has mean zero. -/
private theorem ar1MA_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1) (hInt : ∀ t, Integrable (ε t) μ)
    (hMean : ∀ t, ∫ ω, ε t ω ∂μ = 0)
    (hNorm : ∀ t, ∫ ω, ‖ε t ω‖ ∂μ = ∫ ω, ‖ε 0 ω‖ ∂μ) (t : ℤ) :
    ∫ ω, ar1MA ε ρ t ω ∂μ = 0 := by
  have hgeom : Summable (fun k : ℕ => |ρ| ^ k) :=
    summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  have hF_int : ∀ k : ℕ, Integrable (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) μ :=
    fun k => (hInt _).const_mul _
  have hnorm_eq : ∀ k : ℕ, (∫ ω, ‖ρ ^ k * ε (t - (k : ℤ)) ω‖ ∂μ)
      = |ρ| ^ k * ∫ ω, ‖ε 0 ω‖ ∂μ := by
    intro k
    have h1 : ∀ ω : Ω, ‖ρ ^ k * ε (t - (k : ℤ)) ω‖ = |ρ| ^ k * ‖ε (t - (k : ℤ)) ω‖ := by
      intro ω
      rw [norm_mul, norm_pow, Real.norm_eq_abs]
    have h2 : (∫ ω, ‖ρ ^ k * ε (t - (k : ℤ)) ω‖ ∂μ)
        = ∫ ω, |ρ| ^ k * ‖ε (t - (k : ℤ)) ω‖ ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall h1)
    rw [h2, integral_const_mul, hNorm (t - (k : ℤ))]
  have hF_sum : Summable (fun k : ℕ => ∫ ω, ‖ρ ^ k * ε (t - (k : ℤ)) ω‖ ∂μ) := by
    have hfun : (fun k : ℕ => ∫ ω, ‖ρ ^ k * ε (t - (k : ℤ)) ω‖ ∂μ)
        = fun k : ℕ => |ρ| ^ k * ∫ ω, ‖ε 0 ω‖ ∂μ := funext hnorm_eq
    rw [hfun]
    exact hgeom.mul_right _
  have hHasSum : HasSum (fun k : ℕ => ∫ ω, ρ ^ k * ε (t - (k : ℤ)) ω ∂μ)
      (∫ ω, ∑' k : ℕ, ρ ^ k * ε (t - (k : ℤ)) ω ∂μ) :=
    hasSum_integral_of_summable_integral_norm hF_int hF_sum
  have hzero : ∀ k : ℕ, (∫ ω, ρ ^ k * ε (t - (k : ℤ)) ω ∂μ) = 0 := by
    intro k
    rw [integral_const_mul, hMean (t - (k : ℤ)), mul_zero]
  have hfun0 : (fun k : ℕ => ∫ ω, ρ ^ k * ε (t - (k : ℤ)) ω ∂μ) = fun _ => 0 :=
    funext hzero
  rw [hfun0] at hHasSum
  have huniq : (∫ ω, ∑' k : ℕ, ρ ^ k * ε (t - (k : ℤ)) ω ∂μ) = 0 :=
    HasSum.unique hHasSum hasSum_zero
  exact huniq

/-- `L²` bound on a block of the moving-average series. -/
private theorem ar1MA_partial_sub_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1)
    (hNorm : ∀ t, eLpNorm (ε t) 2 μ = eLpNorm (ε 0) 2 μ) (t : ℤ) {M N : ℕ} (hNM : N ≤ M) :
    eLpNorm (fun ω => ar1MAPartial ε ρ t M ω - ar1MAPartial ε ρ t N ω) 2 μ ≤
      ENNReal.ofReal (|ρ| ^ N / (1 - |ρ|)) * eLpNorm (ε 0) 2 μ := by
  have hfun : (fun ω => ar1MAPartial ε ρ t M ω - ar1MAPartial ε ρ t N ω)
      = ∑ k ∈ Finset.Ico N M, (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) := by
    funext ω
    simp only [ar1MAPartial, Finset.sum_apply]
    exact (Finset.sum_Ico_eq_sub _ hNM).symm
  rw [hfun]
  calc eLpNorm (∑ k ∈ Finset.Ico N M, fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ
      ≤ ∑ k ∈ Finset.Ico N M, eLpNorm (fun ω => ρ ^ k * ε (t - (k : ℤ)) ω) 2 μ :=
        MeasureTheory.eLpNorm_sum_le (by norm_num)
    _ = ∑ k ∈ Finset.Ico N M, (ENNReal.ofReal (|ρ| ^ k) * eLpNorm (ε 0) 2 μ) := by
        simp only [ar1MA_term_eLpNorm ε ρ hNorm t]
    _ = (∑ k ∈ Finset.Ico N M, ENNReal.ofReal (|ρ| ^ k)) * eLpNorm (ε 0) 2 μ := by
        rw [← Finset.sum_mul]
    _ = ENNReal.ofReal (∑ k ∈ Finset.Ico N M, |ρ| ^ k) * eLpNorm (ε 0) 2 μ := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => pow_nonneg (abs_nonneg _) _)]
    _ ≤ ENNReal.ofReal (|ρ| ^ N / (1 - |ρ|)) * eLpNorm (ε 0) 2 μ := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one (abs_nonneg _) hρ

/-- `L²` bound on the tail of the moving-average series. -/
private theorem ar1MA_sub_partial_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1) (hLp : ∀ t, MemLp (ε t) 2 μ)
    (hNorm : ∀ t, eLpNorm (ε t) 2 μ = eLpNorm (ε 0) 2 μ) (t : ℤ) (N : ℕ) :
    eLpNorm (fun ω => ar1MA ε ρ t ω - ar1MAPartial ε ρ t N ω) 2 μ ≤
      ENNReal.ofReal (|ρ| ^ N / (1 - |ρ|)) * eLpNorm (ε 0) 2 μ := by
  have hbound : ∀ᶠ M in atTop,
      eLpNorm (fun ω => ar1MAPartial ε ρ t M ω - ar1MAPartial ε ρ t N ω) 2 μ ≤
        ENNReal.ofReal (|ρ| ^ N / (1 - |ρ|)) * eLpNorm (ε 0) 2 μ := by
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    exact ar1MA_partial_sub_eLpNorm_le ε hρ hNorm t hM
  have hmeas : ∀ M : ℕ, AEStronglyMeasurable
      (fun ω => ar1MAPartial ε ρ t M ω - ar1MAPartial ε ρ t N ω) μ := by
    intro M
    exact ((ar1MAPartial_memLp ε ρ hLp t M).sub
      (ar1MAPartial_memLp ε ρ hLp t N)).aestronglyMeasurable
  have hae : ∀ᵐ ω ∂μ, Tendsto (fun M : ℕ => ar1MAPartial ε ρ t M ω - ar1MAPartial ε ρ t N ω)
      atTop (𝓝 (ar1MA ε ρ t ω - ar1MAPartial ε ρ t N ω)) := by
    filter_upwards [ar1MA_ae_summable ε hρ hLp hNorm t] with ω hω
    have hT : Tendsto (fun M : ℕ => ar1MAPartial ε ρ t M ω) atTop (𝓝 (ar1MA ε ρ t ω)) :=
      hω.hasSum.tendsto_sum_nat
    exact hT.sub_const _
  have hg : AEStronglyMeasurable (fun ω => ar1MA ε ρ t ω - ar1MAPartial ε ρ t N ω) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hae
  exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto hbound hmeas hg hae

/-- The truncations converge to the moving-average sum in `L²`. -/
private theorem ar1MA_tendsto_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1) (hLp : ∀ t, MemLp (ε t) 2 μ)
    (hNorm : ∀ t, eLpNorm (ε t) 2 μ = eLpNorm (ε 0) 2 μ) (t : ℤ) :
    Tendsto (fun N : ℕ => eLpNorm (ar1MAPartial ε ρ t N - ar1MA ε ρ t) 2 μ) atTop (𝓝 0) := by
  have hle : ∀ N : ℕ, eLpNorm (ar1MAPartial ε ρ t N - ar1MA ε ρ t) 2 μ ≤
      ENNReal.ofReal (|ρ| ^ N / (1 - |ρ|)) * eLpNorm (ε 0) 2 μ := by
    intro N
    rw [MeasureTheory.eLpNorm_sub_comm]
    exact ar1MA_sub_partial_eLpNorm_le ε hρ hLp hNorm t N
  have hup : Tendsto (fun N : ℕ => ENNReal.ofReal (|ρ| ^ N / (1 - |ρ|)) * eLpNorm (ε 0) 2 μ)
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => |ρ| ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hρ
    have hdiv : Tendsto (fun N : ℕ => |ρ| ^ N / (1 - |ρ|)) atTop (𝓝 (0 / (1 - |ρ|))) :=
      hpow.div_const _
    rw [zero_div] at hdiv
    have hof : Tendsto (fun N : ℕ => ENNReal.ofReal (|ρ| ^ N / (1 - |ρ|))) atTop
        (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal hdiv
    rw [ENNReal.ofReal_zero] at hof
    have hmul := ENNReal.Tendsto.mul_const hof (Or.inr (hLp 0).eLpNorm_ne_top)
    rw [zero_mul] at hmul
    exact hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun N => zero_le) hle

/-- The moving-average sum is square integrable. -/
private theorem ar1MA_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1) (hLp : ∀ t, MemLp (ε t) 2 μ)
    (hNorm : ∀ t, eLpNorm (ε t) 2 μ = eLpNorm (ε 0) 2 μ) (t : ℤ) :
    MemLp (ar1MA ε ρ t) 2 μ := by
  exact MeasureTheory.Lp.memLp_of_cauchy_tendsto (by simp)
    (fun N => ar1MAPartial_memLp ε ρ hLp t N) (ar1MA ε ρ t)
    (ar1MA_tendsto_eLpNorm ε hρ hLp hNorm t)

/-- Variance is continuous along `L²` convergence under a probability measure. -/
private theorem tendsto_variance_of_tendsto_eLpNorm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ) (hY : MemLp Y 2 μ)
    (h : Tendsto (fun n => eLpNorm (X n - Y) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => variance (X n) μ) atTop (𝓝 (variance Y μ)) := by
  have h12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
  have hL1 : Tendsto (fun n => eLpNorm (X n - Y) 1 μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun n => zero_le) fun n => eLpNorm_le_eLpNorm_of_exponent_le h12
  have hm : Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (𝓝 (∫ ω, Y ω ∂μ)) :=
    tendsto_integral_of_L1' Y
      (Filter.Eventually.of_forall fun n => (hX n).integrable h12) hL1
  have hs : Tendsto (fun n => ∫ ω, X n ω * X n ω ∂μ) atTop (𝓝 (∫ ω, Y ω * Y ω ∂μ)) :=
    ProbabilityTheory.tendsto_integral_mul_of_tendsto_eLpNorm hX hX hY hY h h
  simpa only [variance_eq_sub (hX _), variance_eq_sub hY, Pi.pow_apply, pow_two] using
    hs.sub (hm.pow 2)

/-- Variance of the moving-average sum. -/
private theorem ar1MA_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1)
    (hLp : ∀ t, MemLp (ε t) 2 μ) (hIndep : iIndepFun ε μ)
    (hVar : ∀ t, variance (ε t) μ = variance (ε 0) μ)
    (hNorm : ∀ t, eLpNorm (ε t) 2 μ = eLpNorm (ε 0) 2 μ) (t : ℤ) :
    variance (ar1MA ε ρ t) μ = variance (ε 0) μ / (1 - ρ ^ 2) := by
  have hρ2 : ρ ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one ρ).mpr hρ
  have hne : ρ ^ 2 ≠ 1 := ne_of_lt hρ2
  have hcont : Tendsto (fun N => variance (ar1MAPartial ε ρ t N) μ) atTop
      (𝓝 (variance (ar1MA ε ρ t) μ)) :=
    tendsto_variance_of_tendsto_eLpNorm (fun N => ar1MAPartial_memLp ε ρ hLp t N)
      (ar1MA_memLp ε hρ hLp hNorm t) (ar1MA_tendsto_eLpNorm ε hρ hLp hNorm t)
  have hpow : Tendsto (fun N : ℕ => ρ ^ (2 * N)) atTop (𝓝 0) :=
    Filter.Tendsto.congr (fun N => (pow_mul ρ 2 N).symm)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ρ) hρ2)
  have hsub : Tendsto (fun N : ℕ => (1 : ℝ) - ρ ^ (2 * N)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hpow
  have hmul : Tendsto (fun N : ℕ => variance (ε 0) μ * (1 - ρ ^ (2 * N))) atTop
      (𝓝 (variance (ε 0) μ * (1 - 0))) :=
    Filter.Tendsto.const_mul _ hsub
  have hdiv : Tendsto (fun N : ℕ => variance (ε 0) μ * (1 - ρ ^ (2 * N)) / (1 - ρ ^ 2)) atTop
      (𝓝 (variance (ε 0) μ * (1 - 0) / (1 - ρ ^ 2))) :=
    Filter.Tendsto.div_const hmul _
  have hlim : variance (ε 0) μ * (1 - 0) / (1 - ρ ^ 2) = variance (ε 0) μ / (1 - ρ ^ 2) := by
    rw [sub_zero, mul_one]
  rw [hlim] at hdiv
  have hcongr : ∀ N : ℕ, variance (ar1MAPartial ε ρ t N) μ =
      variance (ε 0) μ * (1 - ρ ^ (2 * N)) / (1 - ρ ^ 2) :=
    fun N => ar1MA_partial_variance ε hne hLp hIndep hVar t N
  have hcont' : Tendsto (fun N : ℕ => variance (ε 0) μ * (1 - ρ ^ (2 * N)) / (1 - ρ ^ 2)) atTop
      (𝓝 (variance (ar1MA ε ρ t) μ)) :=
    Filter.Tendsto.congr hcongr hcont
  exact tendsto_nhds_unique hcont' hdiv

/-- The causal MA(infinity) representation: for iid mean-zero finite-variance
innovations and `|ρ| < 1`, the MA series is a.s. summable, its sum satisfies
the AR(1) recursion a.s., has mean zero, and has variance
`Var(ε_0) / (1 - ρ²)`. -/
theorem ar1MA_representation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ε : ℤ → Ω → ℝ) {ρ : ℝ} (hρ : |ρ| < 1)
    (hLp : MemLp (ε 0) 2 μ) (hIndep : iIndepFun ε μ)
    (hIdent : ∀ t, IdentDistrib (ε t) (ε 0) μ μ)
    (hMean : ∫ ω, ε 0 ω ∂μ = 0) (t : ℤ) :
    (∀ᵐ ω ∂μ, Summable (fun k : ℕ => ρ ^ k * ε (t - (k : ℤ)) ω)) ∧
      (∀ᵐ ω ∂μ, ar1MA ε ρ t ω = ρ * ar1MA ε ρ (t - 1) ω + ε t ω) ∧
      (∫ ω, ar1MA ε ρ t ω ∂μ = 0) ∧
      variance (ar1MA ε ρ t) μ = variance (ε 0) μ / (1 - ρ ^ 2) := by
  have h12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
  have hLp_all : ∀ s, MemLp (ε s) 2 μ := fun s => (hIdent s).symm.memLp_snd hLp
  have hmean_all : ∀ s, ∫ ω, ε s ω ∂μ = 0 := fun s => (hIdent s).integral_eq.trans hMean
  have hvar_all : ∀ s, variance (ε s) μ = variance (ε 0) μ := fun s => (hIdent s).variance_eq
  have hnorm_all : ∀ s, eLpNorm (ε s) 2 μ = eLpNorm (ε 0) 2 μ :=
    fun s => (hIdent s).eLpNorm_eq 2
  have hnorm1_all : ∀ s, ∫ ω, ‖ε s ω‖ ∂μ = ∫ ω, ‖ε 0 ω‖ ∂μ :=
    fun s => (hIdent s).norm.integral_eq
  have hint_all : ∀ s, Integrable (ε s) μ := fun s => (hLp_all s).integrable h12
  have hsumm : ∀ᵐ ω ∂μ, Summable (fun k : ℕ => ρ ^ k * ε (t - (k : ℤ)) ω) :=
    ar1MA_ae_summable ε hρ hLp_all hnorm_all t
  refine ⟨hsumm, ?_, ?_, ?_⟩
  · filter_upwards [hsumm] with ω hω
    exact ar1MA_recursion_of_summable ε ρ t ω hω
  · exact ar1MA_integral_eq_zero ε hρ hint_all hmean_all hnorm1_all t
  · exact ar1MA_variance ε hρ hLp_all hIndep hvar_all hnorm_all t

end MathlibExt.Probability.TimeSeries.AR1MovingAverage
