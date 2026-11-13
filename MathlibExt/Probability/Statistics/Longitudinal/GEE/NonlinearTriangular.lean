/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.TriangularArrays
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.Calculus.Deriv.Basic
import MathlibExt.Probability.Statistics.MLEAsymptoticNormality
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Nonlinear cluster estimating equations: root consistency and linearization

`TriangularArrays.lean` (T36) proves CLTs for the standardized score `Ψₙ(β₀) / Bₙ` of a
triangular array of clusters and, for estimators, treats only the linear equation
`∑ᵢ (S i - m β) = 0`. This file supplies the two steps that turn a score CLT into a CLT for a
root `β̂ₙ` of a **nonlinear** cluster estimating equation `Ψₙ(β) = ∑_{i<n} ψ_{n,i}(β) = 0`
(`nonlinearEE`), with a scalar parameter `β ∈ ℝ` and triangular-array normalizations.

## Root consistency

* `tendstoInMeasure_root_of_antitone`: for an antitone (decreasing) estimating function, if
  `β̂ₙ` is a root with probability tending to one and `Ψₙ(β₀ - ε) > 0 > Ψₙ(β₀ + ε)` with
  probability tending to one for each `ε > 0`, then `β̂ₙ → β₀` in probability.
* `tendstoInMeasure_root_of_limit`: the same from `Ψₙ(β) / aₙ → λ(β)` in probability with a
  limit `λ` changing sign at `β₀` (identifiability).
* `nonlinearEE_tendstoInMeasure_div`: a triangular weak law (Chebyshev) giving that convergence
  when the contributions are pairwise independent within each row, from
  `∑ᵢ 𝔼 ψ_{n,i}(β) / aₙ → λ(β)` and
  `∑ᵢ Var ψ_{n,i}(β) / aₙ² → 0` (`tendstoInMeasure_div_of_variance` is the general form).
* `tendsto_measure_not_exists_root`: for a continuous estimating function the same sign
  conditions give a root in `(β₀ - ε, β₀ + ε)` with probability tending to one (intermediate value
  theorem). This is existence only; no measurable selection of a root is constructed, so the
  theorems below take a measurable root sequence `β̂ₙ` as input.

## Linearization

* `abs_linearization_sub_le` (pathwise): if the slope of `Ψ` stays within `ε D` of `-D` on
  `[β₀ - δ, β₀ + δ]` and `b` is a root there, then
  `|D (b - β₀) - Ψ(β₀)| ≤ ε / (1 - ε) · |Ψ(β₀)|`. It uses the mean-value inequality, so no
  intermediate point is chosen and no measurability of one is needed.
* `tendstoInDistribution_of_linearization`: if `Ψₙ(β₀) / Bₙ ⇒ Y`, `β̂ₙ` is a consistent root
  with probability tending to one, and the slope is locally uniformly close to `-Dₙ` in
  probability, then `Dₙ (β̂ₙ - β₀) / Bₙ ⇒ Y` (Slutsky).
* `triangular_nonlinearEE_clt`: the combination with T36's cluster CLT. Under bounded cluster
  scores with negligible largest cluster (`K Mₙ / Bₙ → 0`), monotonicity, the sign conditions
  and the slope condition, `Dₙ (β̂ₙ - β₀) / Bₙ ⇒ N(0, 1)`: asymptotic normality with sandwich
  variance `Bₙ² / Dₙ²`, normalized by `Dₙ / Bₙ`, not `√n`.

## Scope

Scalar parameter only; the vector GEE case (matrix sensitivity `Dₙ`, Cramér–Wold) is not done.
Consistency is proved for monotone estimating functions; the general case through uniform
convergence on compacta is not done. Roots are exact: `Ψₙ(β̂ₙ) = 0` with probability tending to one,
stronger than van der Vaart's Lemma 5.10 hypothesis `Ψₙ(β̂ₙ) = o_P(1)`, so discontinuous estimating
functions whose exact roots may not exist (sign or median scores, binary-response equations as in
`binaryEE_no_root`) are not covered. The slope condition is stated with a deterministic `Dₙ`; taking
`Dₙ = -𝔼 Ψ'ₙ(β₀)` and deriving the condition from moment or Lipschitz bounds on `ψ'` is left to the
user. The test file discharges every hypothesis for a smooth nonlinear mean model
(`ψ_{n,i}(β) = U n i + sinh β₀ - sinh β`, explicit root, `Dₙ = n cosh β₀`), and on a concrete
probability space (iid Rademacher clusters on `ℕ → Bool`) obtains the CLT with no remaining
assumptions. Boundary cases in the test file: a degenerate sensitivity (`g(β) = β³` at `β₀ = 0`)
violates the slope condition for every `Dₙ > 0`, and a non-identified equation (`Ψₙ ≡ 0`) has an
inconsistent root sequence.
T36's `binaryEE_no_root` already shows a root need not exist.

## Source

Reuse search (API-00 gate, base `1686a6b76`): T36's
`ProbabilityTheory.GEE.Triangular.triangular_cluster_clt` (score CLT),
`MeasureTheory.TendstoInDistribution.mul_tendstoInMeasure_zero` and
`MeasureTheory.tendstoInMeasure_zero_of_abs_le` (`MLEAsymptoticNormality`, used for the Slutsky
step), Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub`,
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` (mean-value inequality),
`meas_ge_le_variance_div_sq` (Chebyshev), `IndepFun.variance_sum` and
`intermediate_value_Ioo'`. The repository's only Z-estimator CLT,
`MLEAsymptoticNormality.tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation`, is for iid
observations with `√n` normalization and a second-derivative envelope; no triangular-array or
cluster version of root consistency or linearization existed.
Mathematical references: A. W. van der Vaart, *Asymptotic Statistics* (1998), Lemma 5.10 (exact-root
form; consistency of roots of monotone estimating equations) and Theorem 5.21 (linearization of
Z-estimators); K.-Y. Liang and S. L. Zeger, *Longitudinal data analysis using generalized linear
models*, Biometrika 73 (1986) 13–22; M. Xie and Y. Yang, *Asymptotics for generalized estimating
equations with large cluster sizes*, Ann. Statist. 31 (2003) 310–347 (triangular arrays of clusters
with growing sizes).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace ProbabilityTheory.GEE.NonlinearTriangular

open ProbabilityTheory.GEE.Triangular

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Root consistency for a monotone estimating function -/

/-- **Root consistency, monotone case.** Let `β ↦ Ψ n β ω` be antitone (a decreasing
estimating function, e.g. a GLM score). If `β̂ₙ` is a root with probability tending to one and,
for every `ε > 0`, `Ψₙ(β₀ - ε) > 0` and `Ψₙ(β₀ + ε) < 0` with probability tending to one, then
`β̂ₙ → β₀` in probability. No continuity in `β` is needed. -/
theorem tendstoInMeasure_root_of_antitone {Ψ : ℕ → ℝ → Ω → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ : ℝ}
    (hanti : ∀ n ω, Antitone fun β => Ψ n β ω)
    (hroot : Tendsto (fun n => μ {ω | Ψ n (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    (hleft : ∀ ε > 0, Tendsto (fun n => μ {ω | Ψ n (β₀ - ε) ω ≤ 0}) atTop (𝓝 0))
    (hright : ∀ ε > 0, Tendsto (fun n => μ {ω | 0 ≤ Ψ n (β₀ + ε) ω}) atTop (𝓝 0)) :
    TendstoInMeasure μ βhat atTop (fun _ => β₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have h3 := (hroot.add (hleft ε hε)).add (hright ε hε)
  simp only [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_cases h0 : Ψ n (βhat n ω) ω = 0
  · rcases le_abs'.1 hω with h | h
    · exact Or.inl (Or.inr ((hanti n ω (by linarith)).trans h0.le))
    · exact Or.inr (h0.ge.trans (hanti n ω (by linarith)))
  · exact Or.inl (Or.inl h0)

/-- **Existence of a root with probability tending to one.** If `β ↦ Ψ n β ω` is continuous and
`Ψₙ(β₀ - ε) > 0 > Ψₙ(β₀ + ε)` with probability tending to one, then with probability tending to
one `Ψₙ` has a root in `(β₀ - ε, β₀ + ε)` (intermediate value theorem). This does not select
a measurable root; the asymptotic theorems below take a given root sequence `β̂ₙ`. -/
theorem tendsto_measure_not_exists_root {Ψ : ℕ → ℝ → Ω → ℝ} {β₀ ε : ℝ} (hε : 0 < ε)
    (hcont : ∀ n ω, Continuous fun β => Ψ n β ω)
    (hleft : Tendsto (fun n => μ {ω | Ψ n (β₀ - ε) ω ≤ 0}) atTop (𝓝 0))
    (hright : Tendsto (fun n => μ {ω | 0 ≤ Ψ n (β₀ + ε) ω}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {ω | ¬ ∃ β ∈ Set.Ioo (β₀ - ε) (β₀ + ε), Ψ n β ω = 0}) atTop (𝓝 0) := by
  have h2 := hleft.add hright
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_contra h
  push Not at h
  obtain ⟨β, hβ, hβ0⟩ := intermediate_value_Ioo' (by linarith : β₀ - ε ≤ β₀ + ε)
    (hcont n ω).continuousOn (show (0 : ℝ) ∈ Set.Ioo (Ψ n (β₀ + ε) ω) (Ψ n (β₀ - ε) ω) from
      ⟨h.2, h.1⟩)
  exact hω ⟨β, hβ, hβ0⟩

/-! ### A triangular weak law at a fixed parameter value -/

/-- **Weak law by Chebyshev's inequality.** If `𝔼[Xₙ] / aₙ → c` and `Var[Xₙ] / aₙ² → 0`, then
`Xₙ / aₙ → c` in probability. No identical distribution or independence is assumed here; for a
row sum of independent terms the variance splits (`nonlinearEE_tendstoInMeasure_div`). -/
theorem tendstoInMeasure_div_of_variance [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    {c : ℝ} (hX : ∀ n, MemLp (X n) 2 μ) (ha : ∀ᶠ n in atTop, a n ≠ 0)
    (hmean : Tendsto (fun n => μ[X n] / a n) atTop (𝓝 c))
    (hvar : Tendsto (fun n => Var[X n; μ] / a n ^ 2) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => X n ω / a n) atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hlim : Tendsto (fun n => ENNReal.ofReal ((2 / ε) ^ 2 * (Var[X n; μ] / a n ^ 2))) atTop
      (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hvar.const_mul ((2 / ε) ^ 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  have hm : Tendsto (fun n => |μ[X n] / a n - c|) atTop (𝓝 0) := by
    simpa using (hmean.sub_const c).abs
  filter_upwards [ha, hm.eventually (gt_mem_nhds (half_pos hε))] with n han hn
  have hpos : 0 < ε / 2 * |a n| := by positivity
  refine (measure_mono fun ω hω => ?_).trans ((meas_ge_le_variance_div_sq (hX n) hpos).trans
    (le_of_eq ?_))
  · simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
    have key : X n ω - μ[X n] = a n * ((X n ω / a n - c) - (μ[X n] / a n - c)) := by
      field_simp; ring
    rw [key, abs_mul, mul_comm (ε / 2)]
    gcongr
    have := abs_sub_abs_le_abs_sub (X n ω / a n - c) (μ[X n] / a n - c)
    linarith
  · congr 1
    rw [mul_pow, sq_abs]
    field_simp

/-- Convergence in probability to a positive constant forces positivity with probability
tending to one. -/
theorem tendsto_measure_nonpos_of_tendstoInMeasure {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (ha : ∀ᶠ n in atTop, 0 < a n)
    (hX : TendstoInMeasure μ (fun n ω => X n ω / a n) atTop (fun _ => c)) :
    Tendsto (fun n => μ {ω | X n ω ≤ 0}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_norm] at hX
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hX c hc)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [ha] with n han
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
  have : X n ω / a n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hω han.le
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  linarith

/-- Convergence in probability to a negative constant forces negativity with probability
tending to one. -/
theorem tendsto_measure_nonneg_of_tendstoInMeasure {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {c : ℝ}
    (hc : c < 0) (ha : ∀ᶠ n in atTop, 0 < a n)
    (hX : TendstoInMeasure μ (fun n ω => X n ω / a n) atTop (fun _ => c)) :
    Tendsto (fun n => μ {ω | 0 ≤ X n ω}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_norm] at hX
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hX (-c) (by linarith))
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [ha] with n han
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at hω ⊢
  have : 0 ≤ X n ω / a n := div_nonneg hω han.le
  rw [abs_of_pos (by linarith)]
  linarith

/-- **Root consistency from a limiting estimating function.** If `β ↦ Ψ n β ω` is antitone,
`β̂ₙ` is a root with probability tending to one, and for each `β` the normalized estimating
function converges in probability, `Ψₙ(β) / aₙ → λ(β)`, to a limit that changes sign at `β₀`
(`λ(β₀ - ε) > 0 > λ(β₀ + ε)` for every `ε > 0`: identifiability), then `β̂ₙ → β₀` in
probability. -/
theorem tendstoInMeasure_root_of_limit {Ψ : ℕ → ℝ → Ω → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ : ℝ}
    {a : ℕ → ℝ} {lam : ℝ → ℝ} (hanti : ∀ n ω, Antitone fun β => Ψ n β ω)
    (hroot : Tendsto (fun n => μ {ω | Ψ n (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hlim : ∀ β, TendstoInMeasure μ (fun n ω => Ψ n β ω / a n) atTop (fun _ => lam β))
    (hleft : ∀ ε > 0, 0 < lam (β₀ - ε)) (hright : ∀ ε > 0, lam (β₀ + ε) < 0) :
    TendstoInMeasure μ βhat atTop (fun _ => β₀) :=
  tendstoInMeasure_root_of_antitone hanti hroot
    (fun ε hε => tendsto_measure_nonpos_of_tendstoInMeasure (hleft ε hε) ha (hlim _))
    (fun ε hε => tendsto_measure_nonneg_of_tendstoInMeasure (hright ε hε) ha (hlim _))

/-! ### Nonlinear cluster estimating equations -/

/-- Nonlinear cluster estimating function of row `n`: `Ψₙ(β) = ∑_{i<n} ψ_{n,i}(β)`, where
`ψ n i β ω` is the estimating function contributed by cluster `i` of row `n` at parameter
`β`. The dependence on `β` is arbitrary (T36's `linearEE` is the case `ψ n i β = S i - m β`). -/
def nonlinearEE (ψ : ℕ → ℕ → ℝ → Ω → ℝ) (n : ℕ) (β : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ range n, ψ n i β ω

/-- **Triangular weak law for the estimating function at a fixed `β`.** For pairwise
independent, square-integrable cluster contributions, if `∑ᵢ 𝔼[ψ_{n,i}(β)] / aₙ → c` and
`∑ᵢ Var[ψ_{n,i}(β)] / aₙ² → 0`, then `Ψₙ(β) / aₙ → c` in probability. -/
theorem nonlinearEE_tendstoInMeasure_div [IsProbabilityMeasure μ] {ψ : ℕ → ℕ → ℝ → Ω → ℝ}
    {β : ℝ} {a : ℕ → ℝ} {c : ℝ} (hL2 : ∀ n, ∀ i ∈ range n, MemLp (ψ n i β) 2 μ)
    (hind : ∀ n, Set.Pairwise ↑(range n) fun i j => ψ n i β ⟂ᵢ[μ] ψ n j β)
    (ha : ∀ᶠ n in atTop, a n ≠ 0)
    (hmean : Tendsto (fun n => (∑ i ∈ range n, μ[ψ n i β]) / a n) atTop (𝓝 c))
    (hvar : Tendsto (fun n => (∑ i ∈ range n, Var[ψ n i β; μ]) / a n ^ 2) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => nonlinearEE ψ n β ω / a n) atTop (fun _ => c) := by
  have hfun : ∀ n, (fun ω => nonlinearEE ψ n β ω) = ∑ i ∈ range n, ψ n i β := by
    intro n; funext ω; simp [nonlinearEE]
  refine tendstoInMeasure_div_of_variance (X := fun n ω => nonlinearEE ψ n β ω)
    (fun n => (hfun n) ▸ memLp_finsetSum' _ (hL2 n)) ha ?_ ?_
  · refine hmean.congr fun n => ?_
    change _ = (∫ ω, ∑ i ∈ range n, ψ n i β ω ∂μ) / a n
    rw [integral_finsetSum _ fun i hi => (hL2 n i hi).integrable one_le_two]
  · refine hvar.congr fun n => ?_
    rw [hfun n, IndepFun.variance_sum (hL2 n) (hind n)]

/-! ### Pathwise linearization -/

/-- **Linearization bound.** Let `f` have derivative `f'` on `[β₀ - δ, β₀ + δ]` with
`|f'(β) + D| ≤ ε D` there (`D > 0`, `0 ≤ ε < 1`): the slope stays within a factor `1 ± ε` of
`-D`. If `b` lies in that interval and `f b = 0`, then the one-step linearization
`D (b - β₀) ≈ f β₀` holds with relative error `ε / (1 - ε)`:
`|D (b - β₀) - f β₀| ≤ ε / (1 - ε) · |f β₀|`. -/
theorem abs_linearization_sub_le {f f' : ℝ → ℝ} {β₀ b D δ ε : ℝ} (hD : 0 < D)
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hf : ∀ β ∈ Metric.closedBall β₀ δ, HasDerivAt f (f' β) β)
    (hslope : ∀ β ∈ Metric.closedBall β₀ δ, |f' β + D| ≤ ε * D)
    (hb : b ∈ Metric.closedBall β₀ δ) (hroot : f b = 0) :
    |D * (b - β₀) - f β₀| ≤ ε / (1 - ε) * |f β₀| := by
  have hβ₀ : β₀ ∈ Metric.closedBall β₀ δ :=
    Metric.mem_closedBall_self (dist_nonneg.trans (Metric.mem_closedBall.1 hb))
  have hg : ∀ β ∈ Metric.closedBall β₀ δ,
      HasDerivWithinAt (fun x => f x + D * (x - β₀)) (f' β + D) (Metric.closedBall β₀ δ) β := by
    intro β hβ
    have := (hf β hβ).fun_add (((hasDerivAt_id β).sub_const β₀).const_mul D)
    rw [mul_one] at this
    exact this.hasDerivWithinAt
  have hmvt := (convex_closedBall β₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le hg
    (fun β hβ => by simpa [Real.norm_eq_abs] using hslope β hβ) hβ₀ hb
  simp only [Real.norm_eq_abs, hroot, sub_self, mul_zero, add_zero, zero_add] at hmvt
  -- `hmvt : |D * (b - β₀) - f β₀| ≤ ε * D * |b - β₀|`
  have hDx : |D * (b - β₀) - f β₀| ≤ ε * |D * (b - β₀)| := by
    rw [abs_mul, abs_of_pos hD]; linarith
  have hDx' : (1 - ε) * |D * (b - β₀)| ≤ |f β₀| := by
    have := abs_sub_abs_le_abs_sub (D * (b - β₀)) (f β₀)
    nlinarith
  have h1 : 0 < 1 - ε := by linarith
  calc |D * (b - β₀) - f β₀| ≤ ε * |D * (b - β₀)| := hDx
    _ ≤ ε * (|f β₀| / (1 - ε)) := by
        gcongr; rw [le_div_iff₀ h1]; linarith
    _ = ε / (1 - ε) * |f β₀| := by ring

/-! ### Asymptotic normality of a consistent root -/

/-- The event where the linearization applies fails with probability tending to `0`: `β̂ₙ` is a
root, lies within `δ` of `β₀`, and the slope is within `ε D n` of `-D n` on `[β₀ - δ, β₀ + δ]`. -/
private theorem tendsto_measure_not_good {Ψ Ψ' : ℕ → ℝ → Ω → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ : ℝ}
    {D : ℕ → ℝ} {ε δ : ℝ} (hδ : 0 < δ)
    (hroot : Tendsto (fun n => μ {ω | Ψ n (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure μ βhat atTop (fun _ => β₀))
    (hbad : Tendsto (fun n => μ {ω | ∃ β ∈ Metric.closedBall β₀ δ, ε * D n < |Ψ' n β ω + D n|})
      atTop (𝓝 0)) :
    Tendsto (fun n => μ {ω | ¬ (Ψ n (βhat n ω) ω = 0 ∧ |βhat n ω - β₀| < δ ∧
      ∀ β ∈ Metric.closedBall β₀ δ, |Ψ' n β ω + D n| ≤ ε * D n)}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_norm] at hcons
  have h3 := (hroot.add (hcons δ hδ)).add hbad
  simp only [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))
  simp only [Set.mem_ofPred_eq, Set.mem_union, Real.norm_eq_abs, not_and_or, not_lt,
    not_forall, not_le, exists_prop] at hω ⊢
  tauto

/-- **Asymptotic normality of a consistent root by linearization** (triangular arrays, general
normalizations). Let `Ψₙ(β, ω)` be differentiable in `β` with derivative `Ψ'ₙ(β, ω)`, and let
`Bₙ > 0` (score scale) and `Dₙ > 0` (sensitivity, e.g. `Dₙ = -𝔼[Ψ'ₙ(β₀)]`) be deterministic.
Assume

* the standardized estimating function at the truth converges in distribution,
  `Ψₙ(β₀) / Bₙ ⇒ Y`;
* `β̂ₙ` is (a.e.-)measurable, a root with probability tending to one, and consistent;
* the slope is locally uniformly close to `-Dₙ`: for every `ε > 0` there is `δ > 0` with
  `P(∃ β ∈ [β₀ - δ, β₀ + δ], |Ψ'ₙ(β) + Dₙ| > ε Dₙ) → 0` (outer probability; no measurability
  of this event is required).

Then `Dₙ (β̂ₙ - β₀) / Bₙ ⇒ Y`. The asymptotic variance of `β̂ₙ` is the sandwich
`Bₙ² / Dₙ²` times `Var Y`. -/
theorem tendstoInDistribution_of_linearization [IsProbabilityMeasure μ] {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Ψ Ψ' : ℕ → ℝ → Ω → ℝ} {βhat : ℕ → Ω → ℝ} {β₀ : ℝ} {B D : ℕ → ℝ} {Y : Ω' → ℝ}
    (hZ : TendstoInDistribution (fun n ω => Ψ n β₀ ω / B n) atTop Y (fun _ => μ) μ')
    (hB : ∀ᶠ n in atTop, 0 < B n) (hD : ∀ᶠ n in atTop, 0 < D n)
    (hβ_meas : ∀ n, AEMeasurable (βhat n) μ)
    (hroot : Tendsto (fun n => μ {ω | Ψ n (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    (hcons : TendstoInMeasure μ βhat atTop (fun _ => β₀))
    (hderiv : ∀ n ω β, HasDerivAt (fun b => Ψ n b ω) (Ψ' n β ω) β)
    (hslope : ∀ ε > 0, ∃ δ > 0, Tendsto (fun n => μ {ω | ∃ β ∈ Metric.closedBall β₀ δ,
      ε * D n < |Ψ' n β ω + D n|}) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => D n * (βhat n ω - β₀) / B n) atTop Y (fun _ => μ) μ' := by
  set Z : ℕ → Ω → ℝ := fun n ω => Ψ n β₀ ω / B n with hZdef
  set T : ℕ → Ω → ℝ := fun n ω => D n * (βhat n ω - β₀) / B n with hTdef
  -- the pathwise linearization bound, normalized by `Bₙ`
  have hpath : ∀ n, 0 < B n → 0 < D n → ∀ {ε δ : ℝ}, 0 ≤ ε → ε < 1 → ∀ ω,
      Ψ n (βhat n ω) ω = 0 → |βhat n ω - β₀| < δ →
      (∀ β ∈ Metric.closedBall β₀ δ, |Ψ' n β ω + D n| ≤ ε * D n) →
      |T n ω - Z n ω| ≤ ε / (1 - ε) * |Z n ω| := by
    intro n hBn hDn ε δ hε0 hε1 ω h0 hδ hsl
    have h := abs_linearization_sub_le (f := fun b => Ψ n b ω) (f' := fun β => Ψ' n β ω)
      hDn hε0 hε1 (fun β _ => hderiv n ω β) hsl
      (by rw [Metric.mem_closedBall, Real.dist_eq]; exact hδ.le) h0
    simp only [hTdef, hZdef]
    rw [← sub_div, abs_div, abs_div, abs_of_pos hBn, ← mul_div_assoc]
    gcongr
  have hZm : ∀ n, AEMeasurable (Z n) μ := hZ.forall_aemeasurable
  have hTm : ∀ n, AEMeasurable (T n) μ := fun n =>
    (((hβ_meas n).sub_const β₀).const_mul (D n)).div_const (B n)
  set e : ℕ → Ω → ℝ := fun n ω => |T n ω - Z n ω| / |Z n ω| with hedef
  have hem : ∀ n, AEMeasurable (e n) μ := fun n =>
    (continuous_abs.measurable.comp_aemeasurable ((hTm n).sub (hZm n))).div
      (continuous_abs.measurable.comp_aemeasurable (hZm n))
  -- the relative linearization error tends to `0` in probability
  have he : TendstoInMeasure μ e atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro η hη
    set ε : ℝ := min (η / 4) (1 / 2) with hεdef
    have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
    have hε1 : ε ≤ 1 / 2 := min_le_right _ _
    have hεη : ε ≤ η / 4 := min_le_left _ _
    have hratio : ε / (1 - ε) < η := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    obtain ⟨δ, hδ, hbad⟩ := hslope ε hε0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_measure_not_good hδ hroot hcons hbad) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hB, hD] with n hBn hDn
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
    rintro ⟨h0, hδω, hsl⟩
    have hp := hpath n hBn hDn hε0.le (by linarith) ω h0 hδω hsl
    have hle : e n ω ≤ ε / (1 - ε) := by
      by_cases hz : Z n ω = 0
      · simp only [hedef, hz, abs_zero, div_zero]
        exact div_nonneg hε0.le (by linarith)
      · simp only [hedef]
        rw [div_le_iff₀ (abs_pos.2 hz)]
        exact hp
    rw [abs_of_nonneg (by simp only [hedef]; positivity)] at hω
    linarith
  -- so `|Z| e → 0` in probability (Slutsky), and `|T - Z| ≤ |Z| e` w.p. → 1
  have hV : TendstoInMeasure μ (fun n ω => |Z n ω| * e n ω) atTop 0 :=
    (hZ.continuous_comp continuous_abs).mul_tendstoInMeasure_zero he hem
  have hW : TendstoInMeasure μ (fun n ω => T n ω - Z n ω) atTop 0 := by
    refine tendstoInMeasure_zero_of_abs_le hV
      (G := fun n => {ω | |T n ω - Z n ω| ≤ |Z n ω| * e n ω}) ?_ (fun n ω hω => hω)
    obtain ⟨δ, hδ, hbad⟩ := hslope (1 / 2) (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_measure_not_good hδ hroot hcons hbad) (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hB, hD] with n hBn hDn
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hω ⊢
    rintro ⟨h0, hδω, hsl⟩
    apply hω
    have hp := hpath n hBn hDn (by norm_num) (by norm_num) ω h0 hδω hsl
    by_cases hz : Z n ω = 0
    · rw [hz, abs_zero, mul_zero] at hp
      rw [hz, abs_zero, zero_mul]
      exact hp
    · simp only [hedef]
      rw [mul_div_cancel₀ _ (abs_pos.2 hz).ne']
  exact tendstoInDistribution_of_tendstoInMeasure_sub T Y hZ hW hTm

/-! ### Nonlinear cluster estimating equations under bounded cluster growth -/

/-- **Standardized score CLT in distributional form.** T36's `triangular_cluster_clt` for the
cluster scores `U n i = ψ_{n,i}(β₀)` at the true parameter, restated as convergence in
distribution of `Ψₙ(β₀) / Bₙ`, `Bₙ = √(rowVariance U)`, to a standard normal `Y`. -/
theorem tendstoInDistribution_nonlinearEE_score [IsProbabilityMeasure μ] {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (ψ : ℕ → ℕ → ℝ → Ω → ℝ) (m : ℕ → ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K) {β₀ : ℝ}
    (hind : ∀ n, iIndepFun ((range n).restrict fun i => ψ n i β₀) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (ψ n i β₀))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, ψ n i β₀ ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |ψ n i β₀ ω| ≤ K * m n i)
    (hpos : ∀ᶠ n in atTop, 0 < rowVariance (fun n i => ψ n i β₀) μ n)
    (hgrowth : Tendsto (fun n => K * maxClusterSize m n /
      √(rowVariance (fun n i => ψ n i β₀) μ n)) atTop (𝓝 0))
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) μ') :
    TendstoInDistribution (fun n ω => nonlinearEE ψ n β₀ ω /
      √(rowVariance (fun n i => ψ n i β₀) μ n)) atTop Y (fun _ => μ) μ' := by
  have hclt := triangular_cluster_clt (fun n i => ψ n i β₀) m hK hind hmeas hmean hbound hpos
    hgrowth
  have hXm : ∀ n, AEMeasurable (fun ω => nonlinearEE ψ n β₀ ω /
      √(rowVariance (fun n i => ψ n i β₀) μ n)) μ := fun n =>
    ((Finset.measurable_fun_sum (range n) fun i hi => hmeas n i hi).div_const _).aemeasurable
  have hfun : ∀ n, (fun ω => ∑ i ∈ range n, ψ n i β₀ ω /
      √(rowVariance (fun n i => ψ n i β₀) μ n)) =
      fun ω => nonlinearEE ψ n β₀ ω / √(rowVariance (fun n i => ψ n i β₀) μ n) := by
    intro n; funext ω; simp [nonlinearEE, sum_div]
  rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hXm hY.aemeasurable]
  intro f
  have h := hclt f
  simp only [hfun] at h
  rw [← hY.map_eq, integral_map hY.aemeasurable f.continuous.aestronglyMeasurable] at h
  refine h.congr fun n => ?_
  exact integral_map (hXm n) f.continuous.aestronglyMeasurable

/-- **Triangular-array CLT for a nonlinear cluster estimating equation.** Rows of `n`
independent clusters contribute estimating functions `ψ_{n,i}(β)`, differentiable in `β` with
derivative `ψ'_{n,i}(β)`; `Ψₙ = ∑ᵢ ψ_{n,i}` (`nonlinearEE`). Assume

* (**scores at the truth**, T36) the cluster scores `ψ_{n,i}(β₀)` are independent within rows,
  measurable, mean zero, bounded by `K · m n i`, with positive row variance `Bₙ²` eventually and
  negligible largest cluster, `K Mₙ / Bₙ → 0`;
* (**root and consistency**) `β ↦ Ψₙ(β)` is antitone, `β̂ₙ` is a.e.-measurable and a root with
  probability tending to one, and for every `ε > 0`, `Ψₙ(β₀ - ε) > 0 > Ψₙ(β₀ + ε)` with
  probability tending to one (so `β̂ₙ → β₀` by `tendstoInMeasure_root_of_antitone`);
* (**linearization**) for a deterministic sensitivity `Dₙ > 0`, the slope
  `Ψ'ₙ = ∑ᵢ ψ'_{n,i}` is locally uniformly within `ε Dₙ` of `-Dₙ` with probability tending to one.

Then `Dₙ (β̂ₙ - β₀) / Bₙ ⇒ N(0, 1)`, i.e. `β̂ₙ` is asymptotically normal with sandwich variance
`Bₙ² / Dₙ²`. The normalization is `Dₙ / Bₙ`, not `√n`. -/
theorem triangular_nonlinearEE_clt [IsProbabilityMeasure μ] {Ω' : Type*}
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (ψ ψ' : ℕ → ℕ → ℝ → Ω → ℝ) (m : ℕ → ℕ → ℕ) {K : ℝ} (hK : 0 ≤ K) {β₀ : ℝ}
    (hind : ∀ n, iIndepFun ((range n).restrict fun i => ψ n i β₀) μ)
    (hmeas : ∀ n, ∀ i ∈ range n, Measurable (ψ n i β₀))
    (hmean : ∀ n, ∀ i ∈ range n, ∫ ω, ψ n i β₀ ω ∂μ = 0)
    (hbound : ∀ n, ∀ i ∈ range n, ∀ ω, |ψ n i β₀ ω| ≤ K * m n i)
    (hpos : ∀ᶠ n in atTop, 0 < rowVariance (fun n i => ψ n i β₀) μ n)
    (hgrowth : Tendsto (fun n => K * maxClusterSize m n /
      √(rowVariance (fun n i => ψ n i β₀) μ n)) atTop (𝓝 0))
    {βhat : ℕ → Ω → ℝ} (hβ_meas : ∀ n, AEMeasurable (βhat n) μ)
    (hroot : Tendsto (fun n => μ {ω | nonlinearEE ψ n (βhat n ω) ω ≠ 0}) atTop (𝓝 0))
    (hanti : ∀ n ω, Antitone fun β => nonlinearEE ψ n β ω)
    (hleft : ∀ ε > 0, Tendsto (fun n => μ {ω | nonlinearEE ψ n (β₀ - ε) ω ≤ 0}) atTop (𝓝 0))
    (hright : ∀ ε > 0, Tendsto (fun n => μ {ω | 0 ≤ nonlinearEE ψ n (β₀ + ε) ω}) atTop (𝓝 0))
    (hderiv : ∀ n i ω β, HasDerivAt (fun b => ψ n i b ω) (ψ' n i β ω) β)
    {D : ℕ → ℝ} (hD : ∀ᶠ n in atTop, 0 < D n)
    (hslope : ∀ ε > 0, ∃ δ > 0, Tendsto (fun n => μ {ω | ∃ β ∈ Metric.closedBall β₀ δ,
      ε * D n < |nonlinearEE ψ' n β ω + D n|}) atTop (𝓝 0))
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) μ') :
    TendstoInDistribution (fun n ω => D n * (βhat n ω - β₀) /
      √(rowVariance (fun n i => ψ n i β₀) μ n)) atTop Y (fun _ => μ) μ' := by
  refine tendstoInDistribution_of_linearization (Ψ := nonlinearEE ψ) (Ψ' := nonlinearEE ψ')
    (tendstoInDistribution_nonlinearEE_score ψ m hK hind hmeas hmean hbound hpos hgrowth hY)
    (hpos.mono fun n hn => Real.sqrt_pos.2 hn) hD hβ_meas hroot
    (tendstoInMeasure_root_of_antitone hanti hroot hleft hright) (fun n ω β => ?_) hslope
  simpa [nonlinearEE] using HasDerivAt.fun_sum (u := range n) fun i _ => hderiv n i ω β

end ProbabilityTheory.GEE.NonlinearTriangular
