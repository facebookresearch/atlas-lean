/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Asymptotic efficiency: Hájek's convolution theorem and adaptive estimation

Two results of the asymptotic theory of efficient estimation, as P. J. Bickel reviews it in "On
adaptive estimation" (1980 Wald Memorial Lectures), *Ann. Statist.* 10 (1982) 647–671,
Section 2.

* `hajek_convolution`: in a locally asymptotically normal (LAN) sequence of experiments with a
  one-dimensional local parameter `h` and information `I > 0`, the limit law `L` of every
  regular estimator sequence is a convolution `N(0, I⁻¹) ∗ M`; so `N(0, I⁻¹)` is the best
  possible limit (J. Hájek, "A characterization of limiting distributions of regular
  estimates", *Z. Wahrscheinlichkeitstheorie verw. Geb.* 14 (1970) 323–330).
* `exists_adaptive_location_estimator`: in the semiparametric model of a centre of symmetry
  with unknown symmetric shape `G`, the information bound `I(G)⁻¹` of the model with `G` known
  is attained without knowing `G` (Bickel 1982, Example 1 and Theorem 2.2, due to Beran (1974)
  and Stone (1975)).

LAN is stated through log-likelihood ratios `log dP_{n,h}/dP_{n,0}` (Mathlib's `llr`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MathlibExt.Probability.Statistics.EfficiencyWanted

/-- **Hájek's convolution theorem** (J. Hájek, *Z. Wahrscheinlichkeitstheorie verw. Geb.* 14
(1970) 323–330; here with a one-dimensional parameter). For each `n` let
`(P n h)_{h ∈ ℝ}` be a family of probability measures on `Ω n` (the local experiments
`P_{θ + h/√n}^n`), locally asymptotically normal at `0` with central sequence `Δ n` and
information `I > 0`: `Δ n ⇝ N(0, I)` under `P n 0`, and for every `h`,
`log dP_{n,h}/dP_{n,0} - (h Δ_n - h² I / 2) → 0` in `P n 0`-probability. Let `T n` be
*regular* estimators of the local parameter: for every `h`, the law of `T n - h` under `P n h`
converges weakly to one and the same law `L`. Then `L = N(0, I⁻¹) ∗ M` for some probability
measure `M`. -/
theorem_wanted hajek_convolution {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ℝ → ProbabilityMeasure (Ω n)) (Δ : ∀ n, Ω n → ℝ) (hΔ : ∀ n, Measurable (Δ n))
    {I : ℝ≥0} (hI : 0 < I)
    (hΔlim : Tendsto (fun n => (P n 0).map (Δ n)) atTop
      (𝓝 ⟨gaussianReal 0 I, inferInstance⟩))
    (hLAN : ∀ h ε : ℝ, 0 < ε → Tendsto (fun n => (P n 0 : Measure (Ω n))
      {ω | ε ≤ |llr (P n h : Measure (Ω n)) (P n 0 : Measure (Ω n)) ω -
        (h * Δ n ω - h ^ 2 * I / 2)|}) atTop (𝓝 0))
    (T : ∀ n, Ω n → ℝ) (hT : ∀ n, Measurable (T n)) (L : ProbabilityMeasure ℝ)
    (hreg : ∀ h : ℝ, Tendsto (fun n => (P n h).map (fun ω => T n ω - h)) atTop (𝓝 L)) :
    ∃ M : ProbabilityMeasure ℝ, (L : Measure ℝ) = gaussianReal 0 I⁻¹ ∗ (M : Measure ℝ)

/-- **Adaptive estimation of a centre of symmetry** (P. J. Bickel, "On adaptive estimation",
*Ann. Statist.* 10 (1982), Theorem 2.2 in Example 1, results of R. Beran (1974) and C. J. Stone
(1975)). There are measurable, translation and scale equivariant estimators `T n` of a location
parameter such that, for every law `G` on `ℝ` that is symmetric about `0` and has an absolutely
continuous density `g` with finite Fisher information `I(G) = ∫ g'² / g`, the law of
`√n T_n(X₁, …, X_n)` for i.i.d. `X_i ∼ G` converges weakly to `N(0, I(G)⁻¹)`. By equivariance
the same holds at every location `θ`; `I(G)⁻¹` is the Cramér–Rao and Hájek bound of the
parametric model in which `G` is known, so the estimators are adaptive. Estimators act on
samples of size `n ≥ 1`: the equivariance clauses are required for `0 < n` only (for `n = 0` the
translation clause would force `T 0 x = T 0 x + c`). -/
theorem_wanted exists_adaptive_location_estimator :
    ∃ T : ∀ n : ℕ, (Fin n → ℝ) → ℝ, (∀ n, Measurable (T n)) ∧
      (∀ n, 0 < n → ∀ (x : Fin n → ℝ) (c : ℝ), T n (fun i => x i + c) = T n x + c) ∧
      (∀ n, 0 < n → ∀ (x : Fin n → ℝ) (a : ℝ), 0 < a → T n (fun i => a * x i) = a * T n x) ∧
      ∀ (G : ProbabilityMeasure ℝ) (g : ℝ → ℝ),
        (G : Measure ℝ).map (fun x => -x) = G →
        (∀ x, 0 ≤ g x) → (G : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (g x)) →
        (∀ a b, AbsolutelyContinuousOnInterval g a b) →
        Integrable (fun x => deriv g x ^ 2 / g x) →
        ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ =>
          ∫ x, f (Real.sqrt n * T n x) ∂(Measure.pi fun _ : Fin n => (G : Measure ℝ)))
          atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 (∫ x, deriv g x ^ 2 / g x)⁻¹.toNNReal)))

/-- The equivariance clauses of `exists_adaptive_location_estimator` are satisfiable: the sample
mean is translation and scale equivariant on nonempty samples. -/
example : ∀ n, 0 < n → ∀ (x : Fin n → ℝ) (c : ℝ),
    (∑ i, (x i + c)) / n = (∑ i, x i) / n + c := by
  intro n hn x c
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-- Scale equivariance of the sample mean. -/
example : ∀ n, 0 < n → ∀ (x : Fin n → ℝ) (a : ℝ), 0 < a →
    (∑ i, a * x i) / n = a * ((∑ i, x i) / n) := by
  intro n _ x a _
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Edge case: on samples of size `0` no map is translation equivariant, which is why the
clauses above are restricted to `0 < n`. -/
example : ¬ ∃ T : (Fin 0 → ℝ) → ℝ, ∀ (x : Fin 0 → ℝ) (c : ℝ),
    T (fun i => x i + c) = T x + c := by
  rintro ⟨T, hT⟩
  have h := hT Fin.elim0 1
  have hx : (fun i : Fin 0 => (Fin.elim0 i : ℝ) + 1) = Fin.elim0 := funext fun i => i.elim0
  rw [hx] at h
  linarith

end MathlibExt.Probability.Statistics.EfficiencyWanted
