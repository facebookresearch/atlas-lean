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
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import MathlibExt.Probability.Statistics.HajekConvolution

/-!
# Asymptotic efficiency: adaptive estimation

A result of the asymptotic theory of efficient estimation, as P. J. Bickel reviews it in "On
adaptive estimation" (1980 Wald Memorial Lectures), *Ann. Statist.* 10 (1982) 647–671,
Section 2.

* `exists_adaptive_location_estimator`: in the semiparametric model of a centre of symmetry
  with unknown symmetric shape `G`, the information bound `I(G)⁻¹` of the model with `G` known
  is attained without knowing `G` (Bickel 1982, Example 1 and Theorem 2.2, due to Beran (1974)
  and Stone (1975)).

Hájek's convolution theorem `hajek_convolution` is re-exported here, under its original name,
from `MathlibExt.Probability.Statistics.HajekConvolution`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MathlibExt.Probability.Statistics.EfficiencyWanted

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
