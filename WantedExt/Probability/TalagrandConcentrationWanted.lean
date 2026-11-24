/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Talagrand's concentration inequality

Let `X₁, …, Xₙ` be independent random variables bounded by `K` and let `F : ℝⁿ → ℝ` be convex
and `1`-Lipschitz for the Euclidean metric. Then `F(X)` concentrates around its median, and
around its mean, at scale `K` with Gaussian tails:
`P(|F(X) - M F(X)| ≥ λK) ≤ C exp(-cλ²)` and `P(|F(X) - 𝔼 F(X)| ≥ λK) ≤ C exp(-cλ²)` for all
`λ > 0`, with absolute constants `C, c > 0` that depend on neither `n`, `K`, `F` nor the laws of
the `Xᵢ`. Unlike McDiarmid's inequality, the deviation scale `K` does not grow with `n`. This is
the tool that makes the operator norm and other convex spectral statistics of random matrices
concentrate (Tao, *Topics in Random Matrix Theory*, Proposition 2.3.10).

Tao states the theorem for complex variables and `F : ℂⁿ → ℝ`, identifying `ℂⁿ` with `ℝ²ⁿ`. The
statements below are the real case, which follows from the complex one by composing `F` with
`z ↦ Re z`. "For any `λ`" in the source means `λ > 0`: for `λ < 0` the event is certain while
the bound tends to `0`.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Theorem 2.1.13, inequalities `(2.18)` (median) and `(2.19)` (mean).
* M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*,
  Publ. Math. IHÉS 81 (1995), 73–205.
-/

@[expose] public section

namespace MathlibExt.Probability.TalagrandConcentrationWanted

open MeasureTheory ProbabilityTheory Real

/-- **Talagrand's concentration inequality around a median** (Tao, *Topics in Random Matrix
Theory*, Theorem 2.1.13, `(2.18)`, real case). There are absolute constants `C, c > 0` such
that: if `X₁, …, Xₙ` are independent real random variables with `|Xᵢ| ≤ K` (`K > 0`), `F` is a
convex `1`-Lipschitz function on Euclidean `ℝⁿ`, and `m` is a median of `F(X)`, then
`P(|F(X) - m| ≥ λK) ≤ C exp(-cλ²)` for every `λ > 0`. -/
public theorem_wanted talagrand_concentration_median :
    ∃ C > 0, ∃ c > 0, ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (n : ℕ) (X : Fin n → Ω → ℝ) (K : ℝ), 0 < K →
      (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i ω, |X i ω| ≤ K) →
      ∀ F : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ Set.univ F → LipschitzWith 1 F →
      ∀ m : ℝ, 1 / 2 ≤ P.real {ω | F (WithLp.toLp 2 fun i => X i ω) ≤ m} →
        1 / 2 ≤ P.real {ω | m ≤ F (WithLp.toLp 2 fun i => X i ω)} →
      ∀ t : ℝ, 0 < t →
        P.real {ω | t * K ≤ |F (WithLp.toLp 2 fun i => X i ω) - m|} ≤ C * exp (-c * t ^ 2)

/-- **Talagrand's concentration inequality around the mean** (Tao, *Topics in Random Matrix
Theory*, Theorem 2.1.13, `(2.19)`, real case). Under the hypotheses of
`talagrand_concentration_median`, `P(|F(X) - 𝔼 F(X)| ≥ λK) ≤ C exp(-cλ²)` for every `λ > 0`.
(`F(X)` is bounded and measurable, so its expectation is a genuine integral.) -/
public theorem_wanted talagrand_concentration_mean :
    ∃ C > 0, ∃ c > 0, ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (n : ℕ) (X : Fin n → Ω → ℝ) (K : ℝ), 0 < K →
      (∀ i, Measurable (X i)) → iIndepFun X P → (∀ i ω, |X i ω| ≤ K) →
      ∀ F : EuclideanSpace ℝ (Fin n) → ℝ, ConvexOn ℝ Set.univ F → LipschitzWith 1 F →
      ∀ t : ℝ, 0 < t →
        P.real {ω | t * K ≤ |F (WithLp.toLp 2 fun i => X i ω) -
          ∫ ω', F (WithLp.toLp 2 fun i => X i ω') ∂P|} ≤ C * exp (-c * t ^ 2)

end MathlibExt.Probability.TalagrandConcentrationWanted
