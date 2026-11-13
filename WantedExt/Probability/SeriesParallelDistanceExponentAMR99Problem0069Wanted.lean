/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Distance exponent of the random series-parallel graph at criticality (Benjamini, Question 9.6)

Benjamini, Euclidean vs. graph metric, Question 9.6: in the Hambly-Jordan random series-parallel
graph (start from one edge; at each stage every edge is replaced independently by two edges in
series with probability `p` or by two parallel edges with probability `1 - p`) let `Δ_n` be the
distance between the two extremal points and `E[Δ_n] ≈ e^{n δ(p) + o(n)}`. What is the shape of `p ∈
[1/2, 1] ↦ δ(p)`? In particular, do we have `δ(1/2) = 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Bernoulli

@[expose] public section

namespace MathlibExt.Probability.SeriesParallelDistanceExponentAMR99Problem0069Wanted

/-!
Source: I. Benjamini, Euclidean vs. graph metric, in Erdős Centennial (Bolyai Soc. Math. Stud. 25,
Springer 2013), Question 9.6, PDF p. 18. UnsolvedMath record UM-10000069 (`AMR-099-0069`), dataset
ulamai/UnsolvedMath v1.8.0.

The law of the distance is built from the recursive distributional equation of the source and of
Chen-Derrida-Duquesne-Shi (1.1), as a measure on `ℕ` (Bernoulli step `E_n = 1`, probability `p`, is
the series case); `expectedDistance p n` is `E[D_n(p)]`. The precise part of the question is
answered in the strongest form the paper states: the exponent exists for every `p ∈ [0, 1]` ((1.2)),
vanishes at `p = 1/2` (abstract), and `α(1/2 + ε) / √ε → π / √6` (Theorem 1). The open-ended part,
the shape of `δ` on `[1/2, 1]`, is not formalized.
-/

open Filter Topology

/-- The law of `D_n(p)`, the graph distance between the two extremal vertices of the Hambly-Jordan
random series-parallel graph after `n` steps (every edge is replaced independently by two edges in
series with probability `p`, by two parallel edges otherwise): `D_0 = 1` and
`D_{n+1} = (D_n + D_n') E_n + min (D_n, D_n') (1 - E_n)` for independent copies `D_n, D_n'` and an
independent Bernoulli(`p`) variable `E_n` (Chen-Derrida-Duquesne-Shi, equation (1.1)); `E_n = 1`
(probability `p`) is the series case. The parameter is clamped to `[0, 1]`. -/
noncomputable def distanceLaw (p : ℝ) : ℕ → MeasureTheory.Measure ℕ
  | 0 => MeasureTheory.Measure.dirac 1
  | n + 1 =>
    (ProbabilityTheory.bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)).bind fun e =>
      (distanceLaw p n).bind fun a =>
        (distanceLaw p n).map fun b => if e then a + b else min a b

/-- The expectation `E[D_n(p)]` of the extremal distance after `n` steps. -/
noncomputable def expectedDistance (p : ℝ) (n : ℕ) : ℝ :=
  (∫⁻ k, (k : ENNReal) ∂distanceLaw p n).toReal

/-- Benjamini's Question 9.6 (Euclidean vs. graph metric), precise part, in the form resolved by
Chen-Derrida-Duquesne-Shi: the exponent `α(p) = lim_n (1/n) log E[D_n(p)]` exists for every
`p ∈ [0, 1]`, it vanishes at `p = 1/2` (so `δ(1/2) = 0`), and `α(1/2 + ε) / √ε → π / √6` as
`ε → 0+`. -/
def seriesParallelDistanceExponent : Prop :=
  ∃ α : ℝ → ℝ,
    (∀ p ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => Real.log (expectedDistance p n) / n) atTop (𝓝 (α p))) ∧
    α (1 / 2) = 0 ∧
    Tendsto (fun ε : ℝ => α (1 / 2 + ε) / Real.sqrt ε) (𝓝[>] 0) (𝓝 (Real.pi / Real.sqrt 6))

/--
Resolved true: the exponent `α(p) = lim_n (1/n) log E[D_n(p)]` exists for every `p ∈ [0, 1]`,
`α(1/2) = 0`, so `δ(1/2) = 0` as Benjamini asked, and `α(1/2 + ε)` behaves like `π √(ε/6)` as `ε →
0+`. Source: I. Benjamini, Euclidean vs. graph metric, in Erdős Centennial (Bolyai Soc. Math. Stud.
25, Springer 2013), Question 9.6, PDF p. 18; resolution: X. Chen, B. Derrida, T. Duquesne and Z.
Shi, The distance on the slightly supercritical random series-parallel graph, Adv. Appl. Probab.
(2025, open access), doi:10.1017/apr.2025.10023, abstract: 'It is known that Dn(p) possesses a phase
transition at p = pc := 1/2; more precisely, (1/n) log E[Dn(p)] → α(p) when n → ∞, with α(p) > 0 for
p > pc and α(p) = 0 for p ≤ pc'; equation (1.1) (the recursion), (1.2) (the limit exists for every p
∈ [0, 1], by Fekete's lemma) and Theorem 1: lim_{ε→0+} α(1/2 + ε)/√ε = π/√6,
https://doi.org/10.1017/apr.2025.10023.
-/
public theorem_wanted seriesParallelDistanceExponent_holds : seriesParallelDistanceExponent

end MathlibExt.Probability.SeriesParallelDistanceExponentAMR99Problem0069Wanted
