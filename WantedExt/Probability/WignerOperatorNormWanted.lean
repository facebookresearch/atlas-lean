/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.IdentDistrib
public import MathlibExt.Probability.WignerOperatorNorm
public import MathlibExt.Probability.WignerOperatorNormOpNormConcentrationMedian

/-!
# The operator norm of a random matrix

Three standard facts about the size of the largest eigenvalue of a random matrix with
independent entries, in the setting of Tao's *Topics in Random Matrix Theory*, §2.3:

* **Upper tail** (Corollary 2.3.6): for a real symmetric matrix whose upper-triangular entries
  are independent, mean zero and bounded by `1`, `P(‖M‖ > A√n) ≤ C exp(-cAn)` for `A ≥ C`; so
  `‖M‖ = O(√n)` with overwhelming probability.
* **Concentration** (Proposition 2.3.10): for an `n × n` matrix with independent, mean-zero
  entries bounded by `1`, the operator norm concentrates around a median with `O(1)` Gaussian
  fluctuations, uniformly in `n`; it follows from Talagrand's inequality because `‖·‖` is convex
  and `1`-Lipschitz for the Frobenius norm. This statement, `opNorm_concentration_median`, is in
  `MathlibExt.Probability.WignerOperatorNormOpNormConcentrationMedian`.
* **Bai–Yin** (Theorem 2.3.24): for a Wigner matrix with i.i.d. entries of mean `0`, variance
  `1` and finite fourth moment, almost surely `limsup ‖M_n‖ / √n ≤ 2`. Combined with the lower
  bound that the semicircle law supplies (the semicircle distribution charges every
  neighbourhood of `±2`), `‖M_n‖ / √n → 2` almost surely (Bai and Yin 1988).

The Wigner matrices `wignerMatrix X n ω` are the top-left `n × n` blocks of one infinite real
symmetric array, as in `WignerSemicircleWanted`. The operator norm is that of the matrix acting
on Euclidean space, `‖Matrix.toEuclideanCLM M‖`. Tao's Corollary 2.3.6 and Proposition 2.3.10
allow complex entries; the statements here are the real case. The almost-sure statements use
the `ε`-form of `limsup ≤ 2` because `Filter.limsup` of an unbounded real sequence is a junk
value.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  Corollary 2.3.6, Proposition 2.3.10, Theorem 2.3.24, and the discussion after Theorem 2.4.2.
* Z. D. Bai and Y. Q. Yin, *Necessary and sufficient conditions for almost sure convergence of
  the largest eigenvalue of a Wigner matrix*, Ann. Probab. 16 (1988), no. 4, 1729–1741.
-/

@[expose] public section

namespace MathlibExt.Probability.WignerOperatorNormWanted

open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology
open MathlibExt.Analysis.WignerSemicircleWanted.Analysis.WignerSemicircleProblem (wignerMatrix)

/-- **Strong Bai–Yin theorem, upper bound** (Tao, *Topics in Random Matrix Theory*,
Theorem 2.3.24; Bai and Yin 1988). Let the entries `X i j` (`i ≤ j`) of a real symmetric array
be i.i.d. with mean `0`, variance `1` and finite fourth moment. Then almost surely, for every
`ε > 0`, the `n × n` Wigner matrices satisfy `‖M_n‖ ≤ (2 + ε)√n` for all large `n`, that is
`limsup ‖M_n‖ / √n ≤ 2`. -/
public theorem_wanted wigner_opNorm_le_two_add
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (_hX_meas : ∀ i j, Measurable (X i j))
    (_hX_indep : iIndepFun
      (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) μ)
    (_hX_iid : ∀ i j i' j', i ≤ j → i' ≤ j' →
      ProbabilityTheory.IdentDistrib (X i j) (X i' j') μ μ)
    (_hX_int : ∀ i j, i ≤ j → Integrable (X i j) μ)
    (_hX_sq_int : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω) ^ 2) μ)
    (_hX_four_int : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω) ^ 4) μ)
    (_hX_mean : ∀ i j, i ≤ j → ∫ ω, X i j ω ∂μ = 0)
    (_hX_var : ∀ i j, i ≤ j → ∫ ω, (X i j ω) ^ 2 ∂μ = 1) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (wignerMatrix X n ω)‖ ≤ (2 + ε) * √n

/-- **Bai–Yin theorem** (Bai and Yin 1988; Tao, *Topics in Random Matrix Theory*,
Theorem 2.3.24 with the lower bound from the semicircular law, Theorem 2.4.2). Under the
hypotheses of `wigner_opNorm_le_two_add`, almost surely `‖M_n‖ / √n → 2`. -/
public theorem_wanted tendsto_wigner_opNorm_div_sqrt
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (_hX_meas : ∀ i j, Measurable (X i j))
    (_hX_indep : iIndepFun
      (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) μ)
    (_hX_iid : ∀ i j i' j', i ≤ j → i' ≤ j' →
      ProbabilityTheory.IdentDistrib (X i j) (X i' j') μ μ)
    (_hX_int : ∀ i j, i ≤ j → Integrable (X i j) μ)
    (_hX_sq_int : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω) ^ 2) μ)
    (_hX_four_int : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω) ^ 4) μ)
    (_hX_mean : ∀ i j, i ≤ j → ∫ ω, X i j ω ∂μ = 0)
    (_hX_var : ∀ i j, i ≤ j → ∫ ω, (X i j ω) ^ 2 ∂μ = 1) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (wignerMatrix X n ω)‖ / √n)
      atTop (𝓝 2)

end MathlibExt.Probability.WignerOperatorNormWanted
