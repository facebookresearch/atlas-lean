/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.HermitianTraceExp
public import MathlibExt.Probability.MatrixLaplaceTransform
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Matrix concentration inequalities (wanted)

The matrix Laplace transform method (`MathlibExt.Probability.MatrixLaplaceTransform`) reduces
tail bounds for the extreme eigenvalues of a random Hermitian matrix `Y` to bounds on the trace
mgf `E tr e^{θY}`. For a sum of independent random matrices, Lieb's concavity theorem turns the
trace mgf into a sum of matrix cumulant generating functions, and bounds on each summand's cgf
give matrix analogues of the Chernoff and Bernstein inequalities. The chain, as taught in
J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, Found. Trends Mach. Learn.
8 (2015), arXiv:1501.01571, is:

* Lieb's concavity theorem (Theorem 3.4.1; E. H. Lieb, *Convex trace functions and the
  Wigner–Yanase–Dyson conjecture*, Adv. Math. 11 (1973), Theorem 6), recorded as a
  matrix-analysis result in `MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted`;
* subadditivity of matrix cgfs (Lemma 3.5.1);
* matrix Gaussian series (Theorem 4.6.1);
* the matrix Chernoff inequality (Theorem 5.1.1);
* the matrix Bernstein inequality, Hermitian case (Theorem 6.6.1);
* the matrix Hoeffding inequality (Tropp, *User-friendly tail bounds for sums of random
  matrices*, Found. Comput. Math. 12 (2012), Theorem 1.3).

The proofs are deferred. Expectations of random matrices are taken entrywise
(`MathlibExt.Probability.MatrixLaplaceTransform.expect`), and integrability hypotheses are
explicit so that the Bochner integrals are not the junk value `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.MatrixLaplaceTransform
open scoped ComplexOrder

namespace MathlibExt.Probability.MatrixConcentrationWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Subadditivity of matrix cumulant generating functions** (Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Lemma 3.5.1, display (3.5.1); Tropp,
*User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Lemma 3.4). For independent random Hermitian matrices `X₀, …, X_{N-1}` with integrable
`e^{θ X_k}` and integrable `tr e^{θ ∑ X_k}`,
`E tr exp(∑ₖ θ X_k) ≤ tr exp(∑ₖ log E e^{θ X_k})`. -/
theorem_wanted integral_trace_exp_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) (θ : ℝ)
    (hexp : ∀ k i j, Integrable (fun ω => NormedSpace.exp (θ • X k ω) i j) μ)
    (hsum : Integrable (fun ω => RCLike.re (NormedSpace.exp (θ • ∑ k, X k ω)).trace) μ) :
    ∫ ω, RCLike.re (NormedSpace.exp (θ • ∑ k, X k ω)).trace ∂μ ≤
      RCLike.re (NormedSpace.exp
        (∑ k, cfc Real.log (expect μ fun ω => NormedSpace.exp (θ • X k ω)))).trace

/-- **Matrix Chernoff inequality, tail bounds** (Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Theorem 5.1.1, displays (5.1.5) and (5.1.6);
Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Theorem 1.1). Let `X₀, …, X_{N-1}` be independent random Hermitian `d × d` matrices with
`0 ≤ λmin(X_k)` and `λmax(X_k) ≤ L`, `L > 0`, let `Y = ∑ₖ X_k`, and let
`μmin = λmin(E Y)`, `μmax = λmax(E Y)`. Then for `ε ≥ 0`,
`P{λmax(Y) ≥ (1 + ε) μmax} ≤ d · [e^ε / (1 + ε)^{1+ε}]^{μmax / L}`, and for `0 ≤ ε < 1`,
`P{λmin(Y) ≤ (1 - ε) μmin} ≤ d · [e^{-ε} / (1 - ε)^{1-ε}]^{μmin / L}`. -/
theorem_wanted matrix_chernoff [Nonempty n] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) {L : ℝ} (hL : 0 < L)
    (hlow : ∀ k ω, 0 ≤ (hX k ω).lambdaMin) (hup : ∀ k ω, (hX k ω).lambdaMax ≤ L)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian)
    (hEY : (expect μ fun ω => ∑ k, X k ω).IsHermitian) :
    (∀ ε : ℝ, 0 ≤ ε →
      μ.real {ω | (1 + ε) * hEY.lambdaMax ≤ (hY ω).lambdaMax} ≤
        Fintype.card n * (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (hEY.lambdaMax / L)) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      μ.real {ω | (hY ω).lambdaMin ≤ (1 - ε) * hEY.lambdaMin} ≤
        Fintype.card n * (Real.exp (-ε) / (1 - ε) ^ (1 - ε)) ^ (hEY.lambdaMin / L))

/-- **Matrix Bernstein inequality, Hermitian case** (Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Theorem 6.6.1, display (6.6.3); Tropp,
*User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Theorem 1.4). Let `X₀, …, X_{N-1}` be independent, centered random Hermitian `d × d` matrices with
`λmax(X_k) ≤ L`, let `Y = ∑ₖ X_k` and let `v = ‖∑ₖ E X_k²‖`, which is `λmax(∑ₖ E X_k²)` since
that matrix is positive semidefinite. Then for all `t ≥ 0`,
`P{λmax(Y) ≥ t} ≤ d · exp(-(t²/2) / (v + L t / 3))`. -/
theorem_wanted matrix_bernstein [Nonempty n] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) {L : ℝ} (hL : 0 ≤ L)
    (hup : ∀ k ω, (hX k ω).lambdaMax ≤ L)
    (hint : ∀ k i j, Integrable (fun ω => X k ω i j) μ)
    (hint2 : ∀ k i j, Integrable (fun ω => (X k ω * X k ω) i j) μ)
    (hcenter : ∀ k, expect μ (X k) = 0)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian)
    (hV : (∑ k, expect μ fun ω => X k ω * X k ω).IsHermitian) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (hY ω).lambdaMax} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (hV.lambdaMax + L * t / 3))

/-- **Matrix Gaussian series, Hermitian case** (Tropp, *An Introduction to Matrix Concentration
Inequalities*, arXiv:1501.01571, Theorem 4.6.1, displays (4.6.2) and (4.6.3); Tropp,
*User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Theorem 1.2). Let `A₀, …, A_{N-1}` be fixed Hermitian `d × d` matrices, `γ₀, …, γ_{N-1}`
independent standard normal variables, `Y = ∑ₖ γₖ Aₖ` and `v = ‖∑ₖ Aₖ²‖ = λmax(∑ₖ Aₖ²)`. Then
`E λmax(Y) ≤ (2 v log d)^{1/2}` and, for all `t ≥ 0`, `P{λmax(Y) ≥ t} ≤ d e^{-t²/(2v)}`. -/
theorem_wanted matrix_gaussian_series [Nonempty n] {N : ℕ} {A : Fin N → Matrix n n ℂ}
    (hA : ∀ k, (A k).IsHermitian) (hY : ∀ ω, (gaussianSeries A ω).IsHermitian)
    (hV : (∑ k, A k * A k).IsHermitian) :
    ∫ ω, (hY ω).lambdaMax ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
        Real.sqrt (2 * hV.lambdaMax * Real.log (Fintype.card n)) ∧
      ∀ t : ℝ, 0 ≤ t →
        (Measure.pi fun _ : Fin N => gaussianReal 0 1).real {ω | t ≤ (hY ω).lambdaMax} ≤
          Fintype.card n * Real.exp (-t ^ 2 / (2 * hV.lambdaMax))

/-- **Matrix Hoeffding inequality** (Tropp, *User-friendly tail bounds for sums of random
matrices*, Found. Comput. Math. 12 (2012), Theorem 1.3). Let `X₀, …, X_{N-1}` be independent,
centered random Hermitian `d × d` matrices and `A₀, …, A_{N-1}` fixed Hermitian matrices with
`X_k² ⪯ A_k²` (that is, `A_k² - X_k²` positive semidefinite) for every outcome. Let
`σ² = ‖∑ₖ Aₖ²‖ = λmax(∑ₖ Aₖ²)`. Then for all `t ≥ 0`,
`P{λmax(∑ₖ X_k) ≥ t} ≤ d e^{-t²/(8σ²)}`. -/
theorem_wanted matrix_hoeffding [Nonempty n] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) {A : Fin N → Matrix n n ℂ} (hA : ∀ k, (A k).IsHermitian)
    (hdom : ∀ k ω, (A k * A k - X k ω * X k ω).PosSemidef)
    (hint : ∀ k i j, Integrable (fun ω => X k ω i j) μ) (hcenter : ∀ k, expect μ (X k) = 0)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian) (hσ : (∑ k, A k * A k).IsHermitian)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (hY ω).lambdaMax} ≤
      Fintype.card n * Real.exp (-t ^ 2 / (8 * hσ.lambdaMax))

end MathlibExt.Probability.MatrixConcentrationWanted
