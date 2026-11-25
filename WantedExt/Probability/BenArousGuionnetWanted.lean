/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.LDPSpeed
public import MathlibExt.Probability.SampleEmpiricalMeasure
public import MathlibExt.Probability.Distributions.Semicircle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Large deviations for the empirical spectral measure: Ben Arous–Guionnet (wanted)

For `β > 0`, the *Gaussian `β`-ensemble* is the law on `ℝ^N` with density proportional to
`∏_{i<j} |λᵢ - λⱼ|^β exp(-(β N / 4) ∑ λᵢ²)`; for `β = 1, 2, 4` it is the joint law of the
eigenvalues of the GOE, GUE and GSE matrices normalised so that their spectra fill `[-2, 2]`. Ben
Arous and Guionnet proved that the empirical spectral measure `L_N = N⁻¹ ∑ δ_{λᵢ}` satisfies a large
deviation principle at speed `N²` in the space of probability measures with the weak topology, with
the good rate function
`I_β(μ) = (β/4) ∫ x² dμ - (β/2) Σ(μ) - 3β/8`, `Σ(μ) = ∫∫ log |x - y| dμ(x) dμ(y)`
(Voiculescu's free entropy), whose unique zero is the semicircle law. Since a large deviation
principle with a unique zero implies almost sure convergence, this recovers Wigner's theorem for
these ensembles.

## Encoding of the rate function

`I_β(μ) = (β/2) ∫∫ f dμ dμ - 3β/8` with `f(x, y) = log |x - y|⁻¹ + (x² + y²)/4`
(Guionnet's survey, proof of Theorem 3.1), and `f ≥ c₀ := 1/2 - log 2` because
`(x² + y²)/4 ≥ (x - y)²/8` and `-log d + d²/8 ≥ 1/2 - log 2` for `d > 0`. With the nonnegative
kernel `g = f - c₀` (set to `∞` on the diagonal, where `log |x - y|⁻¹ = +∞`),
`I_β(μ) = (β/2) ∫∫ g dμ dμ - (β/8 + (β/2) log 2)`. This is written in `ℝ≥0∞`: the truncated
subtraction loses nothing because `I_β ≥ 0`, and `I_β(μ) = ∞` exactly when `∫∫ g = ∞`, for instance
when `μ` has an atom or infinite second moment.

## Source

* A. Guionnet, "Large deviations and stochastic calculus for large random matrices", *Probability
  Surveys* 1 (2004), 72–172, arXiv:math/0409277, Theorem 3.1 (for `β = 1, 2, 4`), with the large
  deviation principle at speed `a_N` of Definition 2.1;
* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, Theorem 2.6.1 and Lemma 2.6.2 (for every `β > 0` and potentials `V`,
  here `V(x) = βx²/4`);
* originally G. Ben Arous and A. Guionnet, "Large deviations for Wigner's law and Voiculescu's
  non-commutative entropy", *Probab. Theory Related Fields* 108 (1997), 517–542, Theorem 5.2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open MathlibExt.Probability.LargeDeviationPrinciple MathlibExt.Probability.SampleEmpiricalMeasure

namespace MathlibExt.Probability.BenArousGuionnetWanted

/-- The unnormalised density `∏_{i<j} |λᵢ - λⱼ|^β exp(-(β N / 4) ∑ λᵢ²)` of the Gaussian
`β`-ensemble on `ℝ^N` (Guionnet's survey, the law `Q^N_β` before Theorem 3.1). -/
noncomputable def betaEnsembleWeight (β : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), |x i - x j| ^ β) *
    Real.exp (-(β * N / 4) * ∑ i, x i ^ 2))

/-- **The Gaussian `β`-ensemble**: for `β > 0`, the probability law on `ℝ^N` with density
proportional to `∏_{i<j} |λᵢ - λⱼ|^β exp(-(β N / 4) ∑ λᵢ²)`. For `β = 1, 2, 4` it is the joint law
of the eigenvalues of the Gaussian orthogonal, unitary and symplectic ensembles (Guionnet,
*Probability Surveys* 1 (2004), formula (3.1.1) and the law `Q^N_β`). The condition `β > 0`
makes the normalising integral finite and positive: for `β ≤ 0` and `N ≥ 1` it is infinite, and
the normalised measure would be zero. -/
noncomputable def betaEnsemble (β : ℝ) (_hβ : 0 < β) (N : ℕ) : Measure (Fin N → ℝ) :=
  (∫⁻ x, betaEnsembleWeight β N x)⁻¹ • volume.withDensity (betaEnsembleWeight β N)

/-- **Empirical spectral measure** `L_N = N⁻¹ ∑_{i<N} δ_{λᵢ}` of a point `λ ∈ ℝ^N`, as a probability
measure on `ℝ` (for `N = 0` it is `δ₀`, a convention irrelevant to asymptotics). -/
noncomputable def spectralEmpiricalMeasure (N : ℕ) (x : Fin N → ℝ) : ProbabilityMeasure ℝ :=
  sampleEmpiricalMeasure (fun i => if h : i < N then x ⟨i, h⟩ else 0) N

/-- The logarithmic-energy kernel `log |x - y|⁻¹ + (x² + y²)/4 - (1/2 - log 2) ≥ 0`, equal to `∞`
on the diagonal. -/
noncomputable def logEnergyKernel (x y : ℝ) : ℝ≥0∞ :=
  if x = y then ⊤ else
    ENNReal.ofReal (Real.log |x - y|⁻¹ + (x ^ 2 + y ^ 2) / 4 - (1 / 2 - Real.log 2))

/-- **The Ben Arous–Guionnet rate function**
`I_β(μ) = (β/4) ∫ x² dμ - (β/2) ∫∫ log |x - y| dμ dμ - 3β/8`, written as
`(β/2) ∫∫ g dμ dμ - (β/8 + (β/2) log 2)` with the nonnegative kernel `g = logEnergyKernel` (see the
module docstring for the derivation). -/
noncomputable def benArousGuionnetRate (β : ℝ) (μ : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (β / 2) * ∫⁻ x, ∫⁻ y, logEnergyKernel x y ∂(μ : Measure ℝ) ∂(μ : Measure ℝ) -
    ENNReal.ofReal (β / 8 + β / 2 * Real.log 2)

/-- **Ben Arous–Guionnet large deviation principle** (Guionnet, "Large deviations and stochastic
calculus for large random matrices", *Probability Surveys* 1 (2004), Theorem 3.1(1c) and (2), for
`β = 1, 2, 4`; Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices* (manuscript
numbering), Theorem 2.6.1
with `V(x) = βx²/4`, for every `β > 0`). For `β > 0`, the laws of the empirical spectral measure
`L_N` of the Gaussian `β`-ensemble satisfy, in the space of probability measures on `ℝ` with the
weak topology, a large deviation principle at speed `N²` with the good rate function `I_β`.
As in Sanov's theorem here, the statement assumes that the open sets of the weak topology are
measurable for the Giry σ-algebra, which holds on `ℝ` but is not yet an instance in Mathlib. -/
theorem_wanted benArousGuionnet_ldp {β : ℝ} (hβ : 0 < β)
    [OpensMeasurableSpace (ProbabilityMeasure ℝ)] :
    SatisfiesLDPAtSpeed (fun N => (N : ℝ) ^ 2)
        (fun N => (betaEnsemble β hβ N).map (spectralEmpiricalMeasure N))
        (benArousGuionnetRate β) ∧
      IsGoodRateFunction (benArousGuionnetRate β)

/-- **The semicircle law is the unique zero of the Ben Arous–Guionnet rate function** (Guionnet,
*Probability Surveys* 1 (2004), Theorem 3.1(1e); Anderson, Guionnet and Zeitouni (manuscript
numbering), Lemma 2.6.2(e)).
For `β > 0`, `I_β(μ) = 0` if and only if `μ` is the semicircle law on `[-2, 2]`. -/
theorem_wanted benArousGuionnetRate_eq_zero_iff {β : ℝ} (hβ : 0 < β) (μ : ProbabilityMeasure ℝ) :
    benArousGuionnetRate β μ = 0 ↔ (μ : Measure ℝ) = ProbabilityTheory.semicircleReal

end MathlibExt.Probability.BenArousGuionnetWanted
