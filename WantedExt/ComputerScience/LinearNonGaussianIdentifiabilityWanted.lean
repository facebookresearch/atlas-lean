/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic

/-!
# Identifiability of the causal direction in a linear additive noise model

In a bivariate structural equation `Y = φ X + N` with the noise `N` independent of the cause
`X`, a *backward* model `X = ψ Y + Ñ` with `Ñ` independent of `Y` exists if and only if `X` and
`N` are Gaussian (Peters, Mooij, Janzing and Schölkopf, Proposition 13, after Shimizu et al.
2006). The "if" direction, the linear Gaussian case in which the causal direction cannot be
read off the joint law, is proved in `MathlibExt.Probability.LinearGaussianBackwardModel`. The
"only if" direction recorded here says that with non-Gaussian cause or noise the causal
direction is identifiable from observational data. It is the bivariate case of the
identifiability of linear non-Gaussian acyclic models (LiNGAM, Shimizu et al. 2006) and rests on
the Darmois–Skitovich theorem, which is not in Mathlib.

The nondegeneracy hypotheses are explicit here; Proposition 13 tacitly works with nondegenerate
variables. They are needed for both variables: if `X` is almost surely constant, `ψ = 0` gives a
backward model for every law of `N`, and if `N` is almost surely constant, `ψ = 1/φ` makes
`X - ψ Y = -N/φ` constant, a backward model for every law of `X`.

Reference: J. Peters, J. M. Mooij, D. Janzing and B. Schölkopf, "Causal discovery with
continuous additive noise models", *J. Mach. Learn. Res.* **15** (2014), 2009–2053,
Proposition 13 (after S. Shimizu, P. O. Hoyer, A. Hyvärinen and A. Kerminen, "A linear
non-Gaussian acyclic model for causal discovery", *J. Mach. Learn. Res.* **7** (2006),
2003–2030).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.ComputerScience.LinearNonGaussianIdentifiabilityWanted

/-- **A reversible linear additive noise model is Gaussian** (Peters, Mooij, Janzing and
Schölkopf, *Causal discovery with continuous additive noise models*, JMLR 15 (2014), the "only
if" direction of Proposition 13, after Shimizu et al. 2006). Let `X` and `N` be independent
real random variables, neither almost surely constant, and let `Y = φ X + N` with `φ ≠ 0`. If
there is `ψ ∈ ℝ` such that `Ñ = X - ψ Y` is independent of `Y`, then `X` and `N` have
nondegenerate Gaussian laws. -/
theorem_wanted gaussian_of_indepFun_backward {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X N : Ω → ℝ} (hX : Measurable X)
    (hN : Measurable N) (hXN : IndepFun X N P) (hXc : ∀ c : ℝ, ¬ X =ᵐ[P] fun _ => c)
    (hNc : ∀ c : ℝ, ¬ N =ᵐ[P] fun _ => c) {φ : ℝ} (hφ : φ ≠ 0) {ψ : ℝ}
    (hback : IndepFun (fun ω => X ω - ψ * (φ * X ω + N ω)) (fun ω => φ * X ω + N ω) P) :
    (∃ (m : ℝ) (v : NNReal), v ≠ 0 ∧ P.map X = gaussianReal m v) ∧
      ∃ (m : ℝ) (v : NNReal), v ≠ 0 ∧ P.map N = gaussianReal m v

end MathlibExt.ComputerScience.LinearNonGaussianIdentifiabilityWanted
