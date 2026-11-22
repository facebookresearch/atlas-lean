/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.DirichletForm.QuasiRegular
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Dirichlet forms: wanted theorems

Central theorems of the theory of Dirichlet forms whose proofs are deferred.

* `unitContractionOperates_iff_resolvent`: the Beurling–Deny correspondence between Markovian
  closed forms
  and Markovian resolvents (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd revised and extended ed., de Gruyter, 2011, Theorem 1.4.1, (b) ⇔ (d)).
* `isQuasiRegular_of_isRegular`: regular forms are quasi-regular (M. Röckner and B. Schmuland,
  *Canad. J. Math.* 47 (1995), Proposition 0.9).
* `tendsto_brownian_approximatingForm`: the Dirichlet form of linear Brownian motion is
  `½ ∫ f'²` (FOT, Example 4.2.1 and Lemma 1.3.4).

Fukushima's theorem (a regular Dirichlet form is the Dirichlet form of an `m`-symmetric Hunt
process, FOT Theorem 7.2.1) and the Albeverio–Ma–Röckner characterisation of quasi-regular forms
by right processes are not stated: Mathlib has no Hunt or right processes, and a statement about
an undefined process predicate would not be a faithful proposition.
-/

@[expose] public section

open MeasureTheory Filter Topology Matrix ProbabilityTheory
open scoped RealInnerProductSpace NNReal ContDiff

open MathlibExt.Probability.DirichletForm

namespace MathlibExt.Probability.DirichletFormWanted

/-- **Beurling–Deny: the unit contraction operates on a closed form iff its resolvent is
Markovian.** Let `E` be a closed symmetric form on `L²(X; m)`, `m` σ-finite. For `α > 0` and
`f ∈ L²`, the resolvent `G_α f` is the element `u ∈ D[E]` with `E(u, v) + α (u, v) = (f, v)` for
all `v ∈ D[E]` (FOT, equation (1.3.7)). Then the unit contraction operates on `E` (condition
(E.4)′, equivalent for closed forms to FOT's Markov condition (E.4)) if and only if every
`α G_α` is Markovian: `0 ≤ f ≤ 1` a.e. implies `0 ≤ α G_α f ≤ 1` a.e. (Fukushima, Oshima and
Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, Theorem 1.4.1, (b) ⇔
(d)). FOT prove (b) ⇒ (e) under their topological assumption (1.1.7) and note (footnote 10) that
it holds without it, referring to Ma–Röckner (1992) and Bouleau–Hirsch (1991); the statement
here has no topological assumption. -/
theorem_wanted unitContractionOperates_iff_resolvent {X : Type*} [MeasurableSpace X] {m : Measure X}
    [SigmaFinite m] (E : SymmetricForm m) (hE : E.IsClosed) :
    E.UnitContractionOperates ↔ ∀ α : ℝ, 0 < α → ∀ f u : Lp ℝ 2 m, u ∈ E.domain →
      (∀ v ∈ E.domain, E.form u v + α * ⟪u, v⟫ = ⟪f, v⟫) →
      (∀ᵐ x ∂m, 0 ≤ f x ∧ f x ≤ 1) → ∀ᵐ x ∂m, 0 ≤ α * u x ∧ α * u x ≤ 1

/-- **Regular forms are quasi-regular.** Let `X` be a locally compact separable metric space and `m`
a positive Radon measure on `X`. A regular Dirichlet form on `L²(X; m)` is quasi-regular (M.
Röckner and B. Schmuland, *Quasi-regular Dirichlet forms: examples and counterexamples*, Canad.
J. Math. 47 (1995), Proposition 0.9, stated there for regular semi-Dirichlet forms; cf.
Ma–Röckner 1992, Chapter IV, Example 4a, as cited there). Metrizability cannot be dropped:
Röckner–Schmuland, Remark 0.10 and §5(a), give a regular Dirichlet form on a separable compact
non-metrizable Hausdorff space that is not quasi-regular. -/
theorem_wanted isQuasiRegular_of_isRegular {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
    (E : SymmetricForm m) (hD : E.IsDirichletForm) (hreg : E.IsRegular) : E.IsQuasiRegular

/-- **The Dirichlet form of linear Brownian motion is `½ ∫ f'²`.** For a smooth compactly
supported `f : ℝ → ℝ`, with `T_t f(x) = E f(x + B_t) = ∫ f(x + y) N(0, t)(dy)` the Brownian
semigroup, the approximating forms `(1/t)(f - T_t f, f)_{L²}` tend to `½ ∫ f'(x)² dx` as
`t ↓ 0`. This is the case `d = 1`, `u ∈ C_c^∞(ℝ)` of Fukushima, Oshima and Takeda, *Dirichlet
Forms and Symmetric Markov Processes*, 2nd ed., 2011, Example 4.2.1 (the Dirichlet form of
`d`-dimensional Brownian motion is `(½ D, H¹(ℝ^d))`, with the Gaussian semigroup (1.4.25)),
combined with their Lemma 1.3.4(i) (`E(u, u) = lim_{t ↓ 0} (1/t)(u - T_t u, u)`). -/
theorem_wanted tendsto_brownian_approximatingForm {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ∫ x, f x * (f x - ∫ y, f (x + y) ∂gaussianReal 0 t))
      (𝓝[>] 0) (𝓝 (1 / 2 * ∫ x, deriv f x ^ 2))

end MathlibExt.Probability.DirichletFormWanted
