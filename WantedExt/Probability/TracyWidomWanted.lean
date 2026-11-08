/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Wanted: the Tracy–Widom limit for the largest eigenvalue of a Wishart matrix

Johnstone's theorem: for an `n × p` matrix `X` with independent standard Gaussian entries, the
largest eigenvalue `ℓ₁` of `Xᵀ X` (a `p`-variate white Wishart matrix on `n` degrees of
freedom), centered by `μ = (√(n - 1) + √p)²` and scaled by
`σ = (√(n - 1) + √p) (1/√(n - 1) + 1/√p)^{1/3}`, converges in distribution to the Tracy–Widom
law of order one as `n, p → ∞` with `n / p → γ ≥ 1`.

This is the null distribution that Patterson, Price and Reich use to decide how many principal
components of a genotype matrix are significant; the decision rule itself is proved, conditional
on this approximation, in `MathlibExt.Biology.StatisticalGenetics.Eigenstrat`.

## Main statements

* `johnstone_largest_eigenvalue_tracyWidom` : the limit law, with the Tracy–Widom distribution
  function `F₁(s) = exp (-(1/2) ∫ₛ^∞ (q x + (x - s) q x ²) dx)` written through the
  Hastings–McLeod solution `q` of Painlevé II, `q'' = s q + 2 q³`, `q(s) ∼ Ai(s)` as `s → ∞`
  (the Airy asymptotics `Ai(s) ∼ e^{-(2/3) s^{3/2}} / (2 √π s^{1/4})` are used, so the Airy
  function itself is not needed).

## References

* I. M. Johnstone, "On the distribution of the largest eigenvalue in principal components
  analysis", Ann. Statist. 29 (2001), 295–327, Theorem 1.1.
* C. A. Tracy and H. Widom, "Level-spacing distributions and the Airy kernel", Comm. Math.
  Phys. 159 (1994), 151–174; "On orthogonal and symplectic matrix ensembles", Comm. Math. Phys.
  177 (1996), 727–754 (the order-one law `F₁`).
* S. P. Hastings and J. B. McLeod, "A boundary value problem associated with the second
  Painlevé transcendent and the Korteweg–de Vries equation", Arch. Rational Mech. Anal. 73
  (1980), 31–51.
* N. Patterson, A. L. Price and D. Reich, "Population structure and eigenanalysis", PLoS Genet.
  2 (2006), e190.
-/

@[expose] public section

namespace MathlibExt.Probability.TracyWidomWanted

open Filter MeasureTheory ProbabilityTheory Topology

/--
**Johnstone's Tracy–Widom limit.** Let `q` be the Hastings–McLeod solution of Painlevé II
(`q'' = s q + 2 q³` with `q(s) · 2 √π s^{1/4} e^{(2/3) s^{3/2}} → 1` as `s → ∞`). Let
`n k, p k → ∞` with `n k / p k → γ ≥ 1`, and let `X` have independent standard Gaussian entries
(`Measure.pi` of `gaussianReal 0 1` over `Fin (n k) × Fin (p k)`). The largest eigenvalue of
`Xᵀ X` is `ℓ₁ = sup_{‖v‖ = 1} ‖X v‖²`. Then for every `s`, the function
`x ↦ q x + (x - s) q x ²` is integrable on `(s, ∞)` and
`P((ℓ₁ - μ_k) / σ_k ≤ s) → F₁(s) = exp (-(1/2) ∫ₛ^∞ (q x + (x - s) q x ²) dx)` with Johnstone's
`μ_k = (√(n - 1) + √p)²` and `σ_k = (√(n - 1) + √p) (1/√(n - 1) + 1/√p)^{1/3}`.

Source: I. M. Johnstone, Ann. Statist. 29 (2001), 295–327, Theorem 1.1; Tracy–Widom (1996) for
`F₁`; Hastings–McLeod (1980) for `q`.
-/
public theorem_wanted johnstone_largest_eigenvalue_tracyWidom
    (q : ℝ → ℝ) (hq : ContDiff ℝ 2 q)
    (hq_ode : ∀ s, deriv (deriv q) s = s * q s + 2 * q s ^ 3)
    (hq_airy : Tendsto (fun s => q s * (2 * Real.sqrt Real.pi * s ^ (1 / 4 : ℝ) *
      Real.exp (2 / 3 * s ^ (3 / 2 : ℝ)))) atTop (𝓝 1))
    (n p : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hp : Tendsto p atTop atTop)
    (γ : ℝ) (hγ : 1 ≤ γ) (hratio : Tendsto (fun k => (n k : ℝ) / p k) atTop (𝓝 γ))
    (s : ℝ) :
    IntegrableOn (fun x => q x + (x - s) * q x ^ 2) (Set.Ioi s) ∧
      Tendsto (fun k =>
        (Measure.pi fun _ : Fin (n k) × Fin (p k) => gaussianReal 0 1)
          {X | ((⨆ v : {v : EuclideanSpace ℝ (Fin (p k)) // ‖v‖ = 1},
                ∑ i, (∑ j, X (i, j) * v.1 j) ^ 2) -
              (Real.sqrt ((n k : ℝ) - 1) + Real.sqrt (p k)) ^ 2) /
            ((Real.sqrt ((n k : ℝ) - 1) + Real.sqrt (p k)) *
              (1 / Real.sqrt ((n k : ℝ) - 1) + 1 / Real.sqrt (p k)) ^ (1 / 3 : ℝ)) ≤ s})
        atTop
        (𝓝 (ENNReal.ofReal
          (Real.exp (-(1 / 2) * ∫ x in Set.Ioi s, (q x + (x - s) * q x ^ 2)))))

end MathlibExt.Probability.TracyWidomWanted
