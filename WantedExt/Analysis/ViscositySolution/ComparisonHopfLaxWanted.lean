/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.ViscositySolution.Comparison
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Wanted: the Hopf–Lax formula

The first-order semicontinuous comparison principle is re-exported from
`MathlibExt.Analysis.ViscositySolution.Comparison`. The Hopf–Lax formula below remains deferred:

* `hopfLax_isViscositySolution`: the Hopf–Lax formula gives a viscosity solution of
  `u_t + H(D_x u) = 0`, `u(·, 0) = g`, for convex superlinear `H` and bounded Lipschitz `g`.

## References

* J. Calder, *Lecture notes on viscosity solutions*, version of 30 July 2024, §6.2.
-/

@[expose] public section

namespace MathlibExt.Analysis.ViscositySolutionWanted

open Filter Topology Set MathlibExt.Analysis.ViscositySolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Hopf–Lax formula** (Hopf 1965, Lax 1957; Calder, *Lecture notes on viscosity
solutions*, 2024, §6.2, which defers the full proof to Evans, *Partial Differential Equations*,
Chapter 10). Let `H` be a convex superlinear Hamiltonian on the dual `E*` of a
finite-dimensional real inner product space (`H(p)/‖p‖ → ∞`), `L(v) = sup_p (p v - H(p))` its
Legendre transform, and `g` bounded and Lipschitz. Then
`u(x, t) = inf_y (t L((x - y)/t) + g(y))`
is a viscosity solution of `u_t + H(D_x u) = 0` on `E × (0, ∞)` (the gradient of a function on
`E × ℝ` is a functional `p`, with time component `p (0, 1)` and space component `p ∘ inl`), and
`u(x, t) → g(x)` as `(x', t) → (x, 0)` with `t > 0`. Under these hypotheses `L` and `u` are real
valued. Calder also states that `u` is the unique viscosity solution; uniqueness is not part of
this statement. -/
theorem_wanted hopfLax_isViscositySolution (H : (E →L[ℝ] ℝ) → ℝ) (hconv : ConvexOn ℝ univ H)
    (hsuper : Tendsto (fun p => H p / ‖p‖) (cocompact (E →L[ℝ] ℝ)) atTop)
    (g : E → ℝ) (hgLip : ∃ K, LipschitzWith K g) (hgb : ∃ C, ∀ x, |g x| ≤ C) :
    let L : E → ℝ := fun v => ⨆ p : E →L[ℝ] ℝ, (p v - H p)
    let u : E × ℝ → ℝ := fun q => ⨅ y : E, (q.2 * L (q.2⁻¹ • (q.1 - y)) + g y)
    IsViscositySolution (fun _ _ p => p (0, 1) + H (p.comp (ContinuousLinearMap.inl ℝ E ℝ)))
        (univ ×ˢ Ioi 0) u ∧
      ∀ x : E, Tendsto u (𝓝[univ ×ˢ Ioi 0] (x, 0)) (𝓝 (g x))

end MathlibExt.Analysis.ViscositySolutionWanted
