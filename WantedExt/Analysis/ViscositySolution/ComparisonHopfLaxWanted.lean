/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.ViscositySolution.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Wanted: the comparison principle and the Hopf–Lax formula

Two central theorems of the theory of viscosity solutions of first-order Hamilton–Jacobi
equations whose proofs are deferred:

* `le_of_isViscositySubsolution_of_isViscositySupersolution_of_structure`: the comparison
  principle of Crandall, Ishii and Lions (*User's guide*, Theorem 3.3) for first-order equations,
  semicontinuous sub- and supersolutions and the structure conditions (3.13)–(3.14). The case of
  continuous sub- and supersolutions is proved in `MathlibExt.Analysis.ViscositySolution.Comparison`
  (`le_of_isViscositySubsolution_of_isViscositySupersolution_of_proper`).
* `hopfLax_isViscositySolution`: the Hopf–Lax formula gives a viscosity solution of
  `u_t + H(D_x u) = 0`, `u(·, 0) = g`, for convex superlinear `H` and bounded Lipschitz `g`.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992) 1–67, arXiv:math/9207212, §3.
* J. Calder, *Lecture notes on viscosity solutions*, version of 30 July 2024, §6.2.
-/

@[expose] public section

namespace MathlibExt.Analysis.ViscositySolutionWanted

open Filter Topology Set MathlibExt.Analysis.ViscositySolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Comparison principle for first-order equations** (Crandall and Lions 1983; Crandall, Ishii
and Lions, *User's guide*, Bull. AMS 1992, Theorem 3.3 for an `F` independent of the Hessian
variable). Let `Ω` be a bounded open subset of a finite-dimensional real inner product space and
`F` continuous on `closure Ω × ℝ × E*`, with
* (3.13) properness: `γ (r - s) ≤ F(x, r, p) - F(x, s, p)` for `r ≥ s` and `x ∈ closure Ω`,
  with `γ > 0`;
* (3.14) a modulus `ω` with `ω(0+) = 0`, `ω ≥ 0`, such that
  `F(y, r, α⟪x - y, ·⟫) - F(x, r, α⟪x - y, ·⟫) ≤ ω(α‖x - y‖² + ‖x - y‖)` for `x, y ∈ Ω`,
  `r ∈ ℝ` and `α > 0` (the matrix condition (3.10) is vacuous here, take `X = Y = 0`).
As in the printed user's guide, (3.13) is asked on `closure Ω` and (3.14) only on `Ω`.
If `u` is upper semicontinuous on `closure Ω` and a viscosity subsolution, `v` lower
semicontinuous on `closure Ω` and a viscosity supersolution of `F = 0` on `Ω`, and `u ≤ v` on
`∂Ω`, then `u ≤ v` on `Ω`. Test functions are `C¹` here and `C²` in the user's guide; a
`C¹`-tested subsolution is in particular a `C²`-tested one, so this is a special case of
Theorem 3.3. The case of continuous `u` and `v` is proved in
`MathlibExt.Analysis.ViscositySolution` as
`le_of_isViscositySubsolution_of_isViscositySupersolution_of_proper`; what remains is
semicontinuity. -/
theorem_wanted le_of_isViscositySubsolution_of_isViscositySupersolution_of_structure
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (F : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (hF : ContinuousOn (fun q : E × ℝ × (E →L[ℝ] ℝ) => F q.1 q.2.1 q.2.2)
      (closure Ω ×ˢ univ ×ˢ univ))
    {γ : ℝ} (hγ : 0 < γ)
    (hproper : ∀ x ∈ closure Ω, ∀ r s : ℝ, ∀ p : E →L[ℝ] ℝ, s ≤ r →
      γ * (r - s) ≤ F x r p - F x s p)
    (ω : ℝ → ℝ) (hω : Tendsto ω (𝓝[>] 0) (𝓝 0)) (hω0 : ∀ t, 0 ≤ t → 0 ≤ ω t)
    (hstruct : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ r : ℝ, ∀ α : ℝ, 0 < α →
      F y r (α • innerSL ℝ (x - y)) - F x r (α • innerSL ℝ (x - y)) ≤
        ω (α * ‖x - y‖ ^ 2 + ‖x - y‖))
    {u v : E → ℝ} (hu : UpperSemicontinuousOn u (closure Ω))
    (hv : LowerSemicontinuousOn v (closure Ω))
    (hsub : IsViscositySubsolution F Ω u) (hsup : IsViscositySupersolution F Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ Ω, u x ≤ v x

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
