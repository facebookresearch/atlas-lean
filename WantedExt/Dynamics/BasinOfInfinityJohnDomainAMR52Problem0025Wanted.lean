/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Basins of infinity that are John domains (Carleson, Stony Brook problems)

L. Carleson, Geometry of Julia sets (Stony Brook problems, 1992): for `1 - a z²` with `a` real, the
critical point never returning close to itself is equivalent to the Fatou set being a John domain.
To which extent does this hold for general Misiurewicz points?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace MathlibExt.Dynamics.BasinOfInfinityJohnDomainAMR52Problem0025Wanted

/-!
Source: L. Carleson, Geometry of Julia sets, in J. Milnor (ed.), Problems in holomorphic dynamics
(Stony Brook, 1992), arXiv:math/9205209; Stony Brook - Open Problems in Dynamical Systems, 1992,
Carleson 4, https://www.math.stonybrook.edu/open-problems-dynamical-systems. UnsolvedMath record
UM-05300025 (`AMR-052-0025`), dataset ulamai/UnsolvedMath v1.8.0.

The answer is stated, as Carleson, Jones and Yoccoz prove it, for every complex polynomial `P` of
degree at least `2` and its basin of infinity `A_∞ = {z : P^n(z) → ∞}` (the Fatou set at Carleson's
real Misiurewicz parameters), with Julia set `J = ∂A_∞`. Semi-hyperbolicity is condition (d) of the
zbMATH summary of their paper: no parabolic periodic points (`P^n(z) = z` with `(P^n)'(z)` a root of
unity) and `c ∉ closure {P^n(c) : n ≥ 1}` for every critical point `c ∈ J` (Lin's restatement,
Theorem 1.3, writes the condition for all critical points; the zbMATH form with `c ∈ J` is used). A
John domain with center `∞` is Sumi's Definition 2.14 (Dynamics of postcritically bounded polynomial
semigroups III, arXiv:0811.4536, for domains containing `∞` with boundary in `ℂ`): for some `ε > 0`
every `z₁ ∈ A_∞` is joined to `∞` by an arc `γ` in `A_∞` with `dist(γ t, ∂A_∞) ≥ ε |γ t - z₁|`; an
arc to `∞` is an injective continuous `γ : [0, ∞) → A_∞` with `|γ t| → ∞`. The equivalence answers
Carleson's 'to which extent': it holds for every polynomial without parabolic cycles.
-/

open Filter Topology

/-- The basin of infinity `A_∞(P)` of the polynomial `P`: the points whose orbit tends to `∞`. -/
def basinOfInfinity (P : Polynomial ℂ) : Set ℂ :=
  {z | Tendsto (fun n => ‖(fun w => P.eval w)^[n] z‖) atTop atTop}

/-- The Julia set `J(P) = ∂A_∞(P)` of the polynomial `P`. -/
def juliaSet (P : Polynomial ℂ) : Set ℂ :=
  frontier (basinOfInfinity P)

/-- `Ω ⊆ ℂ` is a John domain with center `∞`: for some `ε > 0`, every `z₁ ∈ Ω` is joined to `∞` by
an arc `γ` in `Ω` (injective and continuous on `[0, ∞)`, with `|γ t| → ∞`) such that
`dist(γ t, ∂Ω) ≥ ε |γ t - z₁|` along the arc. -/
def IsJohnDomainAtInfinity (Ω : Set ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ z₁ ∈ Ω, ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Ici 0) ∧ Set.InjOn γ (Set.Ici 0) ∧
    γ 0 = z₁ ∧ (∀ t, 0 ≤ t → γ t ∈ Ω) ∧ Tendsto (fun t => ‖γ t‖) atTop atTop ∧
    ∀ t, 0 ≤ t → ε * ‖γ t - z₁‖ ≤ Metric.infDist (γ t) (frontier Ω)

/-- `P` has a parabolic periodic point: `P^n(z) = z` for some `n ≥ 1` whose multiplier `(P^n)'(z)`
is a root of unity. -/
def HasParabolicCycle (P : Polynomial ℂ) : Prop :=
  ∃ z : ℂ, ∃ n : ℕ, 0 < n ∧ (fun w => P.eval w)^[n] z = z ∧
    ∃ m : ℕ, 0 < m ∧ (deriv ((fun w => P.eval w)^[n]) z) ^ m = 1

/-- Every critical point `c` of `P` in the Julia set is non-recurrent:
`c ∉ ω(c) = closure {P^n(c) : n ≥ 1}`. -/
def CriticalPointsInJuliaNonrecurrent (P : Polynomial ℂ) : Prop :=
  ∀ c ∈ juliaSet P, P.derivative.eval c = 0 →
    c ∉ closure (Set.range fun n : ℕ => (fun w => P.eval w)^[n + 1] c)

/-- Carleson's question, answered by Carleson, Jones and Yoccoz for every complex polynomial: for
`P` of degree at least `2`, the basin of infinity is a John domain if and only if `P` is
semi-hyperbolic, that is, has no parabolic periodic points and no recurrent critical point in its
Julia set. -/
def basinJohnIffSemiHyperbolic : Prop :=
  ∀ P : Polynomial ℂ, 2 ≤ P.natDegree →
    (IsJohnDomainAtInfinity (basinOfInfinity P) ↔
      ¬ HasParabolicCycle P ∧ CriticalPointsInJuliaNonrecurrent P)

/--
Resolved true: Carleson, Jones and Yoccoz proved that for every polynomial of degree at least `2`
the basin of infinity is a John domain if and only if the polynomial has no parabolic periodic
points and no critical point in the Julia set is recurrent (semi-hyperbolicity), extending the
real-quadratic equivalence to all complex polynomials once parabolic points are excluded. Source: L.
Carleson, Geometry of Julia sets, in J. Milnor (ed.), Problems in holomorphic dynamics (Stony Brook,
1992), arXiv:math/9205209; Stony Brook - Open Problems in Dynamical Systems, 1992, Carleson 4,
https://www.math.stonybrook.edu/open-problems-dynamical-systems; resolution: L. Carleson, P. W.
Jones and J.-C. Yoccoz, Julia and John, Bol. Soc. Bras. Mat. 25 (1994), 1-30, main theorem ([CJY94,
Theorem 1.1] in P. Lin, Quasisymmetry of semihyperbolic Julia equivalences, preprint 2018, Theorem
1.3), as summarized in zbMATH Zbl 0804.30023 (review by N. Steinmetz): for a polynomial P of degree
≥ 2 with Julia set J and basin at infinity A_∞ (J = ∂A_∞), each of the following is equivalent to
semi-hyperbolicity: (a) A_∞ is a John domain; ... (d) P has no parabolic periodic points, and for
all c ∈ J with P'(c) = 0, c ∉ ω(c) = closure ∪_{n≥1} P^n(c); N. Mihalache, Julia and John revisited,
Fund. Math. 215 (2011), 67-86, Section 1: the main result of Carleson, Jones and Yoccoz 'states
equivalence for polynomial maps between a geometric condition, John regularity of the basin of
infinity, and a topological condition on critical orbits, semi-hyperbolicity',
https://doi.org/10.1007/BF01232933.
-/
public theorem_wanted basinJohnIffSemiHyperbolic_holds : basinJohnIffSemiHyperbolic

end MathlibExt.Dynamics.BasinOfInfinityJohnDomainAMR52Problem0025Wanted
