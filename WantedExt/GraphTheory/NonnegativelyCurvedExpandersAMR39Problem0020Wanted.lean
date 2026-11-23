/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Expanders with non-negative coarse Ricci curvature (Ollivier's Problem T)

Y. Ollivier, Problem T: does there exist a family of bounded-degree expander graphs, with spectral
gap bounded away from zero and diameter tending to infinity, whose coarse Ricci curvature is
non-negative?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MathlibExt.GraphTheory.NonnegativelyCurvedExpandersAMR39Problem0020Wanted

/-!
Source: Y. Ollivier, Discrete Ricci curvature: open problems (2008), Problem T,
https://www.yann-ollivier.org/rech/publs/problems_curvmarkov.pdf. UnsolvedMath record UM-04000020
(`AMR-039-0020`), dataset ulamai/UnsolvedMath v1.8.0.

Definitions follow Salez, §1.1: the lazy simple random walk `P(x, x) = 1/2`, `P(x, y) = 1/(2 deg x)`
for `y ∼ x`; Ollivier-Ricci curvature `κ(x, y) = 1 - W₁(P(x, ·), P(y, ·))` on edges, with `W₁` for
the graph distance (`κ ≥ 0` iff some coupling has expected distance at most `1`, the infimum over
couplings being attained); a family of expanders is bounded degree `Δ`, diverging sizes and second
eigenvalue `λ₂(P) ≤ ρ < 1`, stated in Rayleigh-quotient form for the degree measure. With bounded
degree, diverging diameter and diverging size are equivalent. Salez notes that his result covers
every laziness variant of `κ`.
-/

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The transition matrix of the lazy simple random walk on `G`: stay with probability `1/2`,
otherwise move to a uniform random neighbour. -/
noncomputable def lazyWalk (x y : V) : ℝ :=
  if x = y then 1 / 2 else if G.Adj x y then 1 / (2 * G.degree x) else 0

/-- `W₁(P(x, ·), P(y, ·)) ≤ 1` for the graph distance: some coupling of the two lazy-walk steps has
expected distance at most `1` (on a finite graph the infimum over couplings is attained). -/
def WassersteinStepAtMostOne (x y : V) : Prop :=
  ∃ π : V → V → ℝ, (∀ u v, 0 ≤ π u v) ∧ (∀ u, ∑ v, π u v = lazyWalk G x u) ∧
    (∀ v, ∑ u, π u v = lazyWalk G y v) ∧ ∑ u, ∑ v, π u v * G.dist u v ≤ 1

/-- Non-negative Ollivier-Ricci curvature: `κ(x, y) = 1 - W₁(P(x, ·), P(y, ·)) ≥ 0` on every
edge. -/
def IsNonnegativelyCurved : Prop :=
  ∀ x y, G.Adj x y → WassersteinStepAtMostOne G x y

/-- The second largest eigenvalue of the lazy walk (self-adjoint for the degree measure) is at most
`ρ`, in Rayleigh-quotient form: `⟨f, P f⟩_deg ≤ ρ ⟨f, f⟩_deg` for every `f` orthogonal to the
constants in `ℓ²(deg)`. -/
def SecondEigenvalueAtMost (ρ : ℝ) : Prop :=
  ∀ f : V → ℝ, ∑ x, (G.degree x : ℝ) * f x = 0 →
    ∑ x, (G.degree x : ℝ) * f x * ∑ y, lazyWalk G x y * f y ≤ ρ * ∑ x, (G.degree x : ℝ) * f x ^ 2

/-- Naor-Milman's question (Ollivier's Problem T), with a positive answer: there are bounded-degree
non-negatively curved expanders, that is, `Δ` and `ρ < 1` such that arbitrarily large connected
graphs have maximum degree at most `Δ`, second lazy-walk eigenvalue at most `ρ` and non-negative
Ollivier-Ricci curvature. -/
def nonnegativelyCurvedExpandersExist : Prop :=
  ∃ (Δ : ℕ) (ρ : ℝ), ρ < 1 ∧ ∀ N : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj), N ≤ Fintype.card V ∧ G.Connected ∧
      (∀ x, G.degree x ≤ Δ) ∧ SecondEigenvalueAtMost G ρ ∧ IsNonnegativelyCurved G

/--
Resolved false: Salez proves that bounded-degree expanders with non-negative Ollivier-Ricci
curvature do not exist: for fixed `Δ` and `ρ < 1` no arbitrarily large graphs have maximum degree at
most `Δ`, `λ₂ ≤ ρ` and `κ ≥ 0` (Theorem 2, answering Question 1; a graph with these three properties
meets none of the three alternatives of Theorem 2 once `|V| > 1/ε`). Source: Y. Ollivier, Discrete
Ricci curvature: open problems (2008), Problem T,
https://www.yann-ollivier.org/rech/publs/problems_curvmarkov.pdf; resolution: J. Salez, Sparse
expanders have negative curvature, Geom. Funct. Anal. 32 (2022); arXiv:2101.08242, Question 1
(Problem T) answered negatively by Theorem 2: for Δ ≥ 1 and ρ ∈ (0, 1) there is ε > 0 such that
every finite graph G has ∑ₓ deg(x) log deg(x) > (Δ log Δ)|V|, or at least ε|V| eigenvalues of the
lazy walk P_G above ρ, or at least ε|E| edges with κ < -ε; abstract: bounded-degree expanders with
non-negative Ollivier-Ricci curvature do not exist, https://doi.org/10.1007/s00039-022-00618-3.
-/
public theorem_wanted nonnegativelyCurvedExpandersExist_refuted :
    ¬ nonnegativelyCurvedExpandersExist

end MathlibExt.GraphTheory.NonnegativelyCurvedExpandersAMR39Problem0020Wanted
