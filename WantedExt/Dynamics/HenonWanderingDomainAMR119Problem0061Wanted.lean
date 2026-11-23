/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wandering domains for complex Hénon maps (SCV problem list, Problem 64)

Several Complex Variables Problem List, Problem 64 (section "The invariant set `K⁺` of a polynomial
complex Hénon map"): do there exist wandering domains for complex Hénon maps?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Order.CompletePartialOrder
public import WantedExt.Analysis.SeveralComplexVariablesShared

@[expose] public section

namespace MathlibExt.Dynamics.HenonWanderingDomainAMR119Problem0061Wanted

/-!
Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables
Problem List, arXiv:math/9509202 (1995), Problem 64. UnsolvedMath record UM-00800265
(`AMR-119-0061`), dataset ulamai/UnsolvedMath v1.8.0.

The Fatou set is the one the problem list uses in the next problem (65): the set of points near
which the forward iterates are locally bounded (`fatouSet` in the shared module, copied from the
open entry `SCVHenonFatouComponents`); for polynomial automorphisms its components are the
components of the interior of `K⁺`. A wandering domain is a connected component `Ω` of the Fatou set
with `Fⁿ(Ω)` and `Fᵐ(Ω)` disjoint for all `n ≠ m`. Complex Hénon maps are written `(z, w) ↦ (p(z) -
a w, b z)` with `deg p ≥ 2` and `a, b ≠ 0`, the diagonal conjugates of the standard form `(x, y) ↦
(p(x) - δ y, x)`.
-/

open MathlibExt.Analysis.SeveralComplexVariablesShared

/-- `F` is a complex Hénon map `(z, w) ↦ (p(z) - a w, b z)` with `p` a polynomial of degree at
least two and `a, b ≠ 0` (diagonal conjugates of the standard form `(x, y) ↦ (p(x) - δ y, x)`). -/
def IsComplexHenonMap (F : (Fin 2 → ℂ) → Fin 2 → ℂ) : Prop :=
  ∃ (p : Polynomial ℂ) (a b : ℂ), 2 ≤ p.natDegree ∧ a ≠ 0 ∧ b ≠ 0 ∧
    ∀ z : Fin 2 → ℂ, F z = ![p.eval (z 0) - a * z 1, b * z 0]

/-- SCV Problem List, Problem 64: some complex Hénon map has a wandering domain, a connected
component `Ω` of its Fatou set (points near which the forward iterates are bounded) whose forward
images `Fⁿ(Ω)`, `n ≥ 0`, are pairwise disjoint. -/
def henonWanderingDomainExists : Prop :=
  ∃ F : (Fin 2 → ℂ) → Fin 2 → ℂ, IsComplexHenonMap F ∧ ∃ z ∈ fatouSet F, ∀ n m : ℕ, n ≠ m →
    Disjoint (F^[n] '' connectedComponentIn (fatouSet F) z)
      (F^[m] '' connectedComponentIn (fatouSet F) z)

/--
Resolved true: Berger and Biebler construct real Hénon maps `(z, w) ↦ (z⁶ + p₄ z⁴ + ⋯ + p₀ - w, b
z)` with a wandering Fatou component, a component of the interior of `K⁺`, solving the problem
reported by Bedford and Smillie in 1991. Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G.
Krantz (eds.), The Several Complex Variables Problem List, arXiv:math/9509202 (1995), Problem 64;
resolution: P. Berger, S. Biebler, Emergence of wandering stable components, J. Amer. Math. Soc. 36
(2023), arXiv:2001.08649, Theorem A: for every sufficiently small real b ≠ 0 there is a nonempty
open P_b ⊂ ℝ⁵ such that for a dense set of p ∈ P_b the polynomial automorphism f_p(z, w) = (z⁶ +
Σ_{i≤4} pᵢ zⁱ - w, b z) has a wandering Fatou component in ℂ² (whose compact subsets have iterates
of diameter tending to 0); §1.1: for polynomial automorphisms of ℂ² the Fatou components other than
the escaping set are the components of int K⁺, https://arxiv.org/abs/2001.08649.
-/
public theorem_wanted henonWanderingDomainExists_holds : henonWanderingDomainExists

end MathlibExt.Dynamics.HenonWanderingDomainAMR119Problem0061Wanted
