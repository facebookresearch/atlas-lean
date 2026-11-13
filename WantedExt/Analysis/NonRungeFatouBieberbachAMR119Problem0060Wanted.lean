/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A Fatou-Bieberbach domain which is not Runge (SCV problem list, Problem 63)

Several Complex Variables Problem List, Problem 63 (F. Forstnerič): do there exist Fatou-Bieberbach
domains which are not Runge? A Fatou-Bieberbach domain is a proper subdomain of `ℂ²` which is
biholomorphic to `ℂ²`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import WantedExt.Analysis.SeveralComplexVariablesShared

@[expose] public section

namespace MathlibExt.Analysis.NonRungeFatouBieberbachAMR119Problem0060Wanted

/-!
Source: G. Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables
Problem List, arXiv:math/9509202 (1995), Problem 63. UnsolvedMath record UM-00800264
(`AMR-119-0060`), dataset ulamai/UnsolvedMath v1.8.0.

`ℂ²` is `Fin 2 → ℂ`. Fatou-Bieberbach domains are `IsFatouBieberbachDomain 2` from the shared module
(copied from the open entry `FatouBieberbachIntermediatePseudoconvex`). A domain is Runge in `ℂ²`
when every holomorphic function on it is a uniform limit of polynomials on each compact subset
(equivalently of entire functions, which are themselves locally uniform limits of their Taylor
polynomials).
-/

open MathlibExt.Analysis.SeveralComplexVariablesShared

/-- An open set `Ω ⊆ ℂⁿ` is Runge: every function holomorphic on `Ω` is a uniform limit of
polynomials on every compact subset of `Ω`. -/
def IsRunge {n : ℕ} (Ω : Set (Fin n → ℂ)) : Prop :=
  ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f Ω → ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0,
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z ∈ K, ‖f z - MvPolynomial.eval z p‖ < ε

/-- SCV Problem List, Problem 63 (F. Forstnerič): there is a Fatou-Bieberbach domain in `ℂ²` (a
proper subdomain biholomorphic to `ℂ²`) which is not Runge. -/
def nonRungeFatouBieberbachDomainExists : Prop :=
  ∃ Ω : Set (Fin 2 → ℂ), IsFatouBieberbachDomain 2 Ω ∧ ¬ IsRunge Ω

/--
Resolved true: Wold constructed a Fatou-Bieberbach domain in ℂ² which is not Runge (it contains a
holomorphically convex union of two totally real discs but not its polynomial hull). Source: G.
Buzzard, J. E. Fornæss, E. A. Gavosto, S. G. Krantz (eds.), The Several Complex Variables Problem
List, arXiv:math/9509202 (1995), Problem 63; resolution: E. F. Wold, A Fatou-Bieberbach domain in ℂ²
which is not Runge, Math. Ann. 340 (2008), 775-780, main theorem; cited as such in E. F. Wold, A
long ℂ² which is not Stein, Ark. Mat. 48 (2010), 207-210, §1 ('the construction of a non-Runge
Fatou-Bieberbach domain in ℂ² [6]'), and in arXiv:2603.04903, §1 ('The long-standing question
whether there exist non-Runge Fatou-Bieberbach domains in ℂⁿ was settled by Wold in the positive'),
https://arxiv.org/abs/2603.04903.
-/
public theorem_wanted nonRungeFatouBieberbachDomainExists_holds :
    nonRungeFatouBieberbachDomainExists

end MathlibExt.Analysis.NonRungeFatouBieberbachAMR119Problem0060Wanted
