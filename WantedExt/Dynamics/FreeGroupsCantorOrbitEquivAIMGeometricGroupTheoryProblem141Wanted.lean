/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F₂ and F₃ have topologically orbit equivalent free minimal Cantor actions (AimPL L², 2.3)

AimPL, L² invariants for finitely generated groups, Problem 2.3 (K. Medynets): are 2- and
3-generated groups topologically orbit equivalent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Dynamics.Minimal
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

namespace MathlibExt.Dynamics.FreeGroupsCantorOrbitEquivAIMGeometricGroupTheoryProblem141Wanted

/-!
Source: AimPL: L² invariants for finitely generated groups, Problem 2.3 (K. Medynets),
http://aimpl.org/l2invariantsgroups/2/. UnsolvedMath record UM-20001632
(`AIM-GEOMETRIC_GROUP_THEORY-0141`), dataset ulamai/UnsolvedMath v1.8.0.

The question sits in the section on orbit equivalence of measure preserving actions, where free
groups of different rank are not orbit equivalent (cost), and is read for the free groups `F₂` and
`F₃`. Medynets posed it at the AIM workshop L² invariants and their relatives for finitely generated
groups (12-16 September 2011); Medynets, Sauer and Thom began their paper 'during a visit at the AIM
in Palo Alto in September 2011' (Acknowledgments), and its headline corollary is this case: 'free
groups of different rank admit topologically orbit equivalent Cantor minimal actions - unlike in the
measurable setting' (abstract). Topological orbit equivalence is their Definition 2.5: free
continuous actions on the Cantor set and a homeomorphism `h` between them that maps orbits to orbits
with continuous cocycles (cocycles to discrete groups are continuous iff locally constant); the
actions are also minimal (Mathlib's `MulAction.IsMinimal`). The Cantor set is `ℕ → Bool`.
-/

/-- The Cantor space `{0, 1}^ℕ` (every Cantor space is homeomorphic to it). -/
abbrev CantorSpace : Type := ℕ → Bool

/-- AimPL Problem 2.3 (L² invariants for finitely generated groups; K. Medynets), read for the free
groups `F₂` and `F₃`: they have free, minimal (`MulAction.IsMinimal`: every orbit is dense) and
continuous (`ContinuousConstSMul`) actions on the Cantor space that are topologically orbit
equivalent, i.e. there are a homeomorphism `h` and continuous (locally constant) cocycles `α`, `β`
with `α(γ, x) • h x = h (γ • x)` and `β(η, y) • h⁻¹ y = h⁻¹ (η • y)`. -/
def freeGroupsRankTwoThreeTopologicallyOrbitEquivalent : Prop :=
  ∃ (_ : MulAction (FreeGroup (Fin 2)) CantorSpace) (_ : MulAction (FreeGroup (Fin 3)) CantorSpace),
    ContinuousConstSMul (FreeGroup (Fin 2)) CantorSpace ∧
    ContinuousConstSMul (FreeGroup (Fin 3)) CantorSpace ∧
    MulAction.IsMinimal (FreeGroup (Fin 2)) CantorSpace ∧
    MulAction.IsMinimal (FreeGroup (Fin 3)) CantorSpace ∧
    (∀ (γ : FreeGroup (Fin 2)) (x : CantorSpace), γ • x = x → γ = 1) ∧
    (∀ (η : FreeGroup (Fin 3)) (y : CantorSpace), η • y = y → η = 1) ∧
    ∃ (h : CantorSpace ≃ₜ CantorSpace) (α : FreeGroup (Fin 2) → CantorSpace → FreeGroup (Fin 3))
      (β : FreeGroup (Fin 3) → CantorSpace → FreeGroup (Fin 2)),
      (∀ γ, IsLocallyConstant (α γ)) ∧ (∀ η, IsLocallyConstant (β η)) ∧
      (∀ γ x, α γ x • h x = h (γ • x)) ∧ ∀ η y, β η y • h.symm y = h.symm (η • y)

/--
Resolved true for `F₂` and `F₃`: Medynets, Sauer and Thom proved that non-amenable quasi-isometric
finitely generated groups admit topologically orbit equivalent free Cantor minimal systems
(Corollary 3.3), and that non-abelian free groups of different rank do (Corollary 3.4), unlike in
the measurable setting. Source: AimPL: L² invariants for finitely generated groups, Problem 2.3 (K.
Medynets), http://aimpl.org/l2invariantsgroups/2/; resolution: K. Medynets, R. Sauer and A. Thom,
Cantor systems and quasi-isometry of groups, Bull. Lond. Math. Soc. 49 (2017), 709-724,
arXiv:1508.07578, Definition 2.5 (topological orbit equivalence: an orbit equivalence h with
continuous cocycles), Corollary 3.3 (non-amenable quasi-isometric finitely generated groups have
topologically orbit equivalent free Cantor minimal systems) and Corollary 3.4 (non-abelian free
groups of different rank have topologically orbit equivalent free actions); abstract: 'free groups
of different rank admit topologically orbit equivalent Cantor minimal actions unlike in the
measurable setting', https://doi.org/10.1112/blms.12059.
-/
public theorem_wanted freeGroupsRankTwoThreeTopologicallyOrbitEquivalent_holds :
    freeGroupsRankTwoThreeTopologicallyOrbitEquivalent

end MathlibExt.Dynamics.FreeGroupsCantorOrbitEquivAIMGeometricGroupTheoryProblem141Wanted
