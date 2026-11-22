/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalEquivalences

/-!
# Finite Joyal Interval Equivalences
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.FiniteJoyalIntervalEquivalencesTest

/-- The arbitrary-target implication applies directly to J itself. -/
theorem forwardInInterval :
    (Edge.mk' (yonedaEquiv joyalInterval.forward.{u})).IsEquivalence := by
  apply Edge.isEquivalence_of_joyalInterval_extension (t := 𝟙 joyalInterval.{u})
  simp only [Category.comp_id, Edge.mk'_edge, Equiv.symm_apply_apply]

/-- An arbitrary target needs only the exact extension equation. -/
theorem arbitraryTarget {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} (e : Edge x₀ x₁)
    (t : joyalInterval.{u} ⟶ X)
    (ht : joyalInterval.forward ≫ t = yonedaEquiv.symm e.edge) : IsIso e.toHoHom :=
  Edge.isEquivalence_of_joyalInterval_extension ht

/-- Chosen inverse data retain both complete triangles even without a QC premise. -/
theorem chosenTriangles {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {e : Edge x₀ x₁}
    (I : e.InvStruct) :
    ∃ t : joyalInterval.{u} ⟶ X,
      joyalInterval.forward ≫ t = yonedaEquiv.symm e.edge ∧
      joyalInterval.leftTriangle ≫ t = yonedaEquiv.symm I.homInvId.simplex ∧
      joyalInterval.rightTriangle ≫ t = yonedaEquiv.symm I.invHomId.simplex := by
  obtain ⟨t, ht, _⟩ := I.exists_joyalInterval_realization
  exact ⟨t, ht.1, ht.2.2.2.1, ht.2.2.2.2⟩

/-- The QC converse supplies exact forward, source and target maps. -/
theorem strictEndpoints {X : SSet.{u}} [Quasicategory X] {x₀ x₁ : X _⦋0⦌}
    {e : Edge x₀ x₁} (he : e.IsEquivalence) :
    ∃ t : joyalInterval.{u} ⟶ X,
      joyalInterval.forward ≫ t = yonedaEquiv.symm e.edge ∧
      joyalInterval.endpoint 0 ≫ t = yonedaEquiv.symm x₀ ∧
      joyalInterval.endpoint 1 ≫ t = yonedaEquiv.symm x₁ := by
  obtain ⟨t, ht⟩ := he.exists_joyalInterval_extension
  refine ⟨t, ht, ?_, ?_⟩
  · rw [joyalInterval.endpoint_zero, Category.assoc, ht]
    exact e.δ_one_yonedaEquiv_symm
  · rw [joyalInterval.endpoint_one, Category.assoc, ht]
    exact e.δ_zero_yonedaEquiv_symm

end SSet.FiniteJoyalIntervalEquivalencesTest
