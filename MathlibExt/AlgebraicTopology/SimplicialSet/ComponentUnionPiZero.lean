/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ComponentUnionSubcomplex

/-!
# Actual component-map injection for the whole selected original components

Every original native component chain between selected original vertices
stays in the SAME selected full components. Original edges and all chain
steps lift literally to the subcomplex. Its component inclusion is
injective, and its image is precisely the supplied original predicate.
No Kan condition or weak-map conclusion is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {X : SSet.{u}} (P : π₀ X → Prop)

private theorem selected_of_chain {x y : X _⦋0⦌} (h : Relation.EqvGen π₀Rel x y)
    (hx : x ∈ (componentUnion X P).obj (op ⦋0⦌)) : y ∈ (componentUnion X P).obj (op ⦋0⦌) := by
  apply (mem_componentUnion_zero X P y).mpr
  exact (congrArg P ((π₀.mk_eq_mk_iff x y).mpr h)).mp ((mem_componentUnion_zero X P x).mp hx)

private theorem selected_chain_eq {x y : X _⦋0⦌} (h : Relation.EqvGen π₀Rel x y)
    (hx : x ∈ (componentUnion X P).obj (op ⦋0⦌)) (hy : y ∈ (componentUnion X P).obj (op ⦋0⦌)) :
    π₀.mk (⟨x, hx⟩ : (componentUnion X P : SSet.{u}) _⦋0⦌) =
      π₀.mk (X := (componentUnion X P : SSet.{u})) (⟨y, hy⟩ : (componentUnion X P : SSet.{u}) _⦋0⦌) := by
  induction h with
  | rel x y h =>
    obtain ⟨e⟩ := h
    have he : e.edge ∈ (componentUnion X P).obj (op ⦋1⦌) := by
      apply (mem_componentUnion X P (op ⦋1⦌) _).mpr
      rw [← SimplexCategory.δ_one_eq_const]
      change P (π₀.mk (X.δ 1 e.edge))
      rw [e.src_eq]
      exact (mem_componentUnion_zero X P x).mp hx
    exact π₀.sound ((e.toSubcomplex (componentUnion X P) he).ofEq
      (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl))
  | refl => rfl
  | symm x y h ih => exact (ih hy hx).symm
  | trans x y z hxy hyz ihxy ihyz =>
    let hy' := selected_of_chain P hxy hx
    exact (ihxy hx hy').trans (ihyz hy' hy)

/-- The SAME full original selected-component inclusion is injective on actual native component classes. -/
theorem componentUnion_piZero_injective : Function.Injective (mapπ₀ (componentUnion X P).ι) := by
  intro a b h
  obtain ⟨⟨x, hx⟩, rfl⟩ := π₀.mk_surjective a
  obtain ⟨⟨y, hy⟩, rfl⟩ := π₀.mk_surjective b
  have hxy : π₀.mk x = π₀.mk y := h
  exact selected_chain_eq P ((π₀.mk_eq_mk_iff x y).mp hxy) hx hy

/-- Every SAME original selected component class satisfies the supplied predicate in the original Hom. -/
theorem componentUnion_piZero_selected (a : π₀ (componentUnion X P : SSet.{u})) :
    P (mapπ₀ (componentUnion X P).ι a) := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := π₀.mk_surjective a
  exact (mem_componentUnion_zero X P x).mp hx

/-- Every original native component satisfying the predicate has an actual selected original component preimage. -/
theorem componentUnion_piZero_surjective_on (a : π₀ X) (ha : P a) :
    ∃ b : π₀ (componentUnion X P : SSet.{u}), mapπ₀ (componentUnion X P).ι b = a := by
  obtain ⟨x, rfl⟩ := π₀.mk_surjective a
  exact ⟨π₀.mk ⟨x, (mem_componentUnion_zero X P x).mpr ha⟩, rfl⟩

end SSet
