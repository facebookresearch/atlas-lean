/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents

/-!
# Subcomplexes selected by connected components

The canonical union of selected component subcomplexes retains every original
simplex and operator. Membership is exactly the selected zeroth-vertex label.
Maps respecting the component selectors preserve the same whole subcomplexes.
The Kan-fibration results use this common API from their model-category module.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- The literal union of the original component subcomplexes selected by S. -/
def componentUnion (X : SSet.{u}) (S : Set (π₀ X)) : X.Subcomplex :=
  ⨆ c : {c : π₀ X // c ∈ S}, π₀.component c.val

/-- Membership in every degree is the selected label of the original zeroth vertex. -/
theorem mem_componentUnion (X : SSet.{u}) (S : Set (π₀ X))
    (n : SimplexCategoryᵒᵖ) (q : X.obj n) :
    q ∈ (componentUnion X S).obj n ↔
      π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) ∈ S := by
  rw [componentUnion, Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨c, hc⟩, hq⟩
    change π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q) = c at hq
    rw [hq]
    exact hc
  · intro hq
    exact ⟨⟨π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q), hq⟩, rfl⟩

/-- An original vertex belongs exactly when its actual component is selected. -/
@[simp]
theorem mem_componentUnion_zero (X : SSet.{u}) (S : Set (π₀ X)) (x : X _⦋0⦌) :
    x ∈ (componentUnion X S).obj (op ⦋0⦌) ↔ π₀.mk x ∈ S := by
  rw [mem_componentUnion]
  have h : (⦋0⦌.const ⦋0⦌ 0) = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [h]
  simp

variable {X Y : SSet.{u}}

/-- Every SAME original scalar operator preserves the full component-selected simplex and original component
predicate. -/
theorem componentUnion_operator (P : π₀ X → Prop) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r)
    (a : X.obj q) (ha : a ∈ (componentUnion X P).obj q) :
    X.map f a ∈ (componentUnion X P).obj r := (componentUnion X P).map f ha

/-- Entire original simplex component selection is preserved by a full original scalar map respecting its actual
component predicates. -/
theorem componentUnion_map (f : X ⟶ Y) (P : π₀ X → Prop) (Q : π₀ Y → Prop)
    (h : ∀ c, P c → Q (mapπ₀ f c)) (q : SimplexCategoryᵒᵖ) (a : X.obj q)
    (ha : a ∈ (componentUnion X P).obj q) : f.app q a ∈ (componentUnion Y Q).obj q := by
  apply (mem_componentUnion Y Q q _).mpr
  have hc := h _ ((mem_componentUnion X P q a).mp ha)
  have hn := NatTrans.naturality_apply f (⦋0⦌.const q.unop 0).op a
  exact (congrArg Q ((mapπ₀_mk f _).trans (congrArg π₀.mk hn))).mp hc

end SSet
