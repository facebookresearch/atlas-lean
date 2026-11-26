/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import MathlibExt.CategoryTheory.Waldhausen.ApproximationProperty

/-!
# Mapping-cylinder cores and cofibration approximation

Let C have a zero object and WaldhausenCategoryWithoutGluing structure. A mapping-cylinder
core is a functor T : Arrow C ⥤ C with natural front, back and projection maps j_f : f.left →
T(f), k_f : f.right → T(f) and p_f : T(f) → f.right. They satisfy j_f ≫ p_f = f.hom and k_f ≫
p_f = id, and every j_f is a cofibration.

The Cylinder Axiom is the separate condition that all p_f are weak equivalences. For an exact
functor F : C ⥤ D satisfying the approximation property, it changes a factorization g = F(a) ≫
q with q weak into g = F(j_a) ≫ (F(p_a) ≫ q). The new source map is a cofibration and the new
target map is weak. The two category worlds remain independent.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]
variable [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]

/-- Functorial mapping-cylinder core.

For a category C with zero object and WaldhausenCategoryWithoutGluing structure, specify a
cylinder functor on Arrow C, natural front and back inclusions and a projection to the target.
The front-projection composite is the given arrow, the back-projection composite is identity,
and every front inclusion is a cofibration. -/
structure WaldhausenMappingCylinderCore
    (C : Type u₁) [Category.{v₁} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C] where
  /-- Mapping-cylinder object functor.

The core assigns a cylinder object T(f) to each arrow f and a cylinder map T(α) to each
commuting square α, as a functor Arrow C ⥤ C. -/
  functor : Arrow C ⥤ C
  /-- Natural front inclusion into a cylinder.

For an arrow f : X → Y, the front component j_f : X → T(f) is natural in commuting arrow
squares. -/
  front : Arrow.leftFunc ⟶ functor
  /-- Natural back inclusion into a cylinder.

For an arrow f : X → Y, the back component k_f : Y → T(f) is natural in commuting arrow
squares. -/
  back : Arrow.rightFunc ⟶ functor
  /-- Natural projection from a cylinder to the target.

For an arrow f : X → Y, the projection component p_f : T(f) → Y is natural in commuting arrow
squares. -/
  projection : functor ⟶ Arrow.rightFunc
  /-- Front-projection factorization of the arrow.

For every f : X → Y, the cylinder front j_f : X → T(f) and projection p_f : T(f) → Y satisfy
j_f ≫ p_f = f. These equations are an equality of natural transformations on Arrow C. -/
  front_projection : front ≫ projection = Arrow.leftToRight
  /-- Back-projection identity on the target.

For every f : X → Y, the cylinder back k_f : Y → T(f) and projection p_f : T(f) → Y satisfy
k_f ≫ p_f = id_Y. The identities are natural in arrow squares. -/
  back_projection : back ≫ projection =
    (𝟙 _ : (Arrow.rightFunc : Arrow C ⥤ C) ⟶ Arrow.rightFunc)
  /-- Cofibration of every cylinder front inclusion.

For each arrow f in C, the mapping-cylinder core requires its front map j_f : f.left → T(f) to
be a cofibration in the WaldhausenCategoryWithoutGluing structure. -/
  front_cofibration : ∀ f, IsCofibration (front.app f)

namespace WaldhausenMappingCylinderCore

/-- Cylinder Axiom for a mapping-cylinder core.

For a core T, require every projection p_f : T(f) → f.right to be a weak equivalence. This
predicate is separate from the core's front-cofibration and factorization data. -/
def SatisfiesCylinderAxiom
    (T : WaldhausenMappingCylinderCore C) : Prop :=
  ∀ f, IsWeakEquivalence (T.projection.app f)

/-- Cofibration approximation obtained from a mapping-cylinder core.

Let F : C ⥤ D be exact for the given WaldhausenCategoryWithoutGluing structures, satisfy the
approximation property, and let C have a cylinder core whose projections are weak. Every g :
F(X) → Y admits g = F(i) ≫ p with i a cofibration and p a weak equivalence. From g = F(a) ≫ q,
take i to be the front of T(a) and p = F(p_a) ≫ q. -/
theorem cofibrationApproximation_of_approximation
    {F : C ⥤ D} (hF : F.IsWaldhausenExact)
    (hApp : F.WaldhausenApproximationProperty)
    (T : WaldhausenMappingCylinderCore C)
    (hCyl : T.SatisfiesCylinderAxiom) :
    ∀ (X : C) (Y : D) (g : F.obj X ⟶ Y),
      ∃ (Xnext : C) (i : X ⟶ Xnext) (p : F.obj Xnext ⟶ Y),
        IsCofibration i ∧ IsWeakEquivalence p ∧ F.map i ≫ p = g := by
  intro X Y g
  obtain ⟨Xnext, a, p, hp, hfactor⟩ := hApp.factorization X Y g
  refine ⟨T.functor.obj (Arrow.mk a), T.front.app (Arrow.mk a),
    F.map (T.projection.app (Arrow.mk a)) ≫ p,
    T.front_cofibration (Arrow.mk a), ?_, ?_⟩
  · exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := D)).comp_mem _ _
      (hF.map_weakEquivalence _ (hCyl (Arrow.mk a))) hp
  · have hfront :
        T.front.app (Arrow.mk a) ≫
          T.projection.app (Arrow.mk a) = a := by
      simpa using congr_app T.front_projection (Arrow.mk a)
    erw [← Category.assoc, ← F.map_comp, hfront]
    exact hfactor

end WaldhausenMappingCylinderCore
end CategoryTheory

end
