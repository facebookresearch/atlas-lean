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
# Minimal mapping-cylinder core for approximation

This file isolates exactly the mapping-cylinder data needed to replace the
arbitrary source map supplied by literal Waldhausen `(App)` with a
cofibration.  The cylinder projection is required to be weak by a separate
predicate.

This core is deliberately not a full Waldhausen cylinder: it has no natural
zero-arrow normalization, coproduct cofibration, Cyl-I exactness, Stage
cylinder, or gluing data.  It installs no global instance and proves no
Approximation, comma, realization, or K-theory theorem.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]
variable [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]

/-- Minimal functorial mapping-cylinder data sufficient for one
cofibration-replacement calculation. -/
structure WaldhausenMappingCylinderCore
    (C : Type u₁) [Category.{v₁} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C] where
  /-- The mapping-cylinder object, functorial in an arrow. -/
  functor : Arrow C ⥤ C
  /-- Front inclusion from the source of the arrow. -/
  front : Arrow.leftFunc ⟶ functor
  /-- Back inclusion from the target of the arrow. -/
  back : Arrow.rightFunc ⟶ functor
  /-- Projection from the mapping cylinder to the target. -/
  projection : functor ⟶ Arrow.rightFunc
  /-- Front followed by projection is the original arrow. -/
  front_projection : front ≫ projection = Arrow.leftToRight
  /-- Back followed by projection is the identity. -/
  back_projection : back ≫ projection =
    (𝟙 _ : (Arrow.rightFunc : Arrow C ⥤ C) ⟶ Arrow.rightFunc)
  /-- Every front inclusion is a cofibration. -/
  front_cofibration : ∀ f, IsCofibration (front.app f)

namespace WaldhausenMappingCylinderCore

/-- The cylinder axiom for the minimal core: every projection is weak. -/
def SatisfiesCylinderAxiom
    (T : WaldhausenMappingCylinderCore C) : Prop :=
  ∀ f, IsWeakEquivalence (T.projection.app f)

/-- Literal approximation plus an exact functor and a weak mapping-cylinder
projection yields a cofibration-valued factorization.

The new weak map is `F.map projection ≫ p`; no saturation hypothesis is
needed. -/
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
