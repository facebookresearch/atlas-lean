/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeSourceTransport

/-!
# Carrier comparisons under a module equivalence

An equivalence from a commutative module category sends a source
isomorphism to its image followed by the equivalence counit. The transported
source arrow intertwines these carrier comparisons, and the inverse formula
retains the same source arrow and inverse comparison maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory Limits

namespace NativeOmegaRecovery.ModuleFreeSourceTransport
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

omit [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]

/-- The original carrier image of a genuine source iso keeps the original counit. -/
def operatorComparison {M : Mod C A.X} {X : D} (e : M ≅ E.inverse.obj X) :
    E.functor.obj M ≅ X := E.functor.mapIso e ≪≫ E.counitIso.app X

/-- Every whole original source arrow has the same actual conjugated operator
map under the source comparisons and original carrier counit. -/
theorem operatorComparison_source {M M' : Mod C A.X} {X Y : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y) (f : Y ⟶ X) :
    E.functor.map (sourceArrow A E er es f) ≫ (operatorComparison A E er).hom =
      (operatorComparison A E es).hom ≫ f := by
  dsimp only [sourceArrow, operatorComparison]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hCancel : E.functor.map er.inv ≫ E.functor.map er.hom = 𝟙 _ :=
    (E.functor.map_comp er.inv er.hom).symm.trans
      ((congrArg E.functor.map er.inv_hom_id).trans (E.functor.map_id _))
  rw [reassoc_of% hCancel]
  exact congrArg (fun z => E.functor.map es.hom ≫ z) (E.counitIso.hom.naturality f)

/-- The original inverse source comparison retains that same whole source arrow. -/
theorem operatorComparison_inv_source {M M' : Mod C A.X} {X Y : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y) (f : Y ⟶ X) :
    (operatorComparison A E es).inv ≫ E.functor.map (sourceArrow A E er es f) =
      f ≫ (operatorComparison A E er).inv := by
  let e := operatorComparison A E er
  let es' := operatorComparison A E es
  let m := E.functor.map (sourceArrow A E er es f)
  have h : m ≫ e.hom = es'.hom ≫ f := operatorComparison_source A E er es f
  have hPost := congrArg (fun z : E.functor.obj M' ⟶ X => z ≫ e.inv) h
  have hm : m = es'.hom ≫ f ≫ e.inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hPost
  change es'.inv ≫ m = f ≫ e.inv
  rw [hm, ← Category.assoc, es'.inv_hom_id, Category.id_comp]

end NativeOmegaRecovery.ModuleFreeSourceTransport
