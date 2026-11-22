/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.EquivalenceFunction

/-!
# Module precomposition transported through equivalence

For a commutative monoid in a braided closed category with equalizers and coequalizers,
transports source module arrows along a carrier equivalence. The function-object comparison
commutes with precomposition by every target-carrier morphism.
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

/-- Every original native source arrow is carried through the actual free-source
isomorphisms and original inverse carrier functor. -/
def sourceArrow {M M' : Mod C A.X} {X Y : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y) (f : Y ⟶ X) : M' ⟶ M :=
  es.hom ≫ E.inverse.map f ≫ er.inv

/-- The original source comparison is natural for every entire native source
arrow, retaining the full original contravariant internal-Hom transformation. -/
theorem sourceComparison_precompose {M M' : Mod C A.X} {X Y : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y) (f : Y ⟶ X) :
    (NativeOmegaPreparation.ModuleFunctionTransport.sourceComparison A E M X er).hom ≫
        NativeOmegaPreparation.ModuleFunctionTransport.precompose A E f =
      (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map
          (sourceArrow A E er es f).op ≫
        (NativeOmegaPreparation.ModuleFunctionTransport.sourceComparison A E M' Y es).hom := by
  let S := NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E
  let m := sourceArrow A E er es f
  have hm : es.inv ≫ m = E.inverse.map f ≫ er.inv := by
    dsimp only [m, sourceArrow]
    rw [← Category.assoc, es.inv_hom_id, Category.id_comp]
  change S.map er.inv.op ≫ S.map (E.inverse.map f).op =
    S.map m.op ≫ S.map es.inv.op
  rw [← S.map_comp, ← S.map_comp]
  change S.map (E.inverse.map f ≫ er.inv).op = S.map (es.inv ≫ m).op
  exact congrArg (fun z : E.inverse.obj Y ⟶ M => S.map z.op) hm.symm

end NativeOmegaRecovery.ModuleFreeSourceTransport
