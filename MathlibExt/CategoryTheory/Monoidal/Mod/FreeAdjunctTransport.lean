/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeCarrierSourceTransport
public import MathlibExt.CategoryTheory.Enriched.FreeAdjunctionSource

/-!
# Free adjuncts under module-operator comparison

A supplied module-to-enriched-diagram equivalence and free-evaluation adjunctions identify
the transported module free comparison with the operator comparison. The adjunct of a
free-source arrow is the corresponding native free evaluation after the specified inverse
comparison. The formulas retain both source comparisons and the evaluation isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uC vC uV vV uJ
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaRecovery.ModuleFreeAdjunctTransport
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C)
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (E : Mod C A.X ≌ EnrichedFunctorCat V J)

/-- The source comparison carried to operators has exactly the original
free-adjunction comparison and carrier counit. -/
theorem operatorComparison_eq (a : J) (L : V ⥤ Mod C A.X)
    (R : Mod C A.X ⥤ V) (adj : L ⊣ R)
    (r : E.functor ⋙ evaluation a ≅ R) (X : V) :
    ModuleFreeSourceTransport.operatorComparison A E
      ((FreeAdjunctionSource.comparison E a L R adj r).app X) =
        (FreeAdjunctionSource.operatorIso E a L R adj r).app X := by
  rw [FreeAdjunctionSource.operatorIso_eq E a L R adj r]
  apply Iso.ext
  simp only [Iso.app_hom, ModuleFreeSourceTransport.operatorComparison, Iso.trans_hom,
    Functor.mapIso_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    FreeAdjunctionSource.nativeIso_hom_app]

/-- Every whole native free source arrow has the actual original adjunct,
with its complete inverse source comparison and original carrier counit. -/
theorem source_point (a b : J) (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V)
    (adj : L ⊣ R) (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V)
    (adj' : L' ⊣ R') (r' : E.functor ⋙ evaluation b ≅ R')
    (X Y : V) (f : Free.object b Y ⟶ Free.object a X) :
    adj'.homEquiv Y (L.obj X)
        (ModuleFreeSourceTransport.sourceArrow A E
          ((FreeAdjunctionSource.comparison E a L R adj r).app X)
          ((FreeAdjunctionSource.comparison E b L' R' adj' r').app Y) f) ≫
      r'.inv.app (L.obj X) =
        Free.evaluate b Y (E.functor.obj (L.obj X))
          (f ≫ (FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) := by
  let er := (FreeAdjunctionSource.comparison E a L R adj r).app X
  let es := (FreeAdjunctionSource.comparison E b L' R' adj' r').app Y
  let m := ModuleFreeSourceTransport.sourceArrow A E er es f
  have hp := FreeAdjunctionSource.point E b L' R' adj' r' m
  have hOp := ModuleFreeSourceTransport.operatorComparison_inv_source A E er es f
  have her := operatorComparison_eq A E a L R adj r X
  have hes := operatorComparison_eq A E b L' R' adj' r' Y
  have hArrow : (FreeAdjunctionSource.operatorIso E b L' R' adj' r').inv.app Y ≫
      E.functor.map m = f ≫
        (FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X := by
    simpa only [er, es, m, her, hes, Iso.app_inv] using hOp
  exact hp.trans (congrArg (Free.evaluate b Y (E.functor.obj (L.obj X))) hArrow)

end NativeOmegaRecovery.ModuleFreeAdjunctTransport
