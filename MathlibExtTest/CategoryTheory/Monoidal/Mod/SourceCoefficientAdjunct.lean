/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.Mod.SourceCoefficientAdjunct

/-!
# Full public clients of coefficient-source transport and adjuncts

These examples import the generic producer directly. The coefficient category,
enrichment category, index category, carrier category and output category remain
arbitrary with independent universes. All original maps and endpoint transports
are retained before evaluation or application of the supplied functors.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace SourceCoefficientAdjunctClient

section ArbitraryCarrier

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

example {M M' M'' : Mod C A.X} {X Y Z : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y)
    (et : M'' ≅ E.inverse.obj Z) (f : Z ⟶ Y) (g : Y ⟶ X) :
    NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow A E er et (f ≫ g) =
      NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow A E es et f ≫
        NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow A E er es g :=
  NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow_comp A E er es et f g

example {M M' : Mod C A.X} {X Y : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y) (f : Y ⟶ X) :
    E.inverse.map f = es.inv ≫
      NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow A E er es f ≫ er.hom :=
  NativeOmegaRecovery.ModuleFreeSourceTransport.sourceArrow_back A E er es f

end ArbitraryCarrier

section ArbitraryEnrichment

universe uC vC uV vV uJ uB vB
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (A : CommMon C) (E : Mod C A.X ≌ EnrichedFunctorCat V J)
  (b : J) (L : V ⥤ Mod C A.X) (e : L ≅ Free.functor b ⋙ E.inverse)

open NativeOmegaRecovery.ModuleFreeSourceTransport
open NativeOmegaRecovery.FreeAdjunctionCoefficientSource

example {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K) (g : Free.object b K ⟶ X) :
    sourceArrow A E er (e.app W) (Free.coefficientMap b f ≫ g) =
      L.map f ≫ sourceArrow A E er (e.app K) g :=
  sourceArrow_postCoefficient A E b L e er f g

example {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K) (g : Free.object b K ⟶ X) :
    E.inverse.map (Free.coefficientMap b f ≫ g) =
      (e.app W).inv ≫ (L.map f ≫ sourceArrow A E er (e.app K) g) ≫ er.hom :=
  sourceArrow_postCoefficient_back A E b L e er f g

variable {B : Type uB} [Category.{vB} B] (T : (Mod C A.X)ᵒᵖ ⥤ B)

example {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K) (g : Free.object b K ⟶ X) :
    (T.mapIso er.symm.op).hom ≫ T.map (E.inverse.map (Free.coefficientMap b f ≫ g)).op =
      T.map (L.map f ≫ sourceArrow A E er (e.app K) g).op ≫
        (T.mapIso (e.app W).symm.op).hom :=
  sourceComparison_postCoefficient A E b L e T er f g

example {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K) (g : Free.object b K ⟶ X) :
    T.map (E.inverse.map (Free.coefficientMap b f ≫ g)).op ≫
      (T.mapIso (e.app W).symm.op).inv =
      (T.mapIso er.symm.op).inv ≫ T.map (L.map f ≫ sourceArrow A E er (e.app K) g).op :=
  sourceComparison_postCoefficient_inv A E b L e T er f g

end ArbitraryEnrichment

section ArbitraryAdjunctions

universe uC vC uV vV uJ
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C) {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (E : Mod C A.X ≌ EnrichedFunctorCat V J)
  (a b : J) (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V) (adj : L ⊣ R)
  (r : E.functor ⋙ evaluation a ≅ R)
  (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V) (adj' : L' ⊣ R')
  (r' : E.functor ⋙ evaluation b ≅ R')

open NativeOmegaRecovery.ModuleFreeSourceTransport
open NativeOmegaRecovery.ModuleFreeAdjunctTransport

example (X Y : V) (f : Free.object b Y ⟶ Free.object a X) :
    adj'.homEquiv Y (L.obj X)
      (sourceArrow A E ((FreeAdjunctionSource.comparison E a L R adj r).app X)
        ((FreeAdjunctionSource.comparison E b L' R' adj' r').app Y) f) ≫
      r'.inv.app (L.obj X) =
      Free.evaluate b Y (Free.object a X) f ≫
        component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) b :=
  source_point_postcomp A E a b L R adj r L' R' adj' r' X Y f

example (X W K : V) (f : W ⟶ K) (g : Free.object b K ⟶ Free.object a X) :
    adj'.homEquiv W (L.obj X)
      (L'.map f ≫ sourceArrow A E ((FreeAdjunctionSource.comparison E a L R adj r).app X)
        ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K) g) ≫
      r'.inv.app (L.obj X) =
      f ≫ Free.evaluate b K (Free.object a X) g ≫
        component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) b :=
  source_point_postCoefficient A E a b L R adj r L' R' adj' r' X W K f g

example (X W K : V) (f : W ⟶ K) (g : Free.object b K ⟶ Free.object a X) :
    adj'.homEquiv W (L.obj X)
      (L'.map f ≫ sourceArrow A E ((FreeAdjunctionSource.comparison E a L R adj r).app X)
        ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K) g) =
      (f ≫ Free.evaluate b K (Free.object a X) g ≫
        component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) b) ≫
        r'.hom.app (L.obj X) :=
  source_point_postCoefficient_back A E a b L R adj r L' R' adj' r' X W K f g

example (e : L ⋙ E.functor ≅ Free.functor a)
    (he : e = FreeAdjunctionSource.operatorIso E a L R adj r)
    (X W K : V) (f : W ⟶ K) (g : Free.object b K ⟶ Free.object a X) :
    adj'.homEquiv W (L.obj X)
      (L'.map f ≫ sourceArrow A E ((FreeAdjunctionSource.comparison E a L R adj r).app X)
        ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K) g) =
      (f ≫ Free.evaluate b K (Free.object a X) g ≫ component (e.inv.app X) b) ≫
        r'.hom.app (L.obj X) :=
  source_point_postCoefficient_of_operatorIso A E a b L R adj r L' R' adj' r' e he X W K f g

end ArbitraryAdjunctions

section ArbitrarySquares

universe uB vB
variable {B : Type uB} [Category.{vB} B]

example {P Q P' Q' : B} (a a₀ : P ≅ Q) (b b₀ : P' ≅ Q')
    (p : Q ⟶ Q') (q : P ⟶ P') (ha : a = a₀) (hb : b = b₀)
    (h : a₀.hom ≫ p = q ≫ b₀.hom) : a.hom ≫ p = q ≫ b.hom :=
  NativeOmegaRecovery.WholeCoefficientSourceSquares.square_of_iso_eq a a₀ b b₀ p q ha hb h

example {P Q P' Q' P₀ Q₀ P₀' Q₀' : B}
    (a₀ : P₀ ≅ Q₀) (b₀ : P₀' ≅ Q₀') (a : P ≅ Q) (b : P' ≅ Q')
    (hP : P₀ = P) (hQ : Q₀ = Q) (hP' : P₀' = P') (hQ' : Q₀' = Q')
    (ha : (eqToIso hP).symm ≪≫ a₀ ≪≫ eqToIso hQ = a)
    (hb : (eqToIso hP').symm ≪≫ b₀ ≪≫ eqToIso hQ' = b)
    (p : Q ⟶ Q') (p₀ : Q₀ ⟶ Q₀') (hp : HEq p p₀)
    (q : P ⟶ P') (q₀ : P₀ ⟶ P₀') (hq : HEq q q₀)
    (h : a₀.hom ≫ p₀ = q₀ ≫ b₀.hom) : a.hom ≫ p = q ≫ b.hom :=
  NativeOmegaRecovery.WholeCoefficientSourceSquares.transport_square
    a₀ b₀ a b hP hQ hP' hQ' ha hb p p₀ hp q q₀ hq h

end ArbitrarySquares

section ArbitrarySourceFunctor

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

example (T : (Mod C A.X)ᵒᵖ ⥤ (D ⥤ D))
    (hT : T = NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E)
    {X Y : D} (f : X ⟶ Y) :
    HEq (NativeOmegaPreparation.ModuleFunctionTransport.precompose A E f)
      (T.map (E.inverse.map f).op) :=
  NativeOmegaRecovery.GivenModuleSourceFunctor.precompose_heq_map A E T hT f

end ArbitrarySourceFunctor

end SourceCoefficientAdjunctClient
