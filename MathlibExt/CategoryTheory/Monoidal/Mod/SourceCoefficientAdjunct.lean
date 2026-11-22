/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.FreeAdjunctTransport
import MathlibExt.CategoryTheory.Enriched.FreeLifting

/-!
# Coefficient naturality of transported module adjuncts

A given equivalence from modules over a commutative monoid transports arrows
through specified free-source isomorphisms. Transport respects composition
and coefficient maps, and returns the corresponding inverse-carrier maps.
For enriched free-evaluation adjunctions, these laws identify the adjunct
of a coefficient composite using the supplied evaluation isomorphisms.
The resulting comparison squares retain the chosen adjunctions, free-source
and operator isomorphisms, and the stated braided and enriched hypotheses.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.ModuleFreeSourceTransport

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

/-- Composition keeps all three given free-source isomorphisms and the same inverse carrier. -/
theorem sourceArrow_comp {M M' M'' : Mod C A.X} {X Y Z : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y)
    (et : M'' ≅ E.inverse.obj Z) (f : Z ⟶ Y) (g : Y ⟶ X) :
    sourceArrow A E er et (f ≫ g) =
      sourceArrow A E es et f ≫ sourceArrow A E er es g := by
  dsimp only [sourceArrow]
  rw [E.inverse.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Returning through the given isomorphisms recovers the entire inverse-carrier image. -/
theorem sourceArrow_back {M M' : Mod C A.X} {X Y : D}
    (er : M ≅ E.inverse.obj X) (es : M' ≅ E.inverse.obj Y) (f : Y ⟶ X) :
    E.inverse.map f = es.inv ≫ sourceArrow A E er es f ≫ er.hom := by
  dsimp only [sourceArrow]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end NativeOmegaRecovery.ModuleFreeSourceTransport

namespace NativeOmegaRecovery.FreeAdjunctionCoefficientSource

universe uC vC uV vV uJ
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (A : CommMon C) (E : Mod C A.X ≌ EnrichedFunctorCat V J)
  (b : J) (L : V ⥤ Mod C A.X) (e : L ≅ Free.functor b ⋙ E.inverse)

/-- A scalar map followed by any given free-source arrow retains its full original module
composite. -/
theorem sourceArrow_postCoefficient {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K)
    (g : Free.object b K ⟶ X) :
    ModuleFreeSourceTransport.sourceArrow A E er (e.app W)
        (Free.coefficientMap b f ≫ g) =
      L.map f ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g := by
  have hComp := ModuleFreeSourceTransport.sourceArrow_comp A E
    er (e.app K) (e.app W) (Free.coefficientMap b f) g
  have hCoeff : ModuleFreeSourceTransport.sourceArrow A E (e.app K) (e.app W)
      (Free.coefficientMap b f) = L.map f := by
    unfold ModuleFreeSourceTransport.sourceArrow
    simp only [Iso.app_hom, Iso.app_inv]
    exact NatIso.naturality_2 e f
  exact hComp.trans (congrArg
    (fun q => q ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g) hCoeff)

/-- Both original free isomorphisms return the same full inverse-carrier image of that composite. -/
theorem sourceArrow_postCoefficient_back {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K)
    (g : Free.object b K ⟶ X) :
    E.inverse.map (Free.coefficientMap b f ≫ g) =
      (e.app W).inv ≫
        (L.map f ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g) ≫ er.hom :=
  (ModuleFreeSourceTransport.sourceArrow_back A E er (e.app W)
    (Free.coefficientMap b f ≫ g)).trans
    (congrArg (fun q => (e.app W).inv ≫ q ≫ er.hom)
      (sourceArrow_postCoefficient A E b L e er f g))

universe uB vB
variable {B : Type uB} [Category.{vB} B] (T : (Mod C A.X)ᵒᵖ ⥤ B)

/-- Any given whole source functor retains the scalar and the actual inverse carrier map. -/
theorem sourceComparison_postCoefficient {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K)
    (g : Free.object b K ⟶ X) :
    (T.mapIso er.symm.op).hom ≫ T.map (E.inverse.map (Free.coefficientMap b f ≫ g)).op =
      T.map (L.map f ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g).op ≫
        (T.mapIso (e.app W).symm.op).hom := by
  have hm : (e.app W).inv ≫
      (L.map f ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g) =
      E.inverse.map (Free.coefficientMap b f ≫ g) ≫ er.inv := by
    rw [← sourceArrow_postCoefficient A E b L e er f g]
    dsimp only [ModuleFreeSourceTransport.sourceArrow]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change T.map er.inv.op ≫ T.map (E.inverse.map (Free.coefficientMap b f ≫ g)).op =
    T.map (L.map f ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g).op ≫
      T.map (e.app W).inv.op
  rw [← T.map_comp, ← T.map_comp]
  exact congrArg (fun q : E.inverse.obj (Free.object b W) ⟶ M => T.map q.op) hm.symm

/-- Both complete inverse maps belong to that same supplied whole source functor. -/
theorem sourceComparison_postCoefficient_inv {M : Mod C A.X} {X : EnrichedFunctorCat V J}
    (er : M ≅ E.inverse.obj X) {W K : V} (f : W ⟶ K)
    (g : Free.object b K ⟶ X) :
    T.map (E.inverse.map (Free.coefficientMap b f ≫ g)).op ≫
        (T.mapIso (e.app W).symm.op).inv =
      (T.mapIso er.symm.op).inv ≫
        T.map (L.map f ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g).op :=
  by
    let a := T.mapIso er.symm.op
    let c := T.mapIso (e.app W).symm.op
    let p := T.map (E.inverse.map (Free.coefficientMap b f ≫ g)).op
    let q := T.map (L.map f ≫ ModuleFreeSourceTransport.sourceArrow A E er (e.app K) g).op
    have h : a.hom ≫ p = q ≫ c.hom := sourceComparison_postCoefficient A E b L e T er f g
    have h' : a.hom ≫ (p ≫ c.inv) = q := by
      rw [← Category.assoc, h, Category.assoc, c.hom_inv_id, Category.comp_id]
    exact (Iso.eq_inv_comp a).2 h'

end NativeOmegaRecovery.FreeAdjunctionCoefficientSource

namespace NativeOmegaRecovery.ModuleFreeAdjunctTransport

universe uC vC uV vV uJ
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C) {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {J : Type uJ} [EnrichedCategory V J]
  (E : Mod C A.X ≌ EnrichedFunctorCat V J)

/-- The original full adjunct retains the actual inverse operator comparison and evaluation
endpoint. -/
theorem source_point_postcomp (a b : J) (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V)
    (adj : L ⊣ R) (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V)
    (adj' : L' ⊣ R') (r' : E.functor ⋙ evaluation b ≅ R')
    (X Y : V) (f : Free.object b Y ⟶ Free.object a X) :
    adj'.homEquiv Y (L.obj X)
        (ModuleFreeSourceTransport.sourceArrow A E
          ((FreeAdjunctionSource.comparison E a L R adj r).app X)
          ((FreeAdjunctionSource.comparison E b L' R' adj' r').app Y) f) ≫
      r'.inv.app (L.obj X) =
        Free.evaluate b Y (Free.object a X) f ≫
          component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) b :=
  (source_point A E a b L R adj r L' R' adj' r' X Y f).trans
    (Free.evaluate_postcomp b Y f
      ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X))

/-- The same full module adjunct of a scalar-source composite follows from the two original
adjunctions. -/
theorem source_point_postCoefficient (a b : J) (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V)
    (adj : L ⊣ R) (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V)
    (adj' : L' ⊣ R') (r' : E.functor ⋙ evaluation b ≅ R')
    (X W K : V) (f : W ⟶ K) (g : Free.object b K ⟶ Free.object a X) :
    adj'.homEquiv W (L.obj X)
        (L'.map f ≫ ModuleFreeSourceTransport.sourceArrow A E
          ((FreeAdjunctionSource.comparison E a L R adj r).app X)
          ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K) g) ≫
      r'.inv.app (L.obj X) =
        f ≫ Free.evaluate b K (Free.object a X) g ≫
          component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) b := by
  have hArrow := FreeAdjunctionCoefficientSource.sourceArrow_postCoefficient A E b L'
    (FreeAdjunctionSource.comparison E b L' R' adj' r')
    ((FreeAdjunctionSource.comparison E a L R adj r).app X) f g
  have hPoint := source_point_postcomp A E a b L R adj r L' R' adj' r' X W
    (Free.coefficientMap b f ≫ g)
  have hAdj := congrArg (fun q => adj'.homEquiv W (L.obj X) q ≫ r'.inv.app (L.obj X)) hArrow
  have hEval := Free.evaluate_precomp b (Free.object a X) f g
  simpa only [Category.assoc] using hAdj.symm.trans (hPoint.trans (congrArg (fun q => q ≫
    component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) b) hEval))

/-- Returning through the actual evaluation isomorphism retains the entire module adjunct. -/
theorem source_point_postCoefficient_back
    (a b : J) (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V)
    (adj : L ⊣ R) (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V)
    (adj' : L' ⊣ R') (r' : E.functor ⋙ evaluation b ≅ R')
    (X W K : V) (f : W ⟶ K) (g : Free.object b K ⟶ Free.object a X) :
    adj'.homEquiv W (L.obj X)
        (L'.map f ≫ ModuleFreeSourceTransport.sourceArrow A E
          ((FreeAdjunctionSource.comparison E a L R adj r).app X)
          ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K) g) =
      (f ≫ Free.evaluate b K (Free.object a X) g ≫
        component ((FreeAdjunctionSource.operatorIso E a L R adj r).inv.app X) b) ≫
          r'.hom.app (L.obj X) := by
  exact ((r'.app (L.obj X)).comp_inv_eq).mp
    (source_point_postCoefficient A E a b L R adj r L' R' adj' r' X W K f g)

/-- The complete given operator Iso is identified before any original adjunct component is
applied. -/
theorem source_point_postCoefficient_of_operatorIso (a b : J)
    (L : V ⥤ Mod C A.X) (R : Mod C A.X ⥤ V) (adj : L ⊣ R)
    (r : E.functor ⋙ evaluation a ≅ R)
    (L' : V ⥤ Mod C A.X) (R' : Mod C A.X ⥤ V) (adj' : L' ⊣ R')
    (r' : E.functor ⋙ evaluation b ≅ R')
    (e : L ⋙ E.functor ≅ Free.functor a)
    (he : e = FreeAdjunctionSource.operatorIso E a L R adj r)
    (X W K : V) (f : W ⟶ K) (g : Free.object b K ⟶ Free.object a X) :
    adj'.homEquiv W (L.obj X)
        (L'.map f ≫ ModuleFreeSourceTransport.sourceArrow A E
          ((FreeAdjunctionSource.comparison E a L R adj r).app X)
          ((FreeAdjunctionSource.comparison E b L' R' adj' r').app K) g) =
      (f ≫ Free.evaluate b K (Free.object a X) g ≫ component (e.inv.app X) b) ≫
        r'.hom.app (L.obj X) := by
  cases he
  exact source_point_postCoefficient_back A E a b L R adj r L' R' adj' r' X W K f g

end NativeOmegaRecovery.ModuleFreeAdjunctTransport


namespace NativeOmegaRecovery.WholeCoefficientSourceSquares
universe uB vB
variable {B : Type uB} [Category.{vB} B]

/-- Whole given comparison equalities are eliminated before either square is composed. -/
theorem square_of_iso_eq {P Q P' Q' : B} (a a₀ : P ≅ Q) (b b₀ : P' ≅ Q')
    (p : Q ⟶ Q') (q : P ⟶ P') (ha : a = a₀) (hb : b = b₀)
    (h : a₀.hom ≫ p = q ≫ b₀.hom) : a.hom ≫ p = q ≫ b.hom := by
  cases ha
  cases hb
  exact h

/-- The complete square is transported by the actual four endpoint equalities and two entire Iso
equalities. -/
theorem transport_square {P Q P' Q' P₀ Q₀ P₀' Q₀' : B}
    (a₀ : P₀ ≅ Q₀) (b₀ : P₀' ≅ Q₀') (a : P ≅ Q) (b : P' ≅ Q')
    (hP : P₀ = P) (hQ : Q₀ = Q) (hP' : P₀' = P') (hQ' : Q₀' = Q')
    (ha : (eqToIso hP).symm ≪≫ a₀ ≪≫ eqToIso hQ = a)
    (hb : (eqToIso hP').symm ≪≫ b₀ ≪≫ eqToIso hQ' = b)
    (p : Q ⟶ Q') (p₀ : Q₀ ⟶ Q₀') (hp : HEq p p₀)
    (q : P ⟶ P') (q₀ : P₀ ⟶ P₀') (hq : HEq q q₀)
    (h : a₀.hom ≫ p₀ = q₀ ≫ b₀.hom) : a.hom ≫ p = q ≫ b.hom := by
  cases hP
  cases hQ
  cases hP'
  cases hQ'
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl] at ha hb
  cases ha
  cases hb
  cases eq_of_heq hp
  cases eq_of_heq hq
  exact h

end NativeOmegaRecovery.WholeCoefficientSourceSquares

namespace NativeOmegaRecovery.GivenModuleSourceFunctor
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  (A : CommMon C) {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)

/-- The equality of the entire actual source functor is eliminated before its native map is read. -/
theorem precompose_heq_map (T : (Mod C A.X)ᵒᵖ ⥤ (D ⥤ D))
    (hT : T = NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E)
    {X Y : D} (f : X ⟶ Y) :
    HEq (NativeOmegaPreparation.ModuleFunctionTransport.precompose A E f)
      (T.map (E.inverse.map f).op) := by
  cases hT
  exact HEq.rfl

end NativeOmegaRecovery.GivenModuleSourceFunctor
