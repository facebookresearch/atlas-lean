/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreKanProbe
import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreRightDerived
import MathlibExt.AlgebraicTopology.ModelCategory.GivenFactorizationReplacements

/-!
# Actual Joyal replacement mapping cores

Use the caller's SAME complete Q/R factor records on the named Joyal
model. The original core mapping object maps to core(Fun(Q A,R X)) by
the actual Q counit and R unit. At a genuine fibrant target this map is
Kan weak. Scalar localization identifies it with the canonical total
right-derived mapping row; no derived identification or weak core-map
equation is supplied as a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalCategory MonoidalClosed Opposite
open scoped JoyalSSet.ModelCategory Simplicial

namespace SSet.FunctorCore.Replacement

variable
  (dQ : FunctorialFactorizationData (cofibrations JoyalSSet.{u})
    (trivialFibrations JoyalSSet.{u}))
  (dR : FunctorialFactorizationData (trivialCofibrations JoyalSSet.{u})
    (fibrations JoyalSSet.{u}))

/-- The actual middle functor on the original initial-arrow family. -/
abbrev Q : JoyalSSet.{u} ⥤ JoyalSSet.{u} :=
  GivenFactorizationReplacements.initialReplacement dQ (⊥_ JoyalSSet.{u}) initialIsInitial

/-- Its original complete right factor. -/
abbrev q : Q dQ ⟶ 𝟭 JoyalSSet.{u} :=
  GivenFactorizationReplacements.initialProjection dQ (⊥_ JoyalSSet.{u}) initialIsInitial

/-- The actual middle functor on the original terminal-arrow family. -/
abbrev R : JoyalSSet.{u} ⥤ JoyalSSet.{u} :=
  GivenFactorizationReplacements.terminalReplacement dR (⊤_ JoyalSSet.{u}) terminalIsTerminal

/-- Its original complete left factor. -/
abbrev r : 𝟭 JoyalSSet.{u} ⟶ R dR :=
  GivenFactorizationReplacements.terminalUnit dR (⊤_ JoyalSSet.{u}) terminalIsTerminal

private theorem categorical_of_weak {A B : JoyalSSet.{u}} (f : A ⟶ B)
    (hf : weakEquivalences JoyalSSet.{u} f) : categoricalEquivalences (JoyalSSet.forget.map f) := by
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f at hf
  rw [JoyalSSet.modelCategory_weakEquivalences] at hf
  exact hf

/-- The source remains genuinely cofibrant at this actual factor record. -/
theorem Q_isCofibrant (A : JoyalSSet.{u}) : IsCofibrant ((Q dQ).obj A) :=
  GivenFactorizationReplacements.initialReplacement_isCofibrant JoyalSSet.modelCategory dQ
    (⊥_ JoyalSSet.{u}) initialIsInitial A

/-- The actual Q counit is a categorical equivalence of the original simplicial sets. -/
theorem q_categorical (A : JoyalSSet.{u}) :
    categoricalEquivalences (JoyalSSet.forget.map ((q dQ).app A)) :=
  categorical_of_weak _ (dQ.hp (CategoryTheory.Arrow.mk (initialIsInitial.to A))).2

/-- The actual R unit is a categorical equivalence of the original simplicial sets. -/
theorem r_categorical (X : JoyalSSet.{u}) :
    categoricalEquivalences (JoyalSSet.forget.map ((r dR).app X)) :=
  categorical_of_weak _ (dR.hi (CategoryTheory.Arrow.mk (terminalIsTerminal.from X))).2

/-- The target is quasicategorical by its actual named-model fibrancy. -/
theorem R_quasicategory (X : JoyalSSet.{u}) :
    Quasicategory (JoyalSSet.forget.obj ((R dR).obj X)) :=
  (JoyalSSet.isFibrant_iff_quasicategory _).mp
    (GivenFactorizationReplacements.terminalReplacement_isFibrant JoyalSSet.modelCategory dR
      (⊤_ JoyalSSet.{u}) terminalIsTerminal X)

/-- The literal full functor core between the actual cofibrant and fibrant model replacements. -/
def object (A X : JoyalSSet.{u}) : SSet.{u} :=
  (FunctorCore.functor (JoyalSSet.forget.obj ((Q dQ).obj A))).obj
    (JoyalSSet.forget.obj ((R dR).obj X))

/-- Both parameter maps retain the SAME original middle-functor maps. -/
def map {A B X Y : JoyalSSet.{u}} (f : A ⟶ B) (g : X ⟶ Y) :
    object dQ dR B X ⟶ object dQ dR A Y :=
  FunctorCore.mapBoth (JoyalSSet.forget.map ((Q dQ).map f))
    (JoyalSSet.forget.map ((R dR).map g))

/-- Both model mapping identity changes are the identity on the literal original core. -/
theorem map_id (A X : JoyalSSet.{u}) : map dQ dR (𝟙 A) (𝟙 X) = 𝟙 (object dQ dR A X) := by
  simp only [map, CategoryTheory.Functor.map_id]
  exact FunctorCore.mapBoth_id _ _

/-- Actual model source and target compositions retain both given middle functors. -/
theorem map_comp {A B C X Y Z : JoyalSSet.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    map dQ dR b f ≫ map dQ dR a g = map dQ dR (a ≫ b) (f ≫ g) := by
  rw [map, map, FunctorCore.mapBoth_comp, map]
  simp only [CategoryTheory.Functor.map_comp]

/-- The comparison consists of the SAME actual Q counit and R unit core maps. -/
def comparison (A X : JoyalSSet.{u}) :
    (FunctorCore.functor (JoyalSSet.forget.obj A)).obj (JoyalSSet.forget.obj X) ⟶
      object dQ dR A X :=
  FunctorCore.mapBoth (JoyalSSet.forget.map ((q dQ).app A))
    (JoyalSSet.forget.map ((r dR).app X))

/-- All model mapping spaces are Kan because the actual target replacements are fibrant. -/
theorem object_isKan (A X : JoyalSSet.{u}) : KanComplex (object dQ dR A X) := by
  let _ : Quasicategory (JoyalSSet.forget.obj ((R dR).obj X)) := R_quasicategory dR X
  exact FunctorCore.isKan _ _

/-- At every actual fibrant target the entire prescribed comparison is Kan weak. -/
theorem comparison_weak (A X : JoyalSSet.{u}) [IsFibrant X] :
    KanComplex.W (comparison dQ dR A X) := by
  let _ : Quasicategory (JoyalSSet.forget.obj X) :=
    (JoyalSSet.isFibrant_iff_quasicategory X).mp (inferInstance : IsFibrant X)
  let _ : Quasicategory (JoyalSSet.forget.obj ((R dR).obj X)) := R_quasicategory dR X
  exact FunctorCore.mapBoth_weak _ _ (q_categorical dQ A) (r_categorical dR X)

/-- The same entire original map is in the global Kan realization weak class. -/
theorem comparison_realizationWeak (A X : JoyalSSet.{u}) [IsFibrant X] :
    realizationWeakEquivalences (comparison dQ dR A X) := by
  let _ : Quasicategory (JoyalSSet.forget.obj X) :=
    (JoyalSSet.isFibrant_iff_quasicategory X).mp (inferInstance : IsFibrant X)
  let _ : KanComplex ((FunctorCore.functor (JoyalSSet.forget.obj A)).obj
      (JoyalSSet.forget.obj X)) := FunctorCore.isKan _ _
  let _ : KanComplex (object dQ dR A X) := object_isKan dQ dR A X
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mp (comparison_weak dQ dR A X)

/-- The actual Q/R squares give the complete two-variable comparison square. -/
theorem comparison_joint {A B X Y : JoyalSSet.{u}} (f : A ⟶ B) (g : X ⟶ Y) :
    FunctorCore.mapBoth (JoyalSSet.forget.map f) (JoyalSSet.forget.map g) ≫
        comparison dQ dR A Y = comparison dQ dR B X ≫ map dQ dR f g := by
  have hq := congrArg JoyalSSet.forget.map ((q dQ).naturality f)
  have hr := congrArg JoyalSSet.forget.map ((r dR).naturality g)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.id_map] at hq hr
  rw [comparison, comparison, map, FunctorCore.mapBoth_comp, FunctorCore.mapBoth_comp,
    ← hq, hr]

/-- Its original core inclusion retains both replacement maps before any localization. -/
theorem comparison_inclusion (A X : JoyalSSet.{u}) :
    comparison dQ dR A X ≫
        (core ((ihom (JoyalSSet.forget.obj ((Q dQ).obj A))).obj
          (JoyalSSet.forget.obj ((R dR).obj X)))).ι =
      (core ((ihom (JoyalSSet.forget.obj A)).obj (JoyalSSet.forget.obj X))).ι ≫
        (pre (JoyalSSet.forget.map ((q dQ).app A))).app (JoyalSSet.forget.obj X) ≫
          (ihom (JoyalSSet.forget.obj ((Q dQ).obj A))).map
            (JoyalSSet.forget.map ((r dR).app X)) :=
  FunctorCore.mapBoth_inclusion _ _

/-- Every original individual simplicial functor retains its exact two replacement legs. -/
theorem comparison_vertex (A X : JoyalSSet.{u}) (f : A.toSSet ⟶ X.toSSet) :
    (comparison dQ dR A X).app (op ⦋0⦌) (FunctorCore.vertex f) =
      FunctorCore.vertex (JoyalSSet.forget.map ((q dQ).app A) ≫ f ≫
        JoyalSSet.forget.map ((r dR).app X)) :=
  FunctorCore.mapBoth_vertex _ _ _

section ScalarLocalization

variable {E : Type w} [Category.{v} E]
  (L : SSet.{u} ⥤ E) [L.IsLocalization realizationWeakEquivalences.{u}]

/-- The actual replacement mapping core computes the SAME canonical right-derived row. -/
def derivedIso (A X : JoyalSSet.{u}) [IsFibrant X] :
    L.obj (object dQ dR A X) ≅
      (RightDerived.row L (JoyalSSet.forget.obj A)).obj (RightDerived.joyalLocalization.obj X) :=
  (Localization.isoOfHom L realizationWeakEquivalences (comparison dQ dR A X)
    (comparison_realizationWeak dQ dR A X)).symm ≪≫
      asIso ((RightDerived.unit L (JoyalSSet.forget.obj A)).app X)

/-- The same actual comparison and canonical unit form the entire recognition triangle. -/
theorem derivedIso_triangle (A X : JoyalSSet.{u}) [IsFibrant X] :
    L.map (comparison dQ dR A X) ≫ (derivedIso dQ dR L A X).hom =
      (RightDerived.unit L (JoyalSSet.forget.obj A)).app X := by
  let e := Localization.isoOfHom L realizationWeakEquivalences (comparison dQ dR A X)
    (comparison_realizationWeak dQ dR A X)
  change e.hom ≫ e.inv ≫ (RightDerived.unit L (JoyalSSet.forget.obj A)).app X = _
  rw [← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- Both original model maps retain the SAME derived source action and target map. -/
theorem derivedIso_joint {A B X Y : JoyalSSet.{u}} [IsFibrant X] [IsFibrant Y]
    (f : A ⟶ B) (g : X ⟶ Y) :
    L.map (map dQ dR f g) ≫ (derivedIso dQ dR L A Y).hom =
      (derivedIso dQ dR L B X).hom ≫ (RightDerived.source L (JoyalSSet.forget.map f)).app
        (RightDerived.joyalLocalization.obj X) ≫
          (RightDerived.row L (JoyalSSet.forget.obj A)).map
            (RightDerived.joyalLocalization.map g) := by
  let _ : IsIso (L.map (comparison dQ dR B X)) :=
    Localization.inverts L realizationWeakEquivalences _ (comparison_realizationWeak dQ dR B X)
  apply (cancel_epi (L.map (comparison dQ dR B X))).mp
  have hc := congrArg L.map (comparison_joint dQ dR f g)
  simp only [CategoryTheory.Functor.map_comp] at hc
  calc
    _ = (L.map (comparison dQ dR B X) ≫ L.map (map dQ dR f g)) ≫
        (derivedIso dQ dR L A Y).hom := (Category.assoc _ _ _).symm
    _ = (L.map (FunctorCore.mapBoth (JoyalSSet.forget.map f) (JoyalSSet.forget.map g)) ≫
        L.map (comparison dQ dR A Y)) ≫ (derivedIso dQ dR L A Y).hom :=
      congrArg (fun h => h ≫ (derivedIso dQ dR L A Y).hom) hc.symm
    _ = L.map (FunctorCore.mapBoth (JoyalSSet.forget.map f) (JoyalSSet.forget.map g)) ≫
        (RightDerived.unit L (JoyalSSet.forget.obj A)).app Y := by
      rw [Category.assoc, derivedIso_triangle]
    _ = (RightDerived.unit L (JoyalSSet.forget.obj B)).app X ≫
        (RightDerived.source L (JoyalSSet.forget.map f)).app
          (RightDerived.joyalLocalization.obj X) ≫
          (RightDerived.row L (JoyalSSet.forget.obj A)).map
            (RightDerived.joyalLocalization.map g) :=
      (RightDerived.unit_joint L (JoyalSSet.forget.map f) g).symm
    _ = _ := by
      rw [← derivedIso_triangle dQ dR L B X]
      simp only [Category.assoc]

/-- Change actual Q/R records through their SAME proved right-derived row. -/
def changeRecords
    (dQ' : FunctorialFactorizationData (cofibrations JoyalSSet.{u})
      (trivialFibrations JoyalSSet.{u}))
    (dR' : FunctorialFactorizationData (trivialCofibrations JoyalSSet.{u})
      (fibrations JoyalSSet.{u}))
    (A X : JoyalSSet.{u}) [IsFibrant X] :
    L.obj (object dQ dR A X) ≅ L.obj (object dQ' dR' A X) :=
  derivedIso dQ dR L A X ≪≫ (derivedIso dQ' dR' L A X).symm

/-- Replacement independence preserves the two actual original comparison maps. -/
theorem changeRecords_triangle
    (dQ' : FunctorialFactorizationData (cofibrations JoyalSSet.{u})
      (trivialFibrations JoyalSSet.{u}))
    (dR' : FunctorialFactorizationData (trivialCofibrations JoyalSSet.{u})
      (fibrations JoyalSSet.{u}))
    (A X : JoyalSSet.{u}) [IsFibrant X] :
    L.map (comparison dQ dR A X) ≫ (changeRecords dQ dR L dQ' dR' A X).hom =
      L.map (comparison dQ' dR' A X) := by
  apply (cancel_mono (derivedIso dQ' dR' L A X).hom).mp
  let e := derivedIso dQ dR L A X
  let e' := derivedIso dQ' dR' L A X
  change (L.map (comparison dQ dR A X) ≫ (e.hom ≫ e'.inv)) ≫ e'.hom =
    L.map (comparison dQ' dR' A X) ≫ e'.hom
  simp only [Category.assoc, e'.inv_hom_id, Category.comp_id]
  exact (derivedIso_triangle dQ dR L A X).trans (derivedIso_triangle dQ' dR' L A X).symm

end ScalarLocalization
end SSet.FunctorCore.Replacement
