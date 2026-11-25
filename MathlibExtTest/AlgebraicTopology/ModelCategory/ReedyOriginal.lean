/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.AlgebraicTopology.ModelCategory.ReedyGenerated
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uS vS

section OriginalClientPart1

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace ReedyOriginalClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

@[instance_reducible]
def actual_model : ModelCategory (J ⥤ C) := ReedyModel.modelCategory r Fc Ff

theorem weak_class :
    letI := ReedyModel.modelCategory r Fc Ff
    weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J :=
  ReedyModel.weakEquivalences_eq r Fc Ff

theorem cof_class :
    letI := ReedyModel.modelCategory r Fc Ff
    cofibrations (J ⥤ C) = CategoryTheory.ReedyStructure.latchingClass r (cofibrations C) :=
  ReedyModel.cofibrations_eq r Fc Ff

theorem fib_class :
    letI := ReedyModel.modelCategory r Fc Ff
    fibrations (J ⥤ C) = CategoryTheory.ReedyStructure.matchingClass r (fibrations C) :=
  ReedyModel.fibrations_eq r Fc Ff

theorem trivial_cof_class :
    letI := ReedyModel.modelCategory r Fc Ff
    trivialCofibrations (J ⥤ C) = CategoryTheory.ReedyStructure.latchingClass r (trivialCofibrations C) :=
  ReedyModel.trivialCofibrations_eq r Fc Ff

theorem trivial_fib_class :
    letI := ReedyModel.modelCategory r Fc Ff
    trivialFibrations (J ⥤ C) = CategoryTheory.ReedyStructure.matchingClass r (trivialFibrations C) :=
  ReedyModel.trivialFibrations_eq r Fc Ff

theorem cof_middle_original :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).Z =
      CategoryTheory.ReedyStructure.FunctorialConstruction.middle r Fc := rfl

theorem cof_left_original :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).i =
      CategoryTheory.ReedyStructure.FunctorialConstruction.left r Fc := rfl

theorem cof_right_original :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).p =
      CategoryTheory.ReedyStructure.FunctorialConstruction.right r Fc := rfl

theorem fib_middle_original :
    (ReedyModel.fibrantFactorizationData r Fc Ff).Z =
      CategoryTheory.ReedyStructure.FunctorialConstruction.middle r Ff := rfl

theorem fib_left_original :
    (ReedyModel.fibrantFactorizationData r Fc Ff).i =
      CategoryTheory.ReedyStructure.FunctorialConstruction.left r Ff := rfl

theorem fib_right_original :
    (ReedyModel.fibrantFactorizationData r Fc Ff).p =
      CategoryTheory.ReedyStructure.FunctorialConstruction.right r Ff := rfl

theorem cof_full_fac :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).i ≫ (ReedyModel.cofibrantFactorizationData r Fc Ff).p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (ReedyModel.cofibrantFactorizationData r Fc Ff).fac

theorem fib_full_fac :
    (ReedyModel.fibrantFactorizationData r Fc Ff).i ≫ (ReedyModel.fibrantFactorizationData r Fc Ff).p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (ReedyModel.fibrantFactorizationData r Fc Ff).fac

theorem cof_fac (a : Arrow (J ⥤ C)) :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a ≫
      (ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a = a.hom :=
  (ReedyModel.cofibrantFactorizationData r Fc Ff).fac_app

theorem fib_fac (a : Arrow (J ⥤ C)) :
    (ReedyModel.fibrantFactorizationData r Fc Ff).i.app a ≫
      (ReedyModel.fibrantFactorizationData r Fc Ff).p.app a = a.hom :=
  (ReedyModel.fibrantFactorizationData r Fc Ff).fac_app

theorem cof_i_class (a : Arrow (J ⥤ C)) :
    ∀ j : J, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r ((ReedyModel.cofibrantFactorizationData r Fc
      Ff).i.app a) j) :=
  (ReedyModel.cofibrantFactorizationData r Fc Ff).hi a

theorem cof_p_class (a : Arrow (J ⥤ C)) :
    ∀ j : J, trivialFibrations C
      (CategoryTheory.ReedyStructure.matchingCorner r ((ReedyModel.cofibrantFactorizationData r Fc
      Ff).p.app a) j) :=
  (ReedyModel.trivialFibration_iff_source r Fc Ff _).mp ((ReedyModel.cofibrantFactorizationData r Fc Ff).hp a)

theorem fib_i_class (a : Arrow (J ⥤ C)) :
    ∀ j : J, trivialCofibrations C
      (CategoryTheory.ReedyStructure.latchingCorner r ((ReedyModel.fibrantFactorizationData r Fc
      Ff).i.app a) j) :=
  (ReedyModel.trivialCofibration_iff_source r Fc Ff _).mp ((ReedyModel.fibrantFactorizationData r Fc Ff).hi a)

theorem fib_p_class (a : Arrow (J ⥤ C)) :
    ∀ j : J, fibrations C
      (CategoryTheory.ReedyStructure.matchingCorner r ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app a) j) :=
  (ReedyModel.fibrantFactorizationData r Fc Ff).hp a

theorem cof_square_left {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a ≫
      (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map s =
        s.left ≫ (ReedyModel.cofibrantFactorizationData r Fc Ff).i.app b :=
  ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.naturality s).symm

theorem cof_square_right {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map s ≫
      (ReedyModel.cofibrantFactorizationData r Fc Ff).p.app b =
        (ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a ≫ s.right :=
  (ReedyModel.cofibrantFactorizationData r Fc Ff).p.naturality s

theorem fib_square_left {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (ReedyModel.fibrantFactorizationData r Fc Ff).i.app a ≫
      (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map s =
        s.left ≫ (ReedyModel.fibrantFactorizationData r Fc Ff).i.app b :=
  ((ReedyModel.fibrantFactorizationData r Fc Ff).i.naturality s).symm

theorem fib_square_right {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map s ≫
      (ReedyModel.fibrantFactorizationData r Fc Ff).p.app b =
        (ReedyModel.fibrantFactorizationData r Fc Ff).p.app a ≫ s.right :=
  (ReedyModel.fibrantFactorizationData r Fc Ff).p.naturality s

theorem cof_middle_id (a : Arrow (J ⥤ C)) :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map (𝟙 a) =
      𝟙 ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a) :=
  (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map_id a

theorem fib_middle_id (a : Arrow (J ⥤ C)) :
    (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map (𝟙 a) =
      𝟙 ((ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj a) :=
  (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map_id a

theorem cof_middle_comp {a b c : Arrow (J ⥤ C)} (s : a ⟶ b) (t : b ⟶ c) :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map (s ≫ t) =
      (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map s ≫
        (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map t :=
  (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.map_comp s t

theorem fib_middle_comp {a b c : Arrow (J ⥤ C)} (s : a ⟶ b) (t : b ⟶ c) :
    (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map (s ≫ t) =
      (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map s ≫
        (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map t :=
  (ReedyModel.fibrantFactorizationData r Fc Ff).Z.map_comp s t

theorem cof_original_arrow_left (a : Arrow (J ⥤ C)) {i j : J} (g : i ⟶ j) :
    a.left.map g ≫ ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a).app j =
      ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a).app i ≫
        ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a).map g :=
  ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a).naturality g

theorem fib_original_arrow_right (a : Arrow (J ⥤ C)) {i j : J} (g : i ⟶ j) :
    ((ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj a).map g ≫
      ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app a).app j =
        ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app a).app i ≫ a.right.map g :=
  ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app a).naturality g

theorem cof_original_arrow_right (a : Arrow (J ⥤ C)) {i j : J} (g : i ⟶ j) :
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a).map g ≫
      ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a).app j =
        ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a).app i ≫ a.right.map g :=
  ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a).naturality g

theorem fib_original_arrow_left (a : Arrow (J ⥤ C)) {i j : J} (g : i ⟶ j) :
    a.left.map g ≫ ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a).app j =
      ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a).app i ≫
        ((ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj a).map g :=
  ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a).naturality g

def cof_factory_object (a : Arrow (J ⥤ C)) (j : J) :
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a).obj j ≅
      (CategoryTheory.ReedyStructure.FunctorialConstruction.stageCoefficient r Fc j).Z.obj a :=
  CategoryTheory.ReedyStructure.FunctorialConstruction.coefficientObjectIso r Fc a j

def fib_factory_object (a : Arrow (J ⥤ C)) (j : J) :
    ((ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj a).obj j ≅
      (CategoryTheory.ReedyStructure.FunctorialConstruction.stageCoefficient r Ff j).Z.obj a :=
  CategoryTheory.ReedyStructure.FunctorialConstruction.coefficientObjectIso r Ff a j

theorem coefficient_left_factory (a : Arrow (J ⥤ C)) (j : J) :
    (CategoryTheory.ReedyStructure.FunctorialConstruction.stageCoefficient r Fc j).i.app a =
      Fc.i.app (Arrow.mk ((CategoryTheory.ReedyStructure.FunctorialConstruction.stageMap r Fc j).app a)) :=
  CategoryTheory.ReedyStructure.FunctorialConstruction.stageCoefficient_i r Fc a j

theorem coefficient_right_factory (a : Arrow (J ⥤ C)) (j : J) :
    (CategoryTheory.ReedyStructure.FunctorialConstruction.stageCoefficient r Ff j).p.app a =
      Ff.p.app (Arrow.mk ((CategoryTheory.ReedyStructure.FunctorialConstruction.stageMap r Ff j).app a)) :=
  CategoryTheory.ReedyStructure.FunctorialConstruction.stageCoefficient_p r Ff a j

@[instance_reducible]
def arbitrary_ordinal_model {α : Ordinal.{uD}} (rO : CategoryTheory.ReedyStructure J α.ToType)
    [∀ j, HasLimitsOfShape (rO.Matching j) C] [∀ j, HasColimitsOfShape (rO.Latching j) C] : ModelCategory (J ⥤ C) :=
  ReedyModel.modelCategory rO Fc Ff

section CallerLatching

variable (a : Arrow (J ⥤ C))
  (cX : ∀ j : J, Cocone (r.latchingDiagram a.left j)) (hX : ∀ j : J, IsColimit (cX j))
  (cZ : ∀ j : J, Cocone (r.latchingDiagram ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a) j))
  (hZ : ∀ j : J, IsColimit (cZ j))
  (cP : ∀ j : J, PushoutCocone (r.latchingMapWith a.left j (cX j) (hX j))
    (r.latchingComparisonWith ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a) j
      (cX j) (hX j) (cZ j))) (hP : ∀ j : J, IsColimit (cP j))

theorem cof_actual_chosen_corners : ∀ j : J, cofibrations C
    (r.latchingCornerWith ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a) j
      (cX j) (hX j) (cZ j) (hZ j) (cP j) (hP j)) :=
  (ReedyModel.cofibration_iff_chosen r Fc Ff _ cX hX cZ hZ cP hP).mp
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).hi a)

end CallerLatching

section CallerMatching

variable (a : Arrow (J ⥤ C))
  (cZ : ∀ j : J, Cone (r.matchingDiagram ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a) j))
  (hZ : ∀ j : J, IsLimit (cZ j))
  (cY : ∀ j : J, Cone (r.matchingDiagram a.right j)) (hY : ∀ j : J, IsLimit (cY j))
  (cP : ∀ j : J, PullbackCone
    (r.matchingComparisonWith ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a) j
      (cZ j) (cY j) (hY j)) (r.matchingMapWith a.right j (cY j) (hY j)))
  (hP : ∀ j : J, IsLimit (cP j))

theorem cof_actual_chosen_trivial_corners : ∀ j : J, trivialFibrations C
    (r.matchingCornerWith ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a) j
      (cZ j) (hZ j) (cY j) (hY j) (cP j) (hP j)) :=
  (ReedyModel.trivialFibration_iff_chosen r Fc Ff _ cZ hZ cY hY cP hP).mp
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).hp a)

end CallerMatching

section Generated

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType] (d : CofibrantGenerationData C κ)

@[instance_reducible]
def original_generated_model : ModelCategory (J ⥤ C) := ReedyModel.generatedModelCategory r d

theorem generated_left_original :
    (ReedyModel.generatedCofibrantFactorizationData r d).Z =
      CategoryTheory.ReedyStructure.FunctorialConstruction.middle r d.cofibrantFactorizationData := rfl

theorem generated_right_original :
    (ReedyModel.generatedFibrantFactorizationData r d).Z =
      CategoryTheory.ReedyStructure.FunctorialConstruction.middle r d.fibrantFactorizationData := rfl

end Generated

end ReedyOriginalClients

namespace ReedyZeroUniverseClients

variable {J C : Type} [Category.{0} J] [Category.{0} C] [ModelCategory C]
    (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

@[instance_reducible]
def ordinal_model (α : Ordinal.{0}) (r : CategoryTheory.ReedyStructure J α.ToType)
    [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C] : ModelCategory (J ⥤ C) :=
  ReedyModel.modelCategory r Fc Ff

theorem full_left_factor (α : Ordinal.{0}) (r : CategoryTheory.ReedyStructure J α.ToType)
    [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C] :
    letI := ReedyModel.modelCategory r Fc Ff
    (ReedyModel.cofibrantFactorizationData r Fc Ff).i ≫ (ReedyModel.cofibrantFactorizationData r Fc Ff).p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (ReedyModel.cofibrantFactorizationData r Fc Ff).fac

theorem full_right_factor (α : Ordinal.{0}) (r : CategoryTheory.ReedyStructure J α.ToType)
    [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C] :
    letI := ReedyModel.modelCategory r Fc Ff
    (ReedyModel.fibrantFactorizationData r Fc Ff).i ≫ (ReedyModel.fibrantFactorizationData r Fc Ff).p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (ReedyModel.fibrantFactorizationData r Fc Ff).fac

end ReedyZeroUniverseClients

end OriginalClientPart1

section OriginalClientPart2

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open CategoryTheory.ReedyStructure CategoryTheory.ReedyStructure.FunctorialConstruction

namespace ReedyFactoryClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

theorem cof_original_factory_i (a : Arrow (J ⥤ C)) (j : J) :
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a).app j ≫ (coefficientObjectIso r Fc a j).hom =
      (pushout.inl (CategoryTheory.ReedyStructure.latchingMap r (universalLeft (J := J) (C := C)) j)
        (StageFactory.latchingI r (universalMap (J := J) (C := C)) (stageLower r Fc j) j rfl)).app a ≫
        Fc.i.app (Arrow.mk ((stageMap r Fc j).app a)) := data_i_factory r Fc a j

theorem cof_original_factory_p (a : Arrow (J ⥤ C)) (j : J) :
    (coefficientObjectIso r Fc a j).hom ≫
      (Fc.p.app (Arrow.mk ((stageMap r Fc j).app a)) ≫
        (pullback.snd (StageFactory.matchingP r (universalMap (J := J) (C := C)) (stageLower r Fc j) j rfl)
          (CategoryTheory.ReedyStructure.matchingMap r (universalRight (J := J) (C := C)) j)).app a) =
      ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app a).app j := data_p_factory_projection r Fc a j

theorem fib_original_factory_i (a : Arrow (J ⥤ C)) (j : J) :
    ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a).app j ≫ (coefficientObjectIso r Ff a j).hom =
      (pushout.inl (CategoryTheory.ReedyStructure.latchingMap r (universalLeft (J := J) (C := C)) j)
        (StageFactory.latchingI r (universalMap (J := J) (C := C)) (stageLower r Ff j) j rfl)).app a ≫
        Ff.i.app (Arrow.mk ((stageMap r Ff j).app a)) := data_i_factory r Ff a j

theorem fib_original_factory_p (a : Arrow (J ⥤ C)) (j : J) :
    (coefficientObjectIso r Ff a j).hom ≫
      (Ff.p.app (Arrow.mk ((stageMap r Ff j).app a)) ≫
        (pullback.snd (StageFactory.matchingP r (universalMap (J := J) (C := C)) (stageLower r Ff j) j rfl)
          (CategoryTheory.ReedyStructure.matchingMap r (universalRight (J := J) (C := C)) j)).app a) =
      ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app a).app j := data_p_factory_projection r Ff a j

theorem cof_original_factory_square {a b : Arrow (J ⥤ C)} (s : a ⟶ b) (j : J) :
    (stageCoefficient r Fc j).Z.map s = Fc.Z.map (Arrow.homMk
      ((StageFactory.coefficientSource r (universalMap (J := J) (C := C)) (stageLower r Fc j) j rfl).map s)
      ((StageFactory.coefficientTarget r (universalMap (J := J) (C := C)) (stageLower r Fc j) j rfl).map s)
      (stageMap_square r Fc s j)) := stageCoefficient_map r Fc s j

theorem fib_original_factory_square {a b : Arrow (J ⥤ C)} (s : a ⟶ b) (j : J) :
    (stageCoefficient r Ff j).Z.map s = Ff.Z.map (Arrow.homMk
      ((StageFactory.coefficientSource r (universalMap (J := J) (C := C)) (stageLower r Ff j) j rfl).map s)
      ((StageFactory.coefficientTarget r (universalMap (J := J) (C := C)) (stageLower r Ff j) j rfl).map s)
      (stageMap_square r Ff s j)) := stageCoefficient_map r Ff s j

section CallerLatching

variable (a : Arrow (J ⥤ C))
  (cX : ∀ j : J, Cocone (r.latchingDiagram a.left j)) (hX : ∀ j : J, IsColimit (cX j))
  (cZ : ∀ j : J, Cocone (r.latchingDiagram ((ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj a) j))
  (hZ : ∀ j : J, IsColimit (cZ j))
  (cP : ∀ j : J, PushoutCocone (r.latchingMapWith a.left j (cX j) (hX j))
    (r.latchingComparisonWith ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a) j
      (cX j) (hX j) (cZ j))) (hP : ∀ j : J, IsColimit (cP j))

theorem fib_actual_chosen_trivial_corners : ∀ j : J, trivialCofibrations C
    (r.latchingCornerWith ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a) j
      (cX j) (hX j) (cZ j) (hZ j) (cP j) (hP j)) :=
  (ReedyModel.trivialCofibration_iff_chosen r Fc Ff _ cX hX cZ hZ cP hP).mp
    ((ReedyModel.fibrantFactorizationData r Fc Ff).hi a)

end CallerLatching

section CallerMatching

variable (a : Arrow (J ⥤ C))
  (cZ : ∀ j : J, Cone (r.matchingDiagram ((ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj a) j))
  (hZ : ∀ j : J, IsLimit (cZ j))
  (cY : ∀ j : J, Cone (r.matchingDiagram a.right j)) (hY : ∀ j : J, IsLimit (cY j))
  (cP : ∀ j : J, PullbackCone
    (r.matchingComparisonWith ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app a) j
      (cZ j) (cY j) (hY j)) (r.matchingMapWith a.right j (cY j) (hY j)))
  (hP : ∀ j : J, IsLimit (cP j))

theorem fib_actual_chosen_corners : ∀ j : J, fibrations C
    (r.matchingCornerWith ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app a) j
      (cZ j) (hZ j) (cY j) (hY j) (cP j) (hP j)) :=
  (ReedyModel.fibration_iff_chosen r Fc Ff _ cZ hZ cY hY cP hP).mp
    ((ReedyModel.fibrantFactorizationData r Fc Ff).hp a)

end CallerMatching

section ActualCofibrantLift

variable (a b : Arrow (J ⥤ C))

theorem actual_cofibration_trivialFibration_lifting :
    HasLiftingProperty ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a)
      ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app b) :=
  ReedyLifting.cofibration_trivialFibration r _ _ (ReedyOriginalClients.cof_i_class r Fc Ff a)
    (ReedyOriginalClients.cof_p_class r Fc Ff b)

variable
  {t : a.left ⟶ (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj b}
  {u : (ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a ⟶ b.right}
  (sq : CommSq t ((ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a)
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).p.app b) u)

def actual_cofibrant_lift : sq.LiftStruct := ReedyLifting.liftStruct r _ _ sq
  (ReedyOriginalClients.cof_i_class r Fc Ff a) (ReedyOriginalClients.cof_p_class r Fc Ff b)

theorem actual_cofibrant_lift_left :
    (ReedyModel.cofibrantFactorizationData r Fc Ff).i.app a ≫ (actual_cofibrant_lift r Fc Ff a b sq).l = t :=
  (actual_cofibrant_lift r Fc Ff a b sq).fac_left

theorem actual_cofibrant_lift_right :
    (actual_cofibrant_lift r Fc Ff a b sq).l ≫ (ReedyModel.cofibrantFactorizationData r Fc Ff).p.app b = u :=
  (actual_cofibrant_lift r Fc Ff a b sq).fac_right

theorem actual_cofibrant_lift_naturality {j k : J} (g : j ⟶ k) :
    ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj a).map g ≫
      (actual_cofibrant_lift r Fc Ff a b sq).l.app k =
        (actual_cofibrant_lift r Fc Ff a b sq).l.app j ≫
          ((ReedyModel.cofibrantFactorizationData r Fc Ff).Z.obj b).map g :=
  (actual_cofibrant_lift r Fc Ff a b sq).l.naturality g

end ActualCofibrantLift

section ActualFibrantLift

variable (a b : Arrow (J ⥤ C))

theorem actual_trivialCofibration_fibration_lifting :
    HasLiftingProperty ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a)
      ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app b) :=
  ReedyLifting.trivialCofibration_fibration r _ _ (ReedyOriginalClients.fib_i_class r Fc Ff a)
    (ReedyOriginalClients.fib_p_class r Fc Ff b)

variable
  {t : a.left ⟶ (ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj b}
  {u : (ReedyModel.fibrantFactorizationData r Fc Ff).Z.obj a ⟶ b.right}
  (sq : CommSq t ((ReedyModel.fibrantFactorizationData r Fc Ff).i.app a)
    ((ReedyModel.fibrantFactorizationData r Fc Ff).p.app b) u)

def actual_fibrant_lift : sq.LiftStruct := CategoryTheory.ReedyStructure.Lifting.liftStruct r sq
  (fun j => hasLiftingProperty_of_wfs _ _ (ReedyOriginalClients.fib_i_class r Fc Ff a j)
    (ReedyOriginalClients.fib_p_class r Fc Ff b j))

theorem actual_fibrant_lift_left :
    (ReedyModel.fibrantFactorizationData r Fc Ff).i.app a ≫ (actual_fibrant_lift r Fc Ff a b sq).l = t :=
  (actual_fibrant_lift r Fc Ff a b sq).fac_left

theorem actual_fibrant_lift_right :
    (actual_fibrant_lift r Fc Ff a b sq).l ≫ (ReedyModel.fibrantFactorizationData r Fc Ff).p.app b = u :=
  (actual_fibrant_lift r Fc Ff a b sq).fac_right

end ActualFibrantLift

end ReedyFactoryClients

end OriginalClientPart2

section OriginalClientPart3

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.ReedyModel.ScalarClients

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D]
  (r : CategoryTheory.ReedyStructure J D) {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {F G : J ⥤ C} (f : F ⟶ G)

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The complete original latching corners are recognized without any degree or source-category restriction. -/
theorem source_latchingRecognition :
    (∀ j : J, trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j)) ↔
      (∀ j : J, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j)) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  latchingCorner_trivialCofibrations_iff r f

/-- The original scalar square has its full chosen-cocone lift constructed only from source model lifting. -/
def source_latchingSquareLift (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    {U V : C} (p : U ⟶ V) {t : cX.pt ⟶ U} {b : cY.pt ⟶ V}
    (sq : CommSq t (r.latchingComparisonWith f j cX hX cY) p b)
    (hp : fibrations C p)
    (hc : ∀ k : J, r.degree k < r.degree j →
      trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f k)) :
    sq.LiftStruct :=
  CategoryTheory.ReedyStructure.latchingComparisonWithLiftStruct r f j cX hX cY hY p sq
    (fun k hk => hasLiftingProperty_of_wfs _ _ (hc k hk) hp)

/-- Both original caller maps of the scalar square are retained by the constructed latching lift. -/
theorem source_latchingSquare_factors (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    {U V : C} (p : U ⟶ V) {t : cX.pt ⟶ U} {b : cY.pt ⟶ V}
    (sq : CommSq t (r.latchingComparisonWith f j cX hX cY) p b)
    (hp : fibrations C p)
    (hc : ∀ k : J, r.degree k < r.degree j →
      trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f k)) :
    r.latchingComparisonWith f j cX hX cY ≫
      (source_latchingSquareLift r f j cX hX cY hY p sq hp hc).l = t ∧
      (source_latchingSquareLift r f j cX hX cY hY p sq hp hc).l ≫ p = b :=
  ⟨(source_latchingSquareLift r f j cX hX cY hY p sq hp hc).fac_left,
    (source_latchingSquareLift r f j cX hX cY hY p sq hp hc).fac_right⟩

/-- Every original chosen latching-corner component is the canonical component under the complete comparison. -/
theorem source_latchingCorner_comparison (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (cP : PushoutCocone (r.latchingMapWith F j cX hX) (r.latchingComparisonWith f j cX hX cY))
    (hP : IsColimit cP) :
    (CategoryTheory.ReedyStructure.latchingCornerSourceIso r f j cX hX cY hY cP hP).hom ≫
      CategoryTheory.ReedyStructure.latchingCorner r f j =
      r.latchingCornerWith f j cX hX cY hY cP hP :=
  CategoryTheory.ReedyStructure.latchingCornerWith_comparison r f j cX hX cY hY cP hP

/-- Full families of original caller chosen cocones and pushouts have the same source recognition. -/
theorem source_chosenLatchingRecognition
    (cX : ∀ j : J, Cocone (r.latchingDiagram F j)) (hX : ∀ j : J, IsColimit (cX j))
    (cY : ∀ j : J, Cocone (r.latchingDiagram G j)) (hY : ∀ j : J, IsColimit (cY j))
    (cP : ∀ j : J, PushoutCocone (r.latchingMapWith F j (cX j) (hX j))
      (r.latchingComparisonWith f j (cX j) (hX j) (cY j)))
    (hP : ∀ j : J, IsColimit (cP j)) :
    (∀ j : J, trivialCofibrations C
      (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ↔
      (∀ j : J, cofibrations C
        (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  latchingCornerWith_trivialCofibrations_iff r f cX hX cY hY cP hP

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The complete original matching corners are recognized without any degree or source-category restriction. -/
theorem source_matchingRecognition :
    (∀ j : J, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j)) ↔
      (∀ j : J, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j)) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  matchingCorner_trivialFibrations_iff r f

/-- The original scalar square has its full chosen-cone lift constructed only from source model lifting. -/
def source_matchingSquareLift (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    {U V : C} (i : U ⟶ V) {t : U ⟶ cX.pt} {b : V ⟶ cY.pt}
    (sq : CommSq t i (r.matchingComparisonWith f j cX cY hY) b)
    (hi : cofibrations C i)
    (hc : ∀ k : J, r.degree k < r.degree j → trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f k)) :
    sq.LiftStruct :=
  CategoryTheory.ReedyStructure.matchingComparisonWithLiftStruct r f j cX hX cY hY i sq
    (fun k hk => hasLiftingProperty_of_wfs _ _ hi (hc k hk))

/-- Both original caller maps of the scalar square are retained by the constructed matching lift. -/
theorem source_matchingSquare_factors (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    {U V : C} (i : U ⟶ V) {t : U ⟶ cX.pt} {b : V ⟶ cY.pt}
    (sq : CommSq t i (r.matchingComparisonWith f j cX cY hY) b)
    (hi : cofibrations C i)
    (hc : ∀ k : J, r.degree k < r.degree j → trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f k)) :
    i ≫ (source_matchingSquareLift r f j cX hX cY hY i sq hi hc).l = t ∧
      (source_matchingSquareLift r f j cX hX cY hY i sq hi hc).l ≫
        r.matchingComparisonWith f j cX cY hY = b :=
  ⟨(source_matchingSquareLift r f j cX hX cY hY i sq hi hc).fac_left,
    (source_matchingSquareLift r f j cX hX cY hY i sq hi hc).fac_right⟩

/-- Every original chosen matching-corner component is the canonical component under the complete comparison. -/
theorem source_matchingCorner_comparison (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (cP : PullbackCone (r.matchingComparisonWith f j cX cY hY) (r.matchingMapWith G j cY hY))
    (hP : IsLimit cP) :
    r.matchingCornerWith f j cX hX cY hY cP hP ≫
      (CategoryTheory.ReedyStructure.matchingCornerTargetIso r f j cX hX cY hY cP hP).hom =
      CategoryTheory.ReedyStructure.matchingCorner r f j :=
  CategoryTheory.ReedyStructure.matchingCornerWith_comparison r f j cX hX cY hY cP hP

/-- Full families of original caller chosen cones and pullbacks have the same source recognition. -/
theorem source_chosenMatchingRecognition
    (cX : ∀ j : J, Cone (r.matchingDiagram F j)) (hX : ∀ j : J, IsLimit (cX j))
    (cY : ∀ j : J, Cone (r.matchingDiagram G j)) (hY : ∀ j : J, IsLimit (cY j))
    (cP : ∀ j : J, PullbackCone (r.matchingComparisonWith f j (cX j) (cY j) (hY j))
      (r.matchingMapWith G j (cY j) (hY j)))
    (hP : ∀ j : J, IsLimit (cP j)) :
    (∀ j : J, trivialFibrations C
      (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ↔
      (∀ j : J, fibrations C
        (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ∧
      (∀ j : J, weakEquivalences C (f.app j)) :=
  matchingCornerWith_trivialFibrations_iff r f cX hX cY hY cP hP

end Matching

end HomotopicalAlgebra.ReedyModel.ScalarClients

end OriginalClientPart3
