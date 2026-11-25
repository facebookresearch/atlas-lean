/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.FactorizationCorners

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Full original functorial Reedy factors and factory maps

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.FunctorialConstruction

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {P Q : MorphismProperty C} (F : FunctorialFactorizationData P Q)

/-- Every original source Arrow value, retained as a diagram in the Arrow parameter functor
category. -/
abbrev universalLeft : J ⥤ Arrow (J ⥤ C) ⥤ C := (Arrow.leftFunc : Arrow (J ⥤ C) ⥤ J ⥤ C).flip

/-- Every original target Arrow value, retained as a diagram in the Arrow parameter functor
category. -/
abbrev universalRight : J ⥤ Arrow (J ⥤ C) ⥤ C := (Arrow.rightFunc : Arrow (J ⥤ C) ⥤ J ⥤ C).flip

/-- The full original universal Arrow transformation, including every original square parameter. -/
def universalMap : universalLeft (J := J) (C := C) ⟶ universalRight (J := J) (C := C) :=
  (flipFunctor (Arrow (J ⥤ C)) J C).map Arrow.leftToRight

/-- The original source factory constructs the whole universal Arrow factor by actual degree
induction. -/
def universalFactor : MapFactorizationData
    (⊤ : MorphismProperty (J ⥤ Arrow (J ⥤ C) ⥤ C)) ⊤ (universalMap (J := J) (C := C)) :=
  DegreeFactorization.factor r (universalMap (J := J) (C := C))
    ((F.functorCategory (Arrow (J ⥤ C))).factorizationData)

/-- The full middle diagram functor on all original Arrows and every original commutative square. -/
def middle : Arrow (J ⥤ C) ⥤ J ⥤ C := (universalFactor r F).Z.flip

/-- The complete original natural left factor arrow on the full Arrow category. -/
def left : Arrow.leftFunc ⟶ middle r F :=
  (flipFunctor J (Arrow (J ⥤ C)) C).map (universalFactor r F).i

/-- The complete original natural right factor arrow on the full Arrow category. -/
def right : middle r F ⟶ Arrow.rightFunc :=
  (flipFunctor J (Arrow (J ⥤ C)) C).map (universalFactor r F).p

/-- Both complete original natural factor arrows recover the original whole Arrow transformation. -/
theorem fac : left r F ≫ right r F = (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) := by
  change (flipFunctor J (Arrow (J ⥤ C)) C).map (universalFactor r F).i ≫
    (flipFunctor J (Arrow (J ⥤ C)) C).map (universalFactor r F).p = _
  rw [← Functor.map_comp, (universalFactor r F).fac]
  rfl

/-- The actual degree algorithm constructs the full original functorial factor record without
diagram outcomes. -/
def data : FunctorialFactorizationData (⊤ : MorphismProperty (J ⥤ C)) ⊤ where
  Z := middle r F
  i := left r F
  p := right r F
  fac := fac r F
  hi _ := trivial
  hp _ := trivial

/-- Both original natural factor arrows recover every original caller Arrow. -/
theorem fac_app (f : Arrow (J ⥤ C)) : (data r F).i.app f ≫ (data r F).p.app f = f.hom :=
  (data r F).fac_app

/-- Every original source square component is retained in the whole natural left-factor equation. -/
theorem i_naturality {f g : Arrow (J ⥤ C)} (s : f ⟶ g) :
    (data r F).i.app f ≫ (data r F).Z.map s = s.left ≫ (data r F).i.app g :=
  ((data r F).i.naturality s).symm

/-- Every original target square component is retained in the whole natural right-factor
equation. -/
theorem p_naturality {f g : Arrow (J ⥤ C)} (s : f ⟶ g) :
    (data r F).Z.map s ≫ (data r F).p.app g = (data r F).p.app f ≫ s.right :=
  (data r F).p.naturality s

/-- The actual whole intermediate functor preserves each original Arrow identity. -/
theorem middle_map_id (f : Arrow (J ⥤ C)) : (data r F).Z.map (𝟙 f) = 𝟙 ((data r F).Z.obj f) :=
  (data r F).Z.map_id f

/-- The actual whole intermediate functor preserves every original compositional square
comparison. -/
theorem middle_map_comp {f g h : Arrow (J ⥤ C)} (s : f ⟶ g) (t : g ⟶ h) :
    (data r F).Z.map (s ≫ t) = (data r F).Z.map s ≫ (data r F).Z.map t :=
  (data r F).Z.map_comp s t

end CategoryTheory.ReedyStructure.FunctorialConstruction

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.FunctorialConstruction

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {P Q : MorphismProperty C} (F : FunctorialFactorizationData P Q)

/-- Evaluating the full original universal left factor is the unchanged flipped left factor. -/
theorem evaluated_left (a : Arrow (J ⥤ C)) :
    Functor.whiskerRight (universalFactor r F).i ((evaluation (Arrow (J ⥤ C)) C).obj a) =
      (data r F).i.app a := rfl

/-- Evaluating the full original universal right factor is the unchanged flipped right factor. -/
theorem evaluated_right (a : Arrow (J ⥤ C)) :
    Functor.whiskerRight (universalFactor r F).p ((evaluation (Arrow (J ⥤ C)) C).obj a) =
      (data r F).p.app a := rfl

/-- The actual original functorial left factor has every original source latching corner in P. -/
theorem data_latching_mem [P.RespectsIso] (a : Arrow (J ⥤ C)) (j : J) :
    P (latchingCorner r ((data r F).i.app a) j) := by
  rw [← evaluated_left]
  apply (EvaluationCorners.latching_mem_iff r (universalFactor r F).i a j P).mp
  exact DegreeFactorization.factor_latching_mem r (universalMap (J := J) (C := C))
    (F.functorCategory (Arrow (J ⥤ C))).factorizationData j a

/-- The actual original functorial right factor has every original source matching corner in Q. -/
theorem data_matching_mem [Q.RespectsIso] (a : Arrow (J ⥤ C)) (j : J) :
    Q (matchingCorner r ((data r F).p.app a) j) := by
  rw [← evaluated_right]
  apply (EvaluationCorners.matching_mem_iff r (universalFactor r F).p a j Q).mp
  exact DegreeFactorization.factor_matching_mem r (universalMap (J := J) (C := C))
    (F.functorCategory (Arrow (J ⥤ C))).factorizationData j a

/-- The source coefficient factory constructs the complete actual functorial Reedy factorization
in its corner
classes. -/
def classifiedData [P.RespectsIso] [Q.RespectsIso] :
    FunctorialFactorizationData (latchingClass r P)
      (matchingClass r Q) where
  Z := (data r F).Z
  i := (data r F).i
  p := (data r F).p
  fac := (data r F).fac
  hi := data_latching_mem r F
  hp := data_matching_mem r F

/-- Both whole original classified natural factor arrows recover the original universal Arrow
transformation. -/
theorem classified_fac [P.RespectsIso] [Q.RespectsIso] :
    (classifiedData r F).i ≫ (classifiedData r F).p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) := (classifiedData r F).fac

/-- Every original Arrow square commutes with the same actual classified natural left factor. -/
theorem classified_i_naturality [P.RespectsIso] [Q.RespectsIso]
    {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (classifiedData r F).i.app a ≫ (classifiedData r F).Z.map s =
      s.left ≫ (classifiedData r F).i.app b := ((classifiedData r F).i.naturality s).symm

/-- Every original Arrow square commutes with the same actual classified natural right factor. -/
theorem classified_p_naturality [P.RespectsIso] [Q.RespectsIso]
    {a b : Arrow (J ⥤ C)} (s : a ⟶ b) :
    (classifiedData r F).Z.map s ≫ (classifiedData r F).p.app b =
      (classifiedData r F).p.app a ≫ s.right := (classifiedData r F).p.naturality s

end CategoryTheory.ReedyStructure.FunctorialConstruction

end ReedyPart2

section ReedyPart3

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.FunctorialConstruction

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {P Q : MorphismProperty C} (F : FunctorialFactorizationData P Q)

/-- The actual original universal lower factor used at the supplied object's own source degree. -/
abbrev stageLower (j : J) :=
  DegreeFactorization.lowerAt r (universalMap (J := J) (C := C))
    (F.functorCategory (Arrow (J ⥤ C))).factorizationData (r.degree j)

/-- The actual original coefficient arrow factored by F on all original Arrow parameters. -/
abbrev stageMap (j : J) := StageFactory.coefficientMap r (universalMap (J := J) (C := C))
  (stageLower r F j) j rfl

/-- The actual original coefficient factor record retains every source Arrow parameter and
square. -/
abbrev stageCoefficient (j : J) := StageFactory.coefficientFactor r (universalMap (J := J) (C := C))
  (stageLower r F j) (F.functorCategory (Arrow (J ⥤ C))).factorizationData j rfl

/-- Each complete intermediate coefficient functor is exactly the original C factory on the
original stage arrow. -/
theorem stageCoefficient_obj (a : Arrow (J ⥤ C)) (j : J) :
    (stageCoefficient r F j).Z.obj a = (F.factorizationData ((stageMap r F j).app a)).Z := rfl

/-- Each complete coefficient left map is exactly the original C factory left map on the same
original stage arrow. -/
theorem stageCoefficient_i (a : Arrow (J ⥤ C)) (j : J) :
    (stageCoefficient r F j).i.app a = F.i.app (Arrow.mk ((stageMap r F j).app a)) := rfl

/-- Each complete coefficient right map is exactly the original C factory right map on the same
original stage arrow. -/
theorem stageCoefficient_p (a : Arrow (J ⥤ C)) (j : J) :
    (stageCoefficient r F j).p.app a = F.p.app (Arrow.mk ((stageMap r F j).app a)) := rfl

/-- The actual flipped global middle object has the original source coefficient factory object. -/
def coefficientObjectIso (a : Arrow (J ⥤ C)) (j : J) :
    ((data r F).Z.obj a).obj j ≅ (stageCoefficient r F j).Z.obj a :=
  eqToIso (congrArg (fun Z : Arrow (J ⥤ C) ⥤ C => Z.obj a)
    (DegreeFactorization.factor_obj_new_eq r (universalMap (J := J) (C := C))
      (F.functorCategory (Arrow (J ⥤ C))).factorizationData j))

/-- Each original global left component is the original pushout injection followed by the source
C factory left map. -/
theorem data_i_factory (a : Arrow (J ⥤ C)) (j : J) :
    ((data r F).i.app a).app j ≫ (coefficientObjectIso r F a j).hom =
      (pushout.inl (latchingMap r (universalLeft (J := J) (C := C)) j)
        (StageFactory.latchingI r (universalMap (J := J) (C := C))
          (stageLower r F j) j rfl)).app a ≫
        F.i.app (Arrow.mk ((stageMap r F j).app a)) := by
  have h := congr_app (DegreeFactorization.factor_i_new r (universalMap (J := J) (C := C))
    (F.functorCategory (Arrow (J ⥤ C))).factorizationData j) a
  change ((universalFactor r F).i.app j).app a ≫
    eqToHom (congrArg (fun Z : Arrow (J ⥤ C) ⥤ C => Z.obj a)
      (DegreeFactorization.factor_obj_new_eq r (universalMap (J := J) (C := C))
        (F.functorCategory (Arrow (J ⥤ C))).factorizationData j)) =
      (StageFactory.newI r (universalMap (J := J) (C := C)) (stageLower r F j)
        (F.functorCategory (Arrow (J ⥤ C))).factorizationData j rfl).app a
  simpa only [NatTrans.comp_app, eqToHom_app, universalFactor, stageLower] using h

/-- Each original global right component is the source C factory right map followed by the
original pullback
projection. -/
theorem data_p_factory (a : Arrow (J ⥤ C)) (j : J) :
    (coefficientObjectIso r F a j).hom ≫ ((StageFactory.newP r (universalMap (J := J) (C := C))
      (stageLower r F j) (F.functorCategory (Arrow (J ⥤ C))).factorizationData j rfl).app a) =
        ((data r F).p.app a).app j := by
  have h := congr_app (DegreeFactorization.factor_p_new r (universalMap (J := J) (C := C))
    (F.functorCategory (Arrow (J ⥤ C))).factorizationData j) a
  change eqToHom (congrArg (fun Z : Arrow (J ⥤ C) ⥤ C => Z.obj a)
      (DegreeFactorization.factor_obj_new_eq r (universalMap (J := J) (C := C))
        (F.functorCategory (Arrow (J ⥤ C))).factorizationData j)) ≫
    (StageFactory.newP r (universalMap (J := J) (C := C)) (stageLower r F j)
      (F.functorCategory (Arrow (J ⥤ C))).factorizationData j rfl).app a =
        ((universalFactor r F).p.app j).app a
  simpa only [NatTrans.comp_app, eqToHom_app, universalFactor, stageLower] using h

/-- The actual right coefficient uses the original C factory projection and the original lower
matching pullback leg. -/
theorem data_p_factory_projection (a : Arrow (J ⥤ C)) (j : J) :
    (coefficientObjectIso r F a j).hom ≫
      (F.p.app (Arrow.mk ((stageMap r F j).app a)) ≫
        (pullback.snd
          (StageFactory.matchingP r (universalMap (J := J) (C := C)) (stageLower r F j) j rfl)
          (matchingMap r (universalRight (J := J) (C := C)) j)).app a) =
      ((data r F).p.app a).app j := data_p_factory r F a j

end CategoryTheory.ReedyStructure.FunctorialConstruction

end ReedyPart3

section ReedyPart4

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.FunctorialConstruction

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {P Q : MorphismProperty C} (F : FunctorialFactorizationData P Q)

/-- Every original Arrow square induces the original full pushout-to-pullback coefficient square. -/
theorem stageMap_square {a b : Arrow (J ⥤ C)} (s : a ⟶ b) (j : J) :
    (StageFactory.coefficientSource r (universalMap (J := J) (C := C))
      (stageLower r F j) j rfl).map s ≫
      (stageMap r F j).app b = (stageMap r F j).app a ≫
        (StageFactory.coefficientTarget r (universalMap (J := J) (C := C))
          (stageLower r F j) j rfl).map s :=
  (stageMap r F j).naturality s

/-- Every coefficient intermediate map is exactly the C factory map of the original coefficient
square. -/
theorem stageCoefficient_map {a b : Arrow (J ⥤ C)} (s : a ⟶ b) (j : J) :
    (stageCoefficient r F j).Z.map s = F.Z.map (Arrow.homMk
      ((StageFactory.coefficientSource r (universalMap (J := J) (C := C))
        (stageLower r F j) j rfl).map s)
      ((StageFactory.coefficientTarget r (universalMap (J := J) (C := C))
        (stageLower r F j) j rfl).map s)
      (stageMap_square r F s j)) := rfl

end CategoryTheory.ReedyStructure.FunctorialConstruction

end ReedyPart4
