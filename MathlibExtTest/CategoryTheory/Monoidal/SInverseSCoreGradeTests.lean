/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreGrade

noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra
open scoped Simplicial

universe u v

#check @CategoryTheory.SInverseS.coreGradeProperty
#print axioms CategoryTheory.SInverseS.coreGradeProperty
#check @CategoryTheory.SInverseS.positiveGradeFractionFunctor
#print axioms CategoryTheory.SInverseS.positiveGradeFractionFunctor
#check @CategoryTheory.SInverseS.positiveGradeFractionFunctor_comp_ι
#print axioms CategoryTheory.SInverseS.positiveGradeFractionFunctor_comp_ι
#check @CategoryTheory.SInverseS.positiveZeroFractionFunctor
#print axioms CategoryTheory.SInverseS.positiveZeroFractionFunctor
#check @CategoryTheory.SInverseS.positiveZeroFractionFunctor_comp_ι
#print axioms CategoryTheory.SInverseS.positiveZeroFractionFunctor_comp_ι
#check @CategoryTheory.SInverseS.positiveZeroFractionHomologyMap_comp_inclusion
#print axioms CategoryTheory.SInverseS.positiveZeroFractionHomologyMap_comp_inclusion

#check @CategoryTheory.SInverseS.coreK0Class_leftTranslation
#print axioms CategoryTheory.SInverseS.coreK0Class_leftTranslation
#check @CategoryTheory.SInverseS.coreGradeLeftTranslationFunctor
#print axioms CategoryTheory.SInverseS.coreGradeLeftTranslationFunctor
#check @CategoryTheory.SInverseS.coreGradeLeftTranslationFunctor_comp_ι
#print axioms CategoryTheory.SInverseS.coreGradeLeftTranslationFunctor_comp_ι

namespace CategoryTheory.SInverseS.CoreGradeTests

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

example (g : GrothendieckAddGroup (Skeleton C)) (t : Skeleton C)
    (X : CoreGrade (C := C) g) :
    ((positiveGradeFractionFunctor (C := C) g t).obj X).obj.difference =
      g - GrothendieckAddGroup.of t :=
  ((positiveGradeFractionFunctor (C := C) g t).obj X).property

-- Equality of K0 classes is the only condition: no isoclass or stable-free witness.
example (P : Core C) (t : Skeleton C)
    (hP : coreK0Class P = GrothendieckAddGroup.of t) :
    ((positiveZeroFractionFunctor (C := C) t).obj ⟨P, hP⟩).obj.difference = 0 :=
  ((positiveZeroFractionFunctor (C := C) t).obj ⟨P, hP⟩).property

example (t : Skeleton C) :
    positiveZeroFractionFunctor (C := C) t ⋙ (zeroComponentProperty (C := C)).ι =
      (coreGradeProperty (C := C) (GrothendieckAddGroup.of t)).ι ⋙
        coreInclusion ⋙ translateSecondFunctor t.out :=
  positiveZeroFractionFunctor_comp_ι (C := C) t

example (A : AddCommGrpCat.{max u v}) (q : ℕ) (t : Skeleton C)
    (x : (nerve (CoreGrade (C := C) (GrothendieckAddGroup.of t))).homology
      (C := AddCommGrpCat.{max u v}) A q) :
    let F : CoreGrade (C := C) (GrothendieckAddGroup.of t) ⥤ ZeroComponent (C := C) :=
      positiveZeroFractionFunctor (C := C) t
    let Z : ZeroComponent (C := C) ⥤ Pair C := (zeroComponentProperty (C := C)).ι
    let I : CoreGrade (C := C) (GrothendieckAddGroup.of t) ⥤ Core C :=
      (coreGradeProperty (C := C) (GrothendieckAddGroup.of t)).ι
    let K : Core C ⥤ Pair C := coreInclusion (C := C)
    let T : Pair C ⥤ Pair C := translateSecondFunctor t.out
    let Xg : SSet.{max u v} := nerve.{v, u} (CoreGrade (C := C) (GrothendieckAddGroup.of t))
    let Xz : SSet.{max u v} := nerve.{max u v, u} (ZeroComponent (C := C))
    let Xc : SSet.{max u v} := nerve.{v, u} (Core C)
    let Xp : SSet.{max u v} := nerve.{max u v, u} (Pair C)
    let f : Xg ⟶ Xz :=
      nerveMapCommonValue.{u, 0, u, v}
        (C := CoreGrade (C := C) (GrothendieckAddGroup.of t)) (D := ZeroComponent (C := C)) F
    let z : Xz ⟶ Xp :=
      nerveMap.{max u v, u} (C := ZeroComponent (C := C)) (D := Pair C) Z
    let i : Xg ⟶ Xc :=
      nerveMap.{v, u} (C := CoreGrade (C := C) (GrothendieckAddGroup.of t)) (D := Core C) I
    let k : Xc ⟶ Xp := nerveMapCommonValue.{u, 0, u, v} (C := Core C) (D := Pair C) K
    let tau : Xp ⟶ Xp := nerveMap.{max u v, u} (C := Pair C) (D := Pair C) T
    let H : SSet.{max u v} ⥤ AddCommGrpCat.{max u v} :=
      SSet.homologyFunctor (C := AddCommGrpCat.{max u v}) A q
    H.map (X := Xz) (Y := Xp) z (H.map (X := Xg) (Y := Xz) f x) =
      H.map (X := Xp) (Y := Xp) tau
        (H.map (X := Xc) (Y := Xp) k (H.map (X := Xg) (Y := Xc) i x)) :=
  ConcreteCategory.congr_hom (positiveZeroFractionHomologyMap_comp_inclusion (C := C) A q t) x

example (T : C) (X : Core C) :
    coreK0Class ((coreLeftTranslationFunctor T).obj X) =
      GrothendieckAddGroup.of (toSkeleton T) + coreK0Class X :=
  coreK0Class_leftTranslation T X

example (T : C) (g : GrothendieckAddGroup (Skeleton C)) :
    coreGradeLeftTranslationFunctor (C := C) T g ⋙
        (coreGradeProperty (C := C) (GrothendieckAddGroup.of (toSkeleton T) + g)).ι =
      (coreGradeProperty (C := C) g).ι ⋙ coreLeftTranslationFunctor T :=
  coreGradeLeftTranslationFunctor_comp_ι T g

end CategoryTheory.SInverseS.CoreGradeTests

namespace CategoryTheory.SInverseS.DiagonalClassTests

-- An arbitrary object's numerator uses its own class, with the original
-- diagonal pair and literal fraction retained.
example {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (P : C) :
    (Pair.mk P P).difference = 0 ∧
      (diagonalZeroComponentObject P).obj = Pair.mk P P ∧
      Nonempty ((positiveZeroFractionFunctor (C := C) (toSkeleton P)).obj
        (diagonalCoreGradeObject P) ≅ diagonalZeroComponentObject P) :=
  ⟨Pair.diagonal_difference_zero P, diagonalZeroComponentObject_obj P,
    ⟨positiveZeroFraction_diagonalIso P⟩⟩

example {C : Type 1} [Category.{2} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (P : C) :
    Nonempty ((positiveZeroFractionFunctor (C := C) (toSkeleton P)).obj
      (diagonalCoreGradeObject P) ≅ diagonalZeroComponentObject P) :=
  ⟨positiveZeroFraction_diagonalIso P⟩

example {C : Type 2} [Category.{1} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (P : C) :
    Nonempty ((positiveZeroFractionFunctor (C := C) (toSkeleton P)).obj
      (diagonalCoreGradeObject P) ≅ diagonalZeroComponentObject P) :=
  ⟨positiveZeroFraction_diagonalIso P⟩

end CategoryTheory.SInverseS.DiagonalClassTests

end
