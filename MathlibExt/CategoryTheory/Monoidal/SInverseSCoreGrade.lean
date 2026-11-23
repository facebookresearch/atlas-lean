/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationComponents
public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentHomology
public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentTranslation
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationFiberPushforward
public import MathlibExt.CategoryTheory.NerveCrossUniverse

/-!
# The actual K0 grade of a translated core class

The source full subcategory is defined by the original Grothendieck class of
its core object. The original positive core inclusion followed by second
translation subtracts the actual denominator class. At equal classes it lands
in the existing categorical zero component, with the same underlying functor.
No stable-freeness, replacement pair, homology comparison or inverse is input.
-/

noncomputable section

open CategoryTheory Limits ZeroObject Algebra Opposite
open scoped Simplicial

universe u v

public section

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The original Grothendieck class of a core object. -/
abbrev coreK0Class (X : Core C) : GrothendieckAddGroup (Skeleton C) :=
  GrothendieckAddGroup.of (toSkeleton X.of)

/-- Core objects with the specified original K0 grade. -/
abbrev coreGradeProperty (g : GrothendieckAddGroup (Skeleton C)) :
    ObjectProperty (Core C) := fun X => coreK0Class X = g

/-- The full subcategory of the original core at one K0 grade. -/
abbrev CoreGrade (g : GrothendieckAddGroup (Skeleton C)) :=
  (coreGradeProperty (C := C) g).FullSubcategory

private theorem positiveFraction_difference
    (g : GrothendieckAddGroup (Skeleton C)) (t : Skeleton C)
    (X : CoreGrade (C := C) g) :
    ((translateSecondFunctor t.out).obj (coreInclusion.obj X.obj)).difference =
      g - GrothendieckAddGroup.of t := by
  have hT : GrothendieckAddGroup.of (toSkeleton t.out) =
      GrothendieckAddGroup.of t :=
    congrArg GrothendieckAddGroup.of (toSkeleton_fromSkeleton_obj t)
  have hX : (coreInclusion.obj X.obj).difference = g :=
    (coreInclusion_difference X.obj).trans X.property
  have hFirst := Pair.difference_translateSecondObj t.out (coreInclusion.obj X.obj)
  exact hFirst.trans
    ((congrArg (fun k => k - GrothendieckAddGroup.of (toSkeleton t.out)) hX).trans
      (congrArg (fun k => g - k) hT))

/-- The literal positive core map followed by second translation, with only
its codomain restricted to the computed original grade. -/
def positiveGradeFractionFunctor
    (g : GrothendieckAddGroup (Skeleton C)) (t : Skeleton C) :
    CoreGrade (C := C) g ⥤
      ComponentTranslation.Component (C := C) (g - GrothendieckAddGroup.of t) :=
  ObjectProperty.lift
    (ComponentTranslation.componentProperty (C := C) (g - GrothendieckAddGroup.of t))
    ((coreGradeProperty (C := C) g).ι ⋙ coreInclusion ⋙ translateSecondFunctor t.out)
    (positiveFraction_difference g t)

private theorem positiveGradeFractionFunctor_comp_ι_computation
    (g : GrothendieckAddGroup (Skeleton C)) (t : Skeleton C) :
    positiveGradeFractionFunctor (C := C) g t ⋙
        (ComponentTranslation.componentProperty (C := C) (g - GrothendieckAddGroup.of t)).ι =
      (coreGradeProperty (C := C) g).ι ⋙ coreInclusion ⋙ translateSecondFunctor t.out := by
  unfold positiveGradeFractionFunctor
  rfl

/-- Forgetting the computed grade retains the entire original fraction functor. -/
theorem positiveGradeFractionFunctor_comp_ι
    (g : GrothendieckAddGroup (Skeleton C)) (t : Skeleton C) :
    positiveGradeFractionFunctor (C := C) g t ⋙
        (ComponentTranslation.componentProperty (C := C) (g - GrothendieckAddGroup.of t)).ι =
      (coreGradeProperty (C := C) g).ι ⋙ coreInclusion ⋙ translateSecondFunctor t.out :=
  positiveGradeFractionFunctor_comp_ι_computation g t

/-- Every numerator with the SAME denominator class maps to the existing zero
component. The original second coordinate t.out biproduct zero is retained. -/
def positiveZeroFractionFunctor (t : Skeleton C) :
    CoreGrade (C := C) (GrothendieckAddGroup.of t) ⥤ ZeroComponent (C := C) :=
  ObjectProperty.lift (zeroComponentProperty (C := C))
    ((coreGradeProperty (C := C) (GrothendieckAddGroup.of t)).ι ⋙
      coreInclusion ⋙ translateSecondFunctor t.out)
    (fun X => (positiveFraction_difference (GrothendieckAddGroup.of t) t X).trans
      (sub_self (GrothendieckAddGroup.of t)))

private theorem positiveZeroFractionFunctor_comp_ι_computation (t : Skeleton C) :
    positiveZeroFractionFunctor (C := C) t ⋙ (zeroComponentProperty (C := C)).ι =
      (coreGradeProperty (C := C) (GrothendieckAddGroup.of t)).ι ⋙
        coreInclusion ⋙ translateSecondFunctor t.out := by
  unfold positiveZeroFractionFunctor
  rfl

/-- The zero-grade restriction retains the whole original core/translation map. -/
theorem positiveZeroFractionFunctor_comp_ι (t : Skeleton C) :
    positiveZeroFractionFunctor (C := C) t ⋙ (zeroComponentProperty (C := C)).ι =
      (coreGradeProperty (C := C) (GrothendieckAddGroup.of t)).ι ⋙
        coreInclusion ⋙ translateSecondFunctor t.out :=
  positiveZeroFractionFunctor_comp_ι_computation t

/-- In EVERY homological degree the restricted map has the original whole
core-fraction homology square. -/
theorem positiveZeroFractionHomologyMap_comp_inclusion
    (A : AddCommGrpCat.{max u v}) (q : ℕ) (t : Skeleton C) :
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
    H.map (X := Xg) (Y := Xz) f ≫ H.map (X := Xz) (Y := Xp) z =
      H.map (X := Xg) (Y := Xc) i ≫ H.map (X := Xc) (Y := Xp) k ≫
        H.map (X := Xp) (Y := Xp) tau := by
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
  have hFunctor : F ⋙ Z = I ⋙ K ⋙ T :=
    positiveZeroFractionFunctor_comp_ι (C := C) t
  have hNerve : f ≫ z = i ≫ k ≫ tau := by
    ext Δ X
    change ((F ⋙ Z).mapComposableArrows Δ.unop.len).obj X =
      ((I ⋙ K ⋙ T).mapComposableArrows Δ.unop.len).obj X
    exact congrArg
      (fun W : CoreGrade (C := C) (GrothendieckAddGroup.of t) ⥤ Pair C =>
        (W.mapComposableArrows Δ.unop.len).obj X) hFunctor
  change H.map f ≫ H.map z = H.map i ≫ H.map k ≫ H.map tau
  calc
    H.map f ≫ H.map z = H.map (f ≫ z) := (H.map_comp f z).symm
    _ = H.map (i ≫ k ≫ tau) :=
      congrArg (fun arrow : Xg ⟶ Xp => H.map arrow) hNerve
    _ = H.map i ≫ H.map k ≫ H.map tau := by
      rw [H.map_comp, H.map_comp]

/-- The existing core LEFT translation adds the actual translating object's
original class. Its object remains the literal biproduct T ⊞ X. -/
theorem coreK0Class_leftTranslation (T : C) (X : Core C) :
    coreK0Class ((coreLeftTranslationFunctor T).obj X) =
      GrothendieckAddGroup.of (toSkeleton T) + coreK0Class X := by
  dsimp only [coreK0Class]
  rw [coreLeftTranslationFunctor_obj_of, Skeleton.toSkeleton_biprod, map_add]

/-- The actual core left translation, restricted to its COMPUTED K0 grades.
No free representative or target-property witness is supplied. -/
def coreGradeLeftTranslationFunctor
    (T : C) (g : GrothendieckAddGroup (Skeleton C)) :
    CoreGrade (C := C) g ⥤
      CoreGrade (C := C) (GrothendieckAddGroup.of (toSkeleton T) + g) :=
  ObjectProperty.lift
    (coreGradeProperty (C := C) (GrothendieckAddGroup.of (toSkeleton T) + g))
    ((coreGradeProperty (C := C) g).ι ⋙ coreLeftTranslationFunctor T)
    (fun X => (coreK0Class_leftTranslation T X.obj).trans
      (congrArg (fun k => GrothendieckAddGroup.of (toSkeleton T) + k) X.property))

private theorem coreGradeLeftTranslationFunctor_comp_ι_computation
    (T : C) (g : GrothendieckAddGroup (Skeleton C)) :
    coreGradeLeftTranslationFunctor (C := C) T g ⋙
        (coreGradeProperty (C := C) (GrothendieckAddGroup.of (toSkeleton T) + g)).ι =
      (coreGradeProperty (C := C) g).ι ⋙ coreLeftTranslationFunctor T := by
  unfold coreGradeLeftTranslationFunctor
  rfl

/-- Forgetting the computed grade retains the WHOLE original left-translation
functor and every original core morphism. -/
theorem coreGradeLeftTranslationFunctor_comp_ι
    (T : C) (g : GrothendieckAddGroup (Skeleton C)) :
    coreGradeLeftTranslationFunctor (C := C) T g ⋙
        (coreGradeProperty (C := C) (GrothendieckAddGroup.of (toSkeleton T) + g)).ι =
      (coreGradeProperty (C := C) g).ι ⋙ coreLeftTranslationFunctor T :=
  coreGradeLeftTranslationFunctor_comp_ι_computation T g

/-! ## The original diagonal pair at its actual projective class -/

/-- Equal coordinates have zero difference at every original class. -/
theorem Pair.diagonal_difference_zero (P : C) :
    (Pair.mk P P).difference = 0 := by
  change GrothendieckAddGroup.of (toSkeleton P) -
    GrothendieckAddGroup.of (toSkeleton P) = 0
  exact sub_self _

/-- The original diagonal pair in the actual categorical zero component. -/
def diagonalZeroComponentObject (P : C) : ZeroComponent (C := C) :=
  ⟨Pair.mk P P, Pair.diagonal_difference_zero P⟩

private theorem diagonalZeroComponentObject_obj_computation (P : C) :
    (diagonalZeroComponentObject P).obj = Pair.mk P P := by
  unfold diagonalZeroComponentObject
  rfl

theorem diagonalZeroComponentObject_obj (P : C) :
    (diagonalZeroComponentObject P).obj = Pair.mk P P :=
  diagonalZeroComponentObject_obj_computation P

/-- The original numerator belongs to its own Grothendieck grade. -/
def diagonalCoreGradeObject (P : C) :
    CoreGrade (C := C) (GrothendieckAddGroup.of (toSkeleton P)) :=
  ⟨Core.mk P, rfl⟩

private theorem diagonalCoreGradeObject_obj_computation (P : C) :
    (diagonalCoreGradeObject P).obj = Core.mk P := by
  unfold diagonalCoreGradeObject
  rfl

theorem diagonalCoreGradeObject_obj (P : C) :
    (diagonalCoreGradeObject P).obj = Core.mk P :=
  diagonalCoreGradeObject_obj_computation P

private def positiveZeroFraction_diagonalIso_computation (P : C) :
    (positiveZeroFractionFunctor (C := C) (toSkeleton P)).obj
        (diagonalCoreGradeObject P) ≅ diagonalZeroComponentObject P := by
  let t : Skeleton C := toSkeleton P
  let eP : t.out ≅ P := Skeleton.isoOfEq (toSkeleton_fromSkeleton_obj t)
  let eRight : t.out ⊞ (0 : C) ≅ t.out :=
    (isoBiprodZero (X := t.out) (isZero_zero C)).symm
  let eDen : t.out ⊞ (0 : C) ≅ P := eRight ≪≫ eP
  let eCoreDen : Core.mk (t.out ⊞ (0 : C)) ≅ Core.mk P := Core.isoMk eDen
  let eCorePair : (Core.mk P, Core.mk (t.out ⊞ (0 : C))) ≅
      (Core.mk P, Core.mk P) :=
    (Iso.refl (Core.mk P)).prod eCoreDen
  let ePair : Pair.mk P (t.out ⊞ (0 : C)) ≅ Pair.mk P P :=
    (corePairInclusion (C := C)).mapIso eCorePair
  apply ObjectProperty.isoMk
  change Pair.mk P (t.out ⊞ (0 : C)) ≅ Pair.mk P P
  exact ePair

/-- The literal numerator/denominator fraction at class `[P]` is
isomorphic to the original diagonal `(P,P)`. The denominator retains
its chosen skeleton representative and actual zero biproduct until the
computed right-unitor and skeleton Iso are applied. No free class or
stable-free witness is required. Object and Hom universes are independent. -/
def positiveZeroFractionDiagonalIso (P : C) :
    (positiveZeroFractionFunctor (C := C) (toSkeleton P)).obj
        (diagonalCoreGradeObject P) ≅ diagonalZeroComponentObject P :=
  positiveZeroFraction_diagonalIso_computation P

/- The historical name uses the builtin persistent export mechanism.
The scoped rename preserves the same public definition and its type. -/
open CategoryTheory.SInverseS renaming positiveZeroFractionDiagonalIso →
  positiveZeroFraction_diagonalIso in
export _root_ (positiveZeroFraction_diagonalIso)

end CategoryTheory.SInverseS

end
