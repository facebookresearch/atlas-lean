/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Finite projectives with independent category object and Hom universes

The original module carriers remain in `max uR uM`. The objects are lifted
to `max (max uR uM + 1) uObj`, and the original morphisms are lifted separately
to `max (max uR uM) uHom`. The actual up/down equivalence transports the Hom
groups, zero object, binary biproducts and canonical split exact structure.
Neither a category equivalence nor an additive/exact structure is an input.

`canonicalZero` is the literal image of the old chosen zero. The new
`HasZeroObject` supplies the usual chosen zero, which is canonically isomorphic
to it. No equality between two independently chosen zero objects is asserted.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] uliftCategory

universe uR uM uObj uHom

namespace FGProjectiveCat.CategoryUniverseLift

variable (R : Type uR) [Ring R]

/-- The original finite-projective category, with the regular module retained. -/
abbrev originalCategory : Type (max uR uM + 1) :=
  FGProjectiveCat.{max uR uM} R

-- `uM` controls the underlying module and Hom universes, while `uObj` raises only the
-- object universe. `uHom` enters the Hom lift in the value, not the type of this abbreviation.
-- The result sort combines `uM` and `uObj`; applications below pass all four levels explicitly.
set_option linter.checkUnivs false in
/-- Separate lifts of the actual original objects and actual original Hom types. -/
abbrev category : Type (max (max uR uM + 1) uObj) :=
  ULiftHom.{max (max uR uM) uHom}
    (ULift.{max (max uR uM + 1) uObj} (originalCategory.{uR, uM} R))

/-- The actual lifted category has the requested independent Hom universe. -/
instance categoryCategory :
    Category.{max (max uR uM) uHom} (category.{uR, uM, uObj, uHom} R) := by
  dsimp only [category]
  infer_instance

/-- Canonical object/Hom lifting equivalence, with the original up/down maps. -/
@[expose] def equivalence :
    originalCategory.{uR, uM} R ≌ category.{uR, uM, uObj, uHom} R :=
  ULiftHomULiftCategory.equiv.{max (max uR uM) uHom,
    max (max uR uM + 1) uObj, max uR uM, max uR uM + 1}
    (originalCategory.{uR, uM} R)

/-- The original object and morphism universe lift. -/
@[expose] def upFunctor : originalCategory.{uR, uM} R ⥤ category.{uR, uM, uObj, uHom} R :=
  (equivalence.{uR, uM, uObj, uHom} R).functor

/-- The original object and morphism universe descent. -/
@[expose] def downFunctor : category.{uR, uM, uObj, uHom} R ⥤ originalCategory.{uR, uM} R :=
  (equivalence.{uR, uM, uObj, uHom} R).inverse

/-- The forward functor is the actual equivalence functor. -/
instance upFunctorIsEquivalence : (upFunctor.{uR, uM, uObj, uHom} R).IsEquivalence :=
  (equivalence.{uR, uM, uObj, uHom} R).isEquivalence_functor

/-- The inverse functor is the actual equivalence inverse. -/
instance downFunctorIsEquivalence : (downFunctor.{uR, uM, uObj, uHom} R).IsEquivalence :=
  (equivalence.{uR, uM, uObj, uHom} R).isEquivalence_inverse

/-- Pull the actual original Hom groups back along the fully faithful descent. -/
instance categoryPreadditive : Preadditive (category.{uR, uM, uObj, uHom} R) :=
  Preadditive.ofFullyFaithful
    (equivalence.{uR, uM, uObj, uHom} R).symm.fullyFaithfulFunctor

/-- Descent preserves the actual original addition of linear maps. -/
instance downFunctorAdditive : (downFunctor.{uR, uM, uObj, uHom} R).Additive :=
  (equivalence.{uR, uM, uObj, uHom} R).symm.fullyFaithfulFunctor.additive_ofFullyFaithful

/-- The canonical inverse lift is additive for that same transferred structure. -/
instance upFunctorAdditive : (upFunctor.{uR, uM, uObj, uHom} R).Additive :=
  (equivalence.{uR, uM, uObj, uHom} R).symm.additive_inverse_of_FullyFaithful

/-- The old chosen zero lifted by the original object functor. -/
@[expose] def canonicalZero : category.{uR, uM, uObj, uHom} R :=
  (upFunctor.{uR, uM, uObj, uHom} R).obj (0 : originalCategory.{uR, uM} R)

/-- The literal lifted zero is a zero object by the original zero-morphism law. -/
theorem canonicalZeroIsZero : IsZero (canonicalZero.{uR, uM, uObj, uHom} R) :=
  Functor.map_isZero (upFunctor.{uR, uM, uObj, uHom} R)
    (isZero_zero (originalCategory.{uR, uM} R))

/-- The category's zero-object existence is derived from the literal lifted zero. -/
instance categoryHasZeroObject : HasZeroObject (category.{uR, uM, uObj, uHom} R) :=
  ⟨⟨canonicalZero.{uR, uM, uObj, uHom} R,
    canonicalZeroIsZero.{uR, uM, uObj, uHom} R⟩⟩

/-- Binary products are transported through the actual descent equivalence. -/
instance categoryHasBinaryProducts : HasBinaryProducts (category.{uR, uM, uObj, uHom} R) :=
  CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence (J := Discrete WalkingPair)
    (downFunctor.{uR, uM, uObj, uHom} R)

/-- The transported products and Hom groups give actual binary biproducts. -/
instance categoryHasBinaryBiproducts : HasBinaryBiproducts (category.{uR, uM, uObj, uHom} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The same canonical split exact structure on the independently lifted category. -/
instance categoryExact : ExactCategory (category.{uR, uM, uObj, uHom} R) :=
  ExactCategory.splitExactCategory (C := category.{uR, uM, uObj, uHom} R)

/-- Lifting is exact because its original source has the split exact structure. -/
instance upFunctorIsExact : (upFunctor.{uR, uM, uObj, uHom} R).IsExact :=
  ExactCategory.isExact_splitSource (upFunctor.{uR, uM, uObj, uHom} R)

/-- Descent is exact for the same lifted split exact structure. -/
instance downFunctorIsExact : (downFunctor.{uR, uM, uObj, uHom} R).IsExact :=
  ExactCategory.isExact_splitSource (downFunctor.{uR, uM, uObj, uHom} R)

/-- The complete original object formula for lifting. -/
theorem upFunctorObj (X : originalCategory.{uR, uM} R) :
    (upFunctor.{uR, uM, uObj, uHom} R).obj X =
      (ULiftHom.objUp (ULift.up X) : category.{uR, uM, uObj, uHom} R) := rfl

/-- The complete original object formula for descent. -/
theorem downFunctorObj (X : category.{uR, uM, uObj, uHom} R) :
    (downFunctor.{uR, uM, uObj, uHom} R).obj X = X.objDown.down := rfl

/-- Descent after lifting is the original object, as an equality. -/
theorem downUpObj (X : originalCategory.{uR, uM} R) :
    (downFunctor.{uR, uM, uObj, uHom} R).obj
      ((upFunctor.{uR, uM, uObj, uHom} R).obj X) = X := rfl

/-- Lifting after descent returns the actual lifted object. -/
theorem upDownObj (X : category.{uR, uM, uObj, uHom} R) :
    (upFunctor.{uR, uM, uObj, uHom} R).obj
      ((downFunctor.{uR, uM, uObj, uHom} R).obj X) = X := by
  change ULiftHom.objUp (ULift.up X.objDown.down) = X
  exact (congrArg
    (fun Y : ULift.{max (max uR uM + 1) uObj} (originalCategory.{uR, uM} R) =>
      (ULiftHom.objUp Y : category.{uR, uM, uObj, uHom} R))
    (ULift.up_down X.objDown)).trans (objUp_objDown X)

/-- The lift wraps the original linear-map morphism without changing it. -/
theorem upFunctorMap {X Y : originalCategory.{uR, uM} R} (f : X ⟶ Y) :
    (upFunctor.{uR, uM, uObj, uHom} R).map f = ULift.up f := rfl

/-- Descent unwraps the same original linear-map morphism. -/
theorem downFunctorMap {X Y : category.{uR, uM, uObj, uHom} R} (f : X ⟶ Y) :
    (downFunctor.{uR, uM, uObj, uHom} R).map f = f.down := rfl

/-- The actual lift is injective on every original Hom type. -/
theorem upFunctorMapInjective (X Y : originalCategory.{uR, uM} R) :
    Function.Injective ((upFunctor.{uR, uM, uObj, uHom} R).map :
      (X ⟶ Y) → ((upFunctor.{uR, uM, uObj, uHom} R).obj X ⟶
        (upFunctor.{uR, uM, uObj, uHom} R).obj Y)) :=
  (upFunctor.{uR, uM, uObj, uHom} R).map_injective

/-- The actual descent is injective on every lifted Hom type. -/
theorem downFunctorMapInjective (X Y : category.{uR, uM, uObj, uHom} R) :
    Function.Injective ((downFunctor.{uR, uM, uObj, uHom} R).map :
      (X ⟶ Y) → ((downFunctor.{uR, uM, uObj, uHom} R).obj X ⟶
        (downFunctor.{uR, uM, uObj, uHom} R).obj Y)) :=
  (downFunctor.{uR, uM, uObj, uHom} R).map_injective

/-- Lifting retains zero morphisms in the same transferred Hom groups. -/
theorem upFunctorMapZero (X Y : originalCategory.{uR, uM} R) :
    (upFunctor.{uR, uM, uObj, uHom} R).map (0 : X ⟶ Y) = 0 := by simp

/-- Descent retains zero morphisms in the original Hom groups. -/
theorem downFunctorMapZero (X Y : category.{uR, uM, uObj, uHom} R) :
    (downFunctor.{uR, uM, uObj, uHom} R).map (0 : X ⟶ Y) = 0 := by simp

/-- The literal lifted zero descends to the original chosen zero. -/
theorem downCanonicalZero :
    (downFunctor.{uR, uM, uObj, uHom} R).obj
      (canonicalZero.{uR, uM, uObj, uHom} R) = (0 : originalCategory.{uR, uM} R) := rfl

/-- Canonical comparison from the literal lifted zero to the category's chosen zero. -/
def upZeroIso : (upFunctor.{uR, uM, uObj, uHom} R).obj
    (0 : originalCategory.{uR, uM} R) ≅ (0 : category.{uR, uM, uObj, uHom} R) :=
  (canonicalZeroIsZero.{uR, uM, uObj, uHom} R).isoZero

/-- Canonical comparison from the image of the actual chosen zero to the old zero. -/
def downZeroIso : (downFunctor.{uR, uM, uObj, uHom} R).obj
    (0 : category.{uR, uM, uObj, uHom} R) ≅ (0 : originalCategory.{uR, uM} R) :=
  (Functor.map_isZero (downFunctor.{uR, uM, uObj, uHom} R)
    (isZero_zero (category.{uR, uM, uObj, uHom} R))).isoZero

/-- The unit at the original zero is the unique zero-object endomorphism. -/
theorem unitHomAtZero :
    (equivalence.{uR, uM, uObj, uHom} R).unitIso.hom.app
      (0 : originalCategory.{uR, uM} R) = 𝟙 (0 : originalCategory.{uR, uM} R) :=
  (isZero_zero (originalCategory.{uR, uM} R)).eq_of_src _ _

/-- The counit at the actual chosen zero is its literal object-equality transport. -/
theorem counitHomAtZero :
    (equivalence.{uR, uM, uObj, uHom} R).counitIso.hom.app
      (0 : category.{uR, uM, uObj, uHom} R) =
        eqToHom (upDownObj.{uR, uM, uObj, uHom} R
          (0 : category.{uR, uM, uObj, uHom} R)) :=
  (isZero_zero (category.{uR, uM, uObj, uHom} R)).eq_of_tgt _ _

/-- The actual admissible short complexes are exactly the original splitting predicate. -/
theorem admissibleExactIffSplitting (S : ShortComplex (category.{uR, uM, uObj, uHom} R)) :
    ExactCategory.IsAdmissibleExact S ↔ Nonempty S.Splitting := Iff.rfl

end FGProjectiveCat.CategoryUniverseLift

end
