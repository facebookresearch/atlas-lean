/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.CotensorCoefficientAction
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorIndexShift

/-!
# Actions on shifted cotensors of symmetric spectra

The sphere-coefficient action on a cotensored symmetric spectrum is the curry of
a coefficient shuffle followed by evaluation and the spectrum action.
Shifting relabels the action by the finite-set tensor product. The combined
shifted-cotensor formula includes the associator for the final index factor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaPreparation.NativeSymmetricShiftCotensorAction
private abbrev I := Operad.SmallFinBijGroupoid
attribute [local instance] CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory

open PointedCGWH.SymmetricModulePresentation

/-- The complete original native labelled action on an actual cotensor is the full coefficient
shuffle followed by original evaluation and that same unchanged native action. -/
theorem cotensor_arrow
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (M : PointedCGWH.{u, v}) (a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    reconstructedArrowAction (cotensorObject M E) a n k f =
      MonoidalClosed.curry
        (CoefficientShuffle.map M (PointedCGWH.sphereSequence.{u, v}.functor.obj a)
          ((ihom M).obj (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj n))) ≫
          (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁
            (ihom.ev M).app (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj n))) ≫
          reconstructedArrowAction E a n k f) := by
  let X := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n)
  let Y := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k)
  let A := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let H := (ihom M).obj X
  let K := (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} k)
  let q : A ⟶ K := operatorGenerator a n k f
  let p : K ⟶ (ihom X).obj Y := E.toEnrichedFunctor.map
    (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k)
  let pM : K ⟶ (ihom H).obj ((ihom M).obj Y) :=
    (EnrichedFunctor.cotensor M E.toEnrichedFunctor).map
      (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k)
  have h : (β_ A H).hom ≫ (H ◁ q) ≫ MonoidalClosed.uncurry pM =
      MonoidalClosed.curry (CoefficientShuffle.map M A H ≫ (A ◁ (ihom.ev M).app X) ≫
        (β_ A X).hom ≫ (X ◁ q) ≫ MonoidalClosed.uncurry p) :=
    CotensorCoefficientAction.action M E.toEnrichedFunctor
      (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k) A q
  change (β_ A H).hom ≫ MonoidalClosed.uncurry (q ≫ pM) =
    MonoidalClosed.curry (CoefficientShuffle.map M A H ≫ (A ◁ (ihom.ev M).app X) ≫
      (β_ A X).hom ≫ MonoidalClosed.uncurry (q ≫ p))
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left]
  exact h

/-- The existing complete native Hom shift carries each original full sphere-coefficient action to
its actual shifted index label. -/
theorem shift_arrow
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (r a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    reconstructedArrowAction ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E) a n k f =
      reconstructedArrowAction E a (n ⊗ r) (k ⊗ r)
        (PointedCGWH.SymmetricShift.label r n k a f) := by
  let X := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))
  let Y := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (k ⊗ r))
  let A := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let K := (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} k)
  let K' := (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r) ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} (k ⊗ r))
  let q : A ⟶ K := operatorGenerator a n k f
  let t : K ⟶ K' := PointedCGWH.SymmetricShift.hom.{u, v} r n k
  let q' : A ⟶ K' := operatorGenerator a (n ⊗ r) (k ⊗ r)
    (PointedCGWH.SymmetricShift.label r n k a f)
  let p : K' ⟶ (ihom X).obj Y :=
    E.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))
      (PointedCGWH.symmetricOperatorObj.{u, v} (k ⊗ r))
  have hg : q ≫ t = q' := by
    apply Under.UnderMorphism.ext
    have hGenerators := congrArg
      (fun Φ => fun (r n k a : I) (f : a ⊗ n ⟶ k) => (Φ r n k a f).right)
      PointedCGWH.SymmetricShift.coendHom_generator_original_function.{u, v}
    have hMaps := congrArg
      (fun Φ => fun (r n k a : I) (f : a ⊗ n ⟶ k) =>
        (operatorGenerator.{u, v} a n k f ≫ Φ r n k).right)
      PointedCGWH.SymmetricShift.coendHom_original_function_via_block_iso.{u, v}
    have hGenerator := congrFun (congrFun (congrFun (congrFun (congrFun
      hGenerators r) n) k) a) f
    have hMap := congrFun (congrFun (congrFun (congrFun (congrFun
      hMaps r) n) k) a) f
    exact hMap.symm.trans hGenerator
  have hp : q ≫ (t ≫ p) = q' ≫ p :=
    (Category.assoc q t p).symm.trans (congrArg (fun z => z ≫ p) hg)
  change (β_ A X).hom ≫ MonoidalClosed.uncurry (q ≫ (t ≫ p)) =
    (β_ A X).hom ≫ MonoidalClosed.uncurry (q' ≫ p)
  exact congrArg (fun z : A ⟶ (ihom X).obj Y => (β_ A X).hom ≫ MonoidalClosed.uncurry z) hp

/-- At every original native coefficient degree, the actual shifted cotensor pair is the original
sphere action with the full final-factor associator. -/
theorem pair_action
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (M : PointedCGWH.{u, v}) (r a n : Operad.SmallFinBijGroupoid) :
    reconstructedPairAction
        (cotensorObject M ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E)) a n =
      MonoidalClosed.curry
        (CoefficientShuffle.map M (PointedCGWH.sphereSequence.{u, v}.functor.obj a)
          ((ihom M).obj (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj (n ⊗ r)))) ≫
          (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁
            (ihom.ev M).app (E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj (n ⊗ r)))) ≫
          reconstructedPairAction E a (n ⊗ r) ≫
          ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map
            (α_ a n r).inv) := by
  let E' := (PointedCGWH.SymmetricShift.functor.{u, v} r).obj E
  let X := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))
  let Y := E.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} ((a ⊗ n) ⊗ r))
  let A := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let H := (ihom M).obj X
  let q : A ⊗ X ⟶ Y := reconstructedPairAction E' a n
  let t : A ⊗ X ⟶ Y := reconstructedPairAction E a (n ⊗ r) ≫
    ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map (α_ a n r).inv
  have hc : reconstructedPairAction (cotensorObject M E') a n =
      MonoidalClosed.curry (CoefficientShuffle.map M A H ≫ (A ◁ (ihom.ev M).app X) ≫ q) :=
    cotensor_arrow E' M a n (a ⊗ n) (𝟙 (a ⊗ n))
  have hlabel : PointedCGWH.SymmetricShift.label r n (a ⊗ n) a (𝟙 (a ⊗ n)) =
      (α_ a n r).inv := by
    simp only [PointedCGWH.SymmetricShift.label, id_tensorHom_id, Category.comp_id]
  have hs : q = reconstructedArrowAction E a (n ⊗ r) ((a ⊗ n) ⊗ r)
      (PointedCGWH.SymmetricShift.label r n (a ⊗ n) a (𝟙 (a ⊗ n))) :=
    shift_arrow E r a n (a ⊗ n) (𝟙 (a ⊗ n))
  have hl := congrArg (reconstructedArrowAction E a (n ⊗ r) ((a ⊗ n) ⊗ r)) hlabel
  have ht : q = t := hs.trans (hl.trans
    (reconstructedPairAction_target E a (n ⊗ r) ((a ⊗ n) ⊗ r) (α_ a n r).inv).symm)
  have hfinal := congrArg (fun z : A ⊗ X ⟶ Y =>
    MonoidalClosed.curry (CoefficientShuffle.map M A H ≫ (A ◁ (ihom.ev M).app X) ≫ z)) ht
  change reconstructedPairAction (cotensorObject M E') a n =
    MonoidalClosed.curry (CoefficientShuffle.map M A H ≫ (A ◁ (ihom.ev M).app X) ≫ t)
  exact hc.trans hfinal

end NativeOmegaPreparation.NativeSymmetricShiftCotensorAction
