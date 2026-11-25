/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Actual coefficient lifting and colimits for the original enriched Free functor

Every map below uses the original Free extension, identity evaluation and chosen adjunction.
Commutative squares and their full lift structures are transported through that adjunction.
Colimit descents retain every coefficient leg. No spectrum model or carrier equivalence is
an input to these functions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uA uV vV uJ vJ

namespace CategoryTheory.EnrichedFunctorCat.Free

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Actual Free identity evaluation respects coefficient precomposition. -/
theorem evaluate_precomp (a : A) {X Y : V} (F : EnrichedFunctorCat V A)
    (f : X ⟶ Y) (t : object a Y ⟶ F) :
    evaluate a X F ((functor a).map f ≫ t) = f ≫ evaluate a Y F t := by
  calc
    _ = evaluate a X F ((functor a).map f ≫ extend a Y F (evaluate a Y F t)) := by
      rw [extend_evaluate]
    _ = evaluate a X F (extend a X F (f ≫ evaluate a Y F t)) := by
      rw [extend_precomp]
    _ = _ := evaluate_extend a X F _

/-- Actual extension respects every target transformation, as a full natural transformation. -/
theorem extend_postcomp (a : A) (X : V) {F G : EnrichedFunctorCat V A}
    (f : X ⟶ F.toEnrichedFunctor.obj a) (p : F ⟶ G) :
    extend a X F f ≫ p =
      extend a X G (f ≫ (EnrichedFunctorCat.evaluation a).map p) := by
  apply (homEquiv a X G).injective
  change evaluate a X G (extend a X F f ≫ p) =
    evaluate a X G (extend a X G _)
  rw [evaluate_postcomp, evaluate_extend, evaluate_extend]
  rfl

section Squares

variable (a : A) {X Y : V} {F G : EnrichedFunctorCat V A}
  (i : X ⟶ Y) (p : F ⟶ G)
  (u : object a X ⟶ F) (v : object a Y ⟶ G)

/-- Evaluate both complete Free sides of a square at the original enriched identity. -/
theorem coefficientSquare (s : CommSq u ((functor a).map i) p v) :
    CommSq (evaluate a X F u) i
      ((EnrichedFunctorCat.evaluation a).map p) (evaluate a Y G v) := by
  exact ⟨(evaluate_postcomp a X u p).symm.trans
    ((congrArg (evaluate a X G) s.w).trans (evaluate_precomp a G i v))⟩

/-- Coefficient squares extend to actual Free natural-transformation squares. -/
theorem extensionSquare
    (x : X ⟶ F.toEnrichedFunctor.obj a) (y : Y ⟶ G.toEnrichedFunctor.obj a)
    (s : CommSq x i ((EnrichedFunctorCat.evaluation a).map p) y) :
    CommSq (extend a X F x) ((functor a).map i) p (extend a Y G y) := by
  exact ⟨(extend_postcomp a X x p).trans
    ((congrArg (extend a X G) s.w).trans (extend_precomp a G i y))⟩

/-- The complete Free and coefficient lift structures correspond through the chosen adjunction. -/
def coefficientLiftStructEquiv (s : CommSq u ((functor a).map i) p v) :
    s.LiftStruct ≃ (coefficientSquare a i p u v s).LiftStruct where
  toFun l :=
    { l := evaluate a Y F l.l
      fac_left := (evaluate_precomp a F i l.l).symm.trans
        (congrArg (evaluate a X F) l.fac_left)
      fac_right := (evaluate_postcomp a Y l.l p).symm.trans
        (congrArg (evaluate a Y G) l.fac_right) }
  invFun l :=
    { l := extend a Y F l.l
      fac_left := (extend_precomp a F i l.l).symm.trans
        ((congrArg (extend a X F) l.fac_left).trans (extend_evaluate a X F u))
      fac_right := (extend_postcomp a Y l.l p).trans
        ((congrArg (extend a Y G) l.fac_right).trans (extend_evaluate a Y G v)) }
  left_inv l := by
    ext1
    exact extend_evaluate a Y F l.l
  right_inv l := by
    ext1
    exact evaluate_extend a Y F l.l

/-- The coefficient lift is the original identity evaluation of the entire Free lift. -/
def evaluateLift (s : CommSq u ((functor a).map i) p v) (l : s.LiftStruct) :
    (coefficientSquare a i p u v s).LiftStruct :=
  coefficientLiftStructEquiv a i p u v s l

/-- The inverse lift is the entire original Free extension of the coefficient lift. -/
def extendLift (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) : s.LiftStruct :=
  (coefficientLiftStructEquiv a i p u v s).symm l

/-- The evaluated lift keeps its actual coefficient map, including all source parameters. -/
theorem evaluateLift_l (s : CommSq u ((functor a).map i) p v) (l : s.LiftStruct) :
    (evaluateLift a i p u v s l).l = evaluate a Y F l.l := rfl

/-- Every inverse lift has the complete actual extension as its natural-transformation map. -/
theorem extendLift_l (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) :
    (extendLift a i p u v s l).l = extend a Y F l.l := rfl

/-- Every actual lift is recovered after the coefficient evaluation and full extension. -/
theorem extend_evaluateLift (s : CommSq u ((functor a).map i) p v) (l : s.LiftStruct) :
    extendLift a i p u v s (evaluateLift a i p u v s l) = l :=
  (coefficientLiftStructEquiv a i p u v s).symm_apply_apply l

/-- Every coefficient lift is recovered after the full Free extension and evaluation. -/
theorem evaluate_extendLift (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) :
    evaluateLift a i p u v s (extendLift a i p u v s l) = l :=
  (coefficientLiftStructEquiv a i p u v s).apply_symm_apply l

/-- All components of the extended lift retain the original coefficient-first action formula. -/
theorem extendLift_component (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) (b : A) :
    EnrichedFunctorCat.component (extendLift a i p u v s l).l b =
      (l.l ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  rw [extendLift_l, extend_component]
  rfl

end Squares

section Colimits

variable {J : Type uJ} [Category.{vJ} J] (a : A) (K : J ⥤ V)

/-- Map the entire original coefficient cocone by the actual Free functor. -/
def coefficientCoconeImage (c : Cocone K) : Cocone (K ⋙ functor a) :=
  (functor a).mapCocone c

/-- Each mapped cocone leg is the entire actual coefficient-map transformation. -/
theorem coefficientCoconeImage_ι (c : Cocone K) (j : J) :
    (coefficientCoconeImage a K c).ι.app j = coefficientMap a (c.ι.app j) := rfl

/-- Every mapped leg retains its coefficient-right tensor component. -/
theorem coefficientCoconeImage_component (c : Cocone K) (j : J) (b : A) :
    EnrichedFunctorCat.component ((coefficientCoconeImage a K c).ι.app j) b =
      c.ι.app j ▷ (a ⟶[V] b) := by
  change EnrichedFunctorCat.component (coefficientMap a (c.ι.app j)) b = _
  exact coefficientMap_component a (c.ι.app j) b

/-- The full mapped cocone is colimiting through the actual chosen Free adjunction. -/
def coefficientCoconeImageIsColimit (c : Cocone K) (hc : IsColimit c) :
    IsColimit (coefficientCoconeImage a K c) := by
  letI : PreservesColimitsOfShape J (functor (V := V) a) :=
    (adjunction (V := V) a).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact isColimitOfPreserves (functor a) hc

variable (F : EnrichedFunctorCat V A)
  (legs : ∀ j : J, object a (K.obj j) ⟶ F)
  (natural : ∀ {j j' : J} (f : j ⟶ j'), (functor a).map (K.map f) ≫ legs j' = legs j)

/-- The coefficient cocone of a compatible full Free transformation family. -/
def evaluatedCocone : Cocone K where
  pt := F.toEnrichedFunctor.obj a
  ι :=
    { app := fun j => evaluate a (K.obj j) F (legs j)
      naturality := fun j j' f => by
        have h := congrArg (evaluate a (K.obj j) F) (natural f)
        rw [evaluate_precomp] at h
        simpa using h }

/-- Each evaluated cocone leg is the original complete identity evaluation. -/
theorem evaluatedCocone_ι (j : J) :
    (evaluatedCocone a K F legs natural).ι.app j =
      evaluate a (K.obj j) F (legs j) := rfl

variable [HasColimit K]

/-- Descend a full compatible Free family by its actual coefficient colimit. -/
def coefficientColimitDesc : object a (colimit K) ⟶ F :=
  extend a (colimit K) F (colimit.desc K (evaluatedCocone a K F legs natural))

/-- The descent evaluates to the actual scalar colimit descent, as an entire function. -/
theorem coefficientColimitDesc_evaluate :
    evaluate a (colimit K) F (coefficientColimitDesc a K F legs natural) =
      colimit.desc K (evaluatedCocone a K F legs natural) :=
  evaluate_extend a (colimit K) F _

/-- The complete descended Free transformation retains every original coefficient leg. -/
theorem coefficientColimitDesc_ι (j : J) :
    (functor a).map (colimit.ι K j) ≫ coefficientColimitDesc a K F legs natural = legs j := by
  apply (homEquiv a (K.obj j) F).injective
  change evaluate a (K.obj j) F ((functor a).map _ ≫ _) =
    evaluate a (K.obj j) F (legs j)
  rw [evaluate_precomp, coefficientColimitDesc_evaluate]
  exact colimit.ι_desc (evaluatedCocone a K F legs natural) j

/-- Every original full transformation is uniquely determined by the complete coefficient family. -/
theorem coefficientColimitDesc_unique (t : object a (colimit K) ⟶ F)
    (ht : ∀ j : J, (functor a).map (colimit.ι K j) ≫ t = legs j) :
    t = coefficientColimitDesc a K F legs natural := by
  apply (homEquiv a (colimit K) F).injective
  change evaluate a (colimit K) F t =
    evaluate a (colimit K) F (coefficientColimitDesc a K F legs natural)
  rw [coefficientColimitDesc_evaluate]
  apply colimit.hom_ext
  intro j
  have h := congrArg (evaluate a (K.obj j) F) (ht j)
  rw [evaluate_precomp] at h
  exact h.trans (colimit.ι_desc (evaluatedCocone a K F legs natural) j).symm

/-- The complete coefficient descent has the original full Hom-action component. -/
theorem coefficientColimitDesc_component (b : A) :
    EnrichedFunctorCat.component (coefficientColimitDesc a K F legs natural) b =
      (colimit.desc K (evaluatedCocone a K F legs natural) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) := by
  change EnrichedFunctorCat.component
    (extend a (colimit K) F (colimit.desc K (evaluatedCocone a K F legs natural))) b = _
  exact extend_component a (colimit K) F _ b

end Colimits

end CategoryTheory.EnrichedFunctorCat.Free
