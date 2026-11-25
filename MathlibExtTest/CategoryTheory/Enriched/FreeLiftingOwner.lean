/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeLifting

/-!
Complete fixed expected interfaces of every new mathematical client.
These signatures are literal source statements; no typeOf/expected-type query occurs at build.
The complete original unit, coefficient, colimit and lift probes accompany these interfaces.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uA uV vV uJ vJ

namespace CategoryTheory.EnrichedFunctorCat.Free.LiftingOwner
open CategoryTheory.EnrichedFunctorCat.Free

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]


/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceEvaluatePrecomp (a : A) {X Y : V} (F : EnrichedFunctorCat V A)
    (f : X ⟶ Y) (t : object a Y ⟶ F) :
    evaluate a X F ((functor a).map f ≫ t) = f ≫ evaluate a Y F t :=
  evaluate_precomp a F f t

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceExtendPostcomp (a : A) (X : V) {F G : EnrichedFunctorCat V A}
    (f : X ⟶ F.toEnrichedFunctor.obj a) (p : F ⟶ G) :
    extend a X F f ≫ p =
      extend a X G (f ≫ (EnrichedFunctorCat.evaluation a).map p) :=
  extend_postcomp a X f p
section Squares
variable (a : A) {X Y : V} {F G : EnrichedFunctorCat V A}
  (i : X ⟶ Y) (p : F ⟶ G)
  (u : object a X ⟶ F) (v : object a Y ⟶ G)


/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientSquare (s : CommSq u ((functor a).map i) p v) :
    CommSq (evaluate a X F u) i
      ((EnrichedFunctorCat.evaluation a).map p) (evaluate a Y G v) :=
  coefficientSquare a i p u v s

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceExtensionSquare
    (x : X ⟶ F.toEnrichedFunctor.obj a) (y : Y ⟶ G.toEnrichedFunctor.obj a)
    (s : CommSq x i ((EnrichedFunctorCat.evaluation a).map p) y) :
    CommSq (extend a X F x) ((functor a).map i) p (extend a Y G y) :=
  extensionSquare a i p x y s

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientLiftStructEquiv (s : CommSq u ((functor a).map i) p v) :
    s.LiftStruct ≃ (coefficientSquare a i p u v s).LiftStruct :=
  coefficientLiftStructEquiv a i p u v s

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceEvaluateLift (s : CommSq u ((functor a).map i) p v) (l : s.LiftStruct) :
    (coefficientSquare a i p u v s).LiftStruct :=
  evaluateLift a i p u v s l

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceExtendLift (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) : s.LiftStruct :=
  extendLift a i p u v s l

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceEvaluateLiftL (s : CommSq u ((functor a).map i) p v) (l : s.LiftStruct) :
    (evaluateLift a i p u v s l).l = evaluate a Y F l.l :=
  evaluateLift_l a i p u v s l

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceExtendLiftL (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) :
    (extendLift a i p u v s l).l = extend a Y F l.l :=
  extendLift_l a i p u v s l

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceExtendEvaluateLift (s : CommSq u ((functor a).map i) p v) (l : s.LiftStruct) :
    extendLift a i p u v s (evaluateLift a i p u v s l) = l :=
  extend_evaluateLift a i p u v s l

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceEvaluateExtendLift (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) :
    evaluateLift a i p u v s (extendLift a i p u v s l) = l :=
  evaluate_extendLift a i p u v s l

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceExtendLiftComponent (s : CommSq u ((functor a).map i) p v)
    (l : (coefficientSquare a i p u v s).LiftStruct) (b : A) :
    EnrichedFunctorCat.component (extendLift a i p u v s l).l b =
      (l.l ⊗ₘ 𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) :=
  extendLift_component a i p u v s l b

end Squares
section Colimits
variable {J : Type uJ} [Category.{vJ} J] (a : A) (K : J ⥤ V)


/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientCoconeImage (c : Cocone K) : Cocone (K ⋙ functor a) :=
  coefficientCoconeImage a K c

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientCoconeImageΙ (c : Cocone K) (j : J) :
    (coefficientCoconeImage a K c).ι.app j = coefficientMap a (c.ι.app j) :=
  coefficientCoconeImage_ι a K c j

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientCoconeImageComponent (c : Cocone K) (j : J) (b : A) :
    EnrichedFunctorCat.component ((coefficientCoconeImage a K c).ι.app j) b =
      c.ι.app j ▷ (a ⟶[V] b) :=
  coefficientCoconeImage_component a K c j b

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientCoconeImageIsColimit (c : Cocone K) (hc : IsColimit c) :
    IsColimit (coefficientCoconeImage a K c) :=
  coefficientCoconeImageIsColimit a K c hc
variable (F : EnrichedFunctorCat V A)
  (legs : ∀ j : J, object a (K.obj j) ⟶ F)
  (natural : ∀ {j j' : J} (f : j ⟶ j'), (functor a).map (K.map f) ≫ legs j' = legs j)


/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceEvaluatedCocone : Cocone K :=
  evaluatedCocone a K F legs natural

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceEvaluatedCoconeΙ (j : J) :
    (evaluatedCocone a K F legs natural).ι.app j =
      evaluate a (K.obj j) F (legs j) :=
  evaluatedCocone_ι a K F legs natural j
variable [HasColimit K]


/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientColimitDesc : object a (colimit K) ⟶ F :=
  coefficientColimitDesc a K F legs natural

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientColimitDescEvaluate :
    evaluate a (colimit K) F (coefficientColimitDesc a K F legs natural) =
      colimit.desc K (evaluatedCocone a K F legs natural) :=
  coefficientColimitDesc_evaluate a K F legs natural

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientColimitDescΙ (j : J) :
    (functor a).map (colimit.ι K j) ≫ coefficientColimitDesc a K F legs natural = legs j :=
  coefficientColimitDesc_ι a K F legs natural j

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientColimitDescUnique (t : object a (colimit K) ⟶ F)
    (ht : ∀ j : J, (functor a).map (colimit.ι K j) ≫ t = legs j) :
    t = coefficientColimitDesc a K F legs natural :=
  coefficientColimitDesc_unique a K F legs natural t ht

/-- Fixed literal expected signature of the complete actual mathematical function. -/
abbrev sourceCoefficientColimitDescComponent (b : A) :
    EnrichedFunctorCat.component (coefficientColimitDesc a K F legs natural) b =
      (colimit.desc K (evaluatedCocone a K F legs natural) ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (F.toEnrichedFunctor.map a b) :=
  coefficientColimitDesc_component a K F legs natural b
end Colimits
end CategoryTheory.EnrichedFunctorCat.Free.LiftingOwner

namespace CategoryTheory.EnrichedFunctorCat.Free.LiftingOwner.Probes
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat.Free
open scoped MonoidalClosed
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {A : Type uA} [EnrichedCategory V A]

/-- The entire actual identity Free square retains the original coefficient identity map. -/
theorem identitySquare (a : A) (X : V) :
    CommSq (𝟙 (object a X)) ((functor a).map (𝟙 X))
      (𝟙 (object a X)) (𝟙 (object a X)) := by
  exact ⟨(Category.comp_id _).trans
    (((functor a).map_id X).symm.trans (Category.comp_id _).symm)⟩

/-- The actual identity natural transformation is a lift of that original square. -/
def identityLift (a : A) (X : V) : (identitySquare a X).LiftStruct where
  l := 𝟙 (object a X)
  fac_left := by rw [(functor a).map_id, Category.id_comp]
  fac_right := Category.comp_id _

/-- The original enriched unit is the actual evaluated identity lift. -/
theorem evaluated_identity_unit (a : A) (X : V) :
    (evaluateLift a (𝟙 X) (𝟙 (object a X)) (𝟙 (object a X))
      (𝟙 (object a X)) (identitySquare a X) (identityLift a X)).l =
      (ρ_ X).inv ≫ X ◁ eId V a := by
  rw [evaluateLift_l]
  simp only [identityLift, evaluate, EnrichedFunctorCat.component_id, Category.comp_id]

/-- Extension of the original enriched unit recovers the entire identity Free transformation. -/
theorem extended_original_unit (a : A) (X : V) :
    extend a X (object a X) ((ρ_ X).inv ≫ X ◁ eId V a) = 𝟙 (object a X) := by
  have h := extend_evaluate a X (object a X) (𝟙 (object a X))
  simpa only [evaluate, EnrichedFunctorCat.component_id, Category.comp_id] using h

/-- The full coefficient lift and Free lift maps reconstruct the original identity structure. -/
theorem identity_lift_roundtrip (a : A) (X : V) :
    extendLift a (𝟙 X) (𝟙 (object a X)) (𝟙 (object a X))
      (𝟙 (object a X)) (identitySquare a X)
      (evaluateLift a (𝟙 X) (𝟙 (object a X)) (𝟙 (object a X))
        (𝟙 (object a X)) (identitySquare a X) (identityLift a X)) =
      identityLift a X :=
  extend_evaluateLift _ _ _ _ _ _ _

/-- The complete original coefficient map is recovered from its exact identity evaluation. -/
theorem original_coefficient_map_recovered (a : A) {X Y : V} (f : X ⟶ Y) :
    extend a X (object a Y) (evaluate a X (object a Y) (coefficientMap a f)) =
      coefficientMap a f :=
  extend_evaluate a X (object a Y) (coefficientMap a f)

variable {J : Type uJ} [Category.{vJ} J] (a : A) (K : J ⥤ V) [HasColimit K]

/-- Every original scalar colimit leg maps through the actual full Free functor. -/
theorem canonical_colimit_legs_natural {j j' : J} (f : j ⟶ j') :
    (functor a).map (K.map f) ≫ (functor a).map (colimit.ι K j') =
      (functor a).map (colimit.ι K j) := by
  rw [← (functor a).map_comp, colimit.w]

/-- The whole canonical Free colimit family descends to the original identity transformation. -/
theorem canonical_colimit_desc_identity :
    coefficientColimitDesc a K (object a (colimit K))
      (fun j => (functor a).map (colimit.ι K j)) (canonical_colimit_legs_natural a K) =
      𝟙 (object a (colimit K)) := by
  symm
  apply coefficientColimitDesc_unique
  intro j
  exact Category.comp_id _

/-- That entire identity descent evaluates by the original coefficient tensor unit. -/
theorem canonical_colimit_desc_evaluated :
    evaluate a (colimit K) (object a (colimit K))
      (coefficientColimitDesc a K (object a (colimit K))
        (fun j => (functor a).map (colimit.ι K j)) (canonical_colimit_legs_natural a K)) =
      (ρ_ (colimit K)).inv ≫ (colimit K) ◁ eId V a := by
  rw [canonical_colimit_desc_identity]
  simp only [evaluate, EnrichedFunctorCat.component_id, Category.comp_id]

end CategoryTheory.EnrichedFunctorCat.Free.LiftingOwner.Probes
