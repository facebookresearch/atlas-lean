/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.PointwiseColimitReflection

/-!
# Whole original enriched cocone reflection tests

Each expected type retains the original cocone point and both morphism
domains. The full descender has original Hom naturality, component functions
and UP behavior even when neither source is cofibrant or ordinarily indexed.
-/

set_option autoImplicit false
noncomputable section
universe uA uV vV uJ vJ

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace EnrichedCoconeReflectionTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {J : Type uJ} [Category.{vJ} J]
  {K : J ⥤ EnrichedFunctorCat V A}

section OriginalCocone

variable (c : Cocone K)
  (hc : ∀ a : A, IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone c))

/-- The fixed expected UP has the original enriched point and all original legs. -/
def wholeOriginalCocone : IsColimit c :=
  EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc

example (q : Cocone K) : c.pt ⟶ q.pt :=
  EnrichedFunctorCat.descOfEvaluations c hc q

example (q : Cocone K) (a : A) :
    EnrichedFunctorCat.component (EnrichedFunctorCat.descOfEvaluations c hc q) a =
      (hc a).desc ((EnrichedFunctorCat.evaluation a).mapCocone q) :=
  EnrichedFunctorCat.descOfEvaluations_component c hc q a

example :
    (fun (q : Cocone K) (a : A) =>
      EnrichedFunctorCat.component
        ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).desc q) a) =
      fun q a => (hc a).desc ((EnrichedFunctorCat.evaluation a).mapCocone q) :=
  EnrichedFunctorCat.evaluationJointlyReflectsColimits_desc_function c hc

example (q : Cocone K) (a b : A) :
    MonoidalClosed.uncurry (c.pt.toEnrichedFunctor.map a b) ≫
        EnrichedFunctorCat.component (EnrichedFunctorCat.descOfEvaluations c hc q) b =
      (EnrichedFunctorCat.component (EnrichedFunctorCat.descOfEvaluations c hc q) a ⊗ₘ
        𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (q.pt.toEnrichedFunctor.map a b) :=
  (EnrichedFunctorCat.descOfEvaluations c hc q).uncurriedNaturality a b

example (q : Cocone K) (a b : A) :
    MonoidalClosed.uncurry (c.pt.toEnrichedFunctor.map a b) ≫
        (hc b).desc ((EnrichedFunctorCat.evaluation b).mapCocone q) =
      ((hc a).desc ((EnrichedFunctorCat.evaluation a).mapCocone q) ⊗ₘ
        𝟙 (a ⟶[V] b)) ≫ MonoidalClosed.uncurry (q.pt.toEnrichedFunctor.map a b) := by
  have h := (EnrichedFunctorCat.descOfEvaluations c hc q).uncurriedNaturality a b
  simpa only [Functor.mapCocone_pt, EnrichedFunctorCat.evaluation_obj,
    EnrichedFunctorCat.descOfEvaluations_component] using h

example (q : Cocone K) (j : J) :
    c.ι.app j ≫ (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).desc q =
      q.ι.app j :=
  (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).fac q j

example (q : Cocone K) (j : J) (a : A) :
    EnrichedFunctorCat.component (c.ι.app j) a ≫
        EnrichedFunctorCat.component
          ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).desc q) a =
      EnrichedFunctorCat.component (q.ι.app j) a := by
  have h := congrArg (fun m => EnrichedFunctorCat.component m a)
    ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).fac q j)
  simpa only [EnrichedFunctorCat.component_comp] using h

example (q : Cocone K) (m : c.pt ⟶ q.pt)
    (hm : ∀ j : J, c.ι.app j ≫ m = q.ι.app j) :
    m = (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).desc q :=
  (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).uniq q m hm

example (q : Cocone K) (m n : c.pt ⟶ q.pt)
    (hm : ∀ j : J, c.ι.app j ≫ m = q.ι.app j)
    (hn : ∀ j : J, c.ι.app j ≫ n = q.ι.app j) : m = n :=
  ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).uniq q m hm).trans
    ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).uniq q n hn).symm

example (m n : c.pt ⟶ c.pt)
    (h : ∀ j : J, c.ι.app j ≫ m = c.ι.app j ≫ n) : m = n :=
  (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).hom_ext h

example : (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).desc c = 𝟙 c.pt := by
  apply (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).hom_ext
  intro j
  simp only [IsColimit.fac, Category.comp_id]

example (h : IsColimit c) (q : Cocone K) :
    EnrichedFunctorCat.descOfEvaluations c hc q = h.desc q := by
  apply h.hom_ext
  intro j
  exact ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).fac q j).trans
    (h.fac q j).symm

example (hc' : ∀ a : A, IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone c)) :
    EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc =
      EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc' :=
  Subsingleton.elim _ _

example (hc' : ∀ a : A, IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone c)) :
    (fun q : Cocone K => EnrichedFunctorCat.descOfEvaluations c hc q) =
      fun q => EnrichedFunctorCat.descOfEvaluations c hc' q := by
  funext q
  apply (EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).hom_ext
  intro j
  exact ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc).fac q j).trans
    ((EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc').fac q j).symm

end OriginalCocone

section ActualPushouts

variable [HasPushouts V]
  {X Y Z W : EnrichedFunctorCat V A}
  {i : X ⟶ Y} {f : X ⟶ Z} {f' : Y ⟶ W} {j : Z ⟶ W}

example (hcomm : i ≫ f' = f ≫ j)
    (h : ∀ a : A, IsPushout ((EnrichedFunctorCat.evaluation a).map i)
      ((EnrichedFunctorCat.evaluation a).map f)
      ((EnrichedFunctorCat.evaluation a).map f')
      ((EnrichedFunctorCat.evaluation a).map j)) :
    IsPushout i f f' j :=
  (EnrichedFunctorCat.isPushout_iff_evaluation hcomm).2 h

example (sq : IsPushout i f f' j) (a : A) :
    IsPushout ((EnrichedFunctorCat.evaluation a).map i)
      ((EnrichedFunctorCat.evaluation a).map f)
      ((EnrichedFunctorCat.evaluation a).map f')
      ((EnrichedFunctorCat.evaluation a).map j) :=
  (EnrichedFunctorCat.isPushout_iff_evaluation sq.w).1 sq a

example (hcomm : i ≫ f' = f ≫ j)
    (h : ∀ a : A, IsPushout ((EnrichedFunctorCat.evaluation a).map f)
      ((EnrichedFunctorCat.evaluation a).map i)
      ((EnrichedFunctorCat.evaluation a).map j)
      ((EnrichedFunctorCat.evaluation a).map f')) :
    IsPushout i f f' j := by
  apply (EnrichedFunctorCat.isPushout_iff_evaluation hcomm).2
  intro a
  exact (h a).flip

example (sq : IsPushout i f f' j) (u v : W ⟶ W)
    (h₁ : f' ≫ u = f' ≫ v) (h₂ : j ≫ u = j ≫ v) : u = v :=
  sq.hom_ext h₁ h₂

example (i : X ⟶ Y) :
    IsPushout i (𝟙 X) (𝟙 Y) i :=
  IsPushout.of_id_snd

example (f : X ⟶ Z) :
    IsPushout (𝟙 X) f f (𝟙 Z) :=
  IsPushout.of_id_fst

end ActualPushouts

section ExistingParticularColimit

variable [∀ a : A, HasColimit (K ⋙ EnrichedFunctorCat.evaluation a)]

example :
    IsColimit (EnrichedFunctorCat.PointwiseColimit.cocone K) :=
  EnrichedFunctorCat.evaluationJointlyReflectsColimits
    (EnrichedFunctorCat.PointwiseColimit.cocone K)
    (EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit K)

example (q : Cocone K) :
    EnrichedFunctorCat.descOfEvaluations (EnrichedFunctorCat.PointwiseColimit.cocone K)
        (EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit K) q =
      EnrichedFunctorCat.PointwiseColimit.desc K q := by
  apply (EnrichedFunctorCat.PointwiseColimit.isColimit K).hom_ext
  intro j
  exact (EnrichedFunctorCat.evaluationJointlyReflectsColimits
    (EnrichedFunctorCat.PointwiseColimit.cocone K)
    (EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit K)).fac q j |>.trans
      ((EnrichedFunctorCat.PointwiseColimit.isColimit K).fac q j).symm

example (q : Cocone K) (a : A) :
    EnrichedFunctorCat.component
      (EnrichedFunctorCat.descOfEvaluations (EnrichedFunctorCat.PointwiseColimit.cocone K)
        (EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit K) q) a =
      colimit.desc (K ⋙ EnrichedFunctorCat.evaluation a)
        ((EnrichedFunctorCat.evaluation a).mapCocone q) := by
  have h : EnrichedFunctorCat.descOfEvaluations
      (EnrichedFunctorCat.PointwiseColimit.cocone K)
      (EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit K) q =
      EnrichedFunctorCat.PointwiseColimit.desc K q := by
    apply (EnrichedFunctorCat.PointwiseColimit.isColimit K).hom_ext
    intro j
    exact (EnrichedFunctorCat.evaluationJointlyReflectsColimits
      (EnrichedFunctorCat.PointwiseColimit.cocone K)
      (EnrichedFunctorCat.PointwiseColimit.evaluatedIsColimit K)).fac q j |>.trans
        ((EnrichedFunctorCat.PointwiseColimit.isColimit K).fac q j).symm
  rw [h]
  exact EnrichedFunctorCat.PointwiseColimit.desc_component K q a

end ExistingParticularColimit

section EmptySource

variable [EnrichedCategory V PEmpty.{uA + 1}]
  {K₀ : J ⥤ EnrichedFunctorCat V PEmpty.{uA + 1}}

example (c : Cocone K₀) : IsColimit c :=
  EnrichedFunctorCat.evaluationJointlyReflectsColimits c (fun a => nomatch a)

example (c q : Cocone K₀) (m n : c.pt ⟶ q.pt) : m = n := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  exact nomatch a

end EmptySource

section InfiniteOriginalLabels

variable [EnrichedCategory V (ULift.{uA} ℕ)]
  {Kₙ : J ⥤ EnrichedFunctorCat V (ULift.{uA} ℕ)}

example (c : Cocone Kₙ)
    (hc : ∀ a : ULift.{uA} ℕ,
      IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone c)) : IsColimit c :=
  EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc

example (c : Cocone Kₙ)
    (hc : ∀ a : ULift.{uA} ℕ,
      IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone c)) (q : Cocone Kₙ) :
    c.pt ⟶ q.pt :=
  EnrichedFunctorCat.descOfEvaluations c hc q

end InfiniteOriginalLabels

section IndependentRaisedUniverses

variable {V₁ : Type 2} [Category.{1} V₁] [MonoidalCategory V₁]
  [BraidedCategory V₁] [MonoidalClosed V₁]
  {A₃ : Type 3} [EnrichedCategory V₁ A₃]
  {J₀ : Type} [Category.{2} J₀]
  {K₃ : J₀ ⥤ EnrichedFunctorCat V₁ A₃}

example (c : Cocone K₃)
    (hc : ∀ a : A₃, IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone c)) :
    IsColimit c :=
  EnrichedFunctorCat.evaluationJointlyReflectsColimits c hc

example (c : Cocone K₃)
    (hc : ∀ a : A₃, IsColimit ((EnrichedFunctorCat.evaluation a).mapCocone c))
    (q : Cocone K₃) (a : A₃) :
    EnrichedFunctorCat.component (EnrichedFunctorCat.descOfEvaluations c hc q) a =
      (hc a).desc ((EnrichedFunctorCat.evaluation a).mapCocone q) :=
  EnrichedFunctorCat.descOfEvaluations_component c hc q a

end IndependentRaisedUniverses

#check @CategoryTheory.EnrichedFunctorCat.descOfEvaluations
#check @CategoryTheory.EnrichedFunctorCat.descOfEvaluations_component
#check @CategoryTheory.EnrichedFunctorCat.evaluationJointlyReflectsColimits
#check @CategoryTheory.EnrichedFunctorCat.evaluationJointlyReflectsColimits_desc_function
#check @CategoryTheory.EnrichedFunctorCat.isPushout_iff_evaluation

end EnrichedCoconeReflectionTests
