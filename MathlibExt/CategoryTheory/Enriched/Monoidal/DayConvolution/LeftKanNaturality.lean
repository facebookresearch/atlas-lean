/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LeftKanComparison

/-!
# Unit and input naturality of the original Day/Kan comparison

The two original units agree through the actual comparison maps. Both complete
input transformations commute with those maps by testing their original Day
and Kan generator families. Inverse naturality follows from the proved inverse
laws. The hypotheses retain only the two endpoint Day presentations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uV vV uC uD uK

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.LeftKanComparison

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) A.toEnrichedFunctor)]
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) A.toEnrichedFunctor)]
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) A.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) A.toEnrichedFunctor)]

section Units

variable (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- The actual identity-insertion points map to the actual Kan unit components. -/
@[reassoc]
theorem point_toKan (a : C × D) :
    Generators.point T F G a ≫ component (toKan T F G) (T.obj a) =
      leftKanUnitComponent T (externalObject F G) a := by
  let Q : V := (F.externalTensor G).obj a
  let W : V := T.obj a ⟶[V] T.obj a
  let ins : Q ⟶ W ⊗ Q := (λ_ Q).inv ≫ (eId V (T.obj a) ⊗ₘ 𝟙 Q)
  let γ : W ⊗ Q ⟶ EnrichedDayKernel.obj T F G (T.obj a) :=
    EnrichedDayKernel.gen T F G (T.obj a) a
  let ι : W ⊗ Q ⟶ leftKanCoendObject T (F.externalTensor G) (T.obj a) :=
    Enriched.weightedCoend.ι (leftKanWeight T (T.obj a)) (F.externalTensor G) a
  have hPoint : Generators.point T F G a = ins ≫ γ := (Category.assoc _ _ _).symm
  have hUnit : leftKanUnitComponent T (externalObject F G) a = ins ≫ ι :=
    (congrArg (fun r => (λ_ Q).inv ≫ r ≫ ι) (tensorHom_id (eId V (T.obj a)) Q).symm).trans
      (Category.assoc _ _ _).symm
  exact (congrArg (fun r => r ≫ component (toKan T F G) (T.obj a)) hPoint).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun r => ins ≫ r) (gen_toKan T F G (T.obj a) a)).trans hUnit.symm))

/-- The original Day generator transformation becomes the original genuine Kan unit. -/
theorem generators_toKan :
    Generators.transformation T F G ≫ restrictionMap T (toKan T F G) =
      leftKanUnit T (externalObject F G) := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  exact (component_comp _ _ a).trans
    ((congrArg₂ (fun r s => r ≫ s) (Generators.transformation_component T F G a)
      (restrictionMap_component T (toKan T F G) a)).trans
        ((point_toKan T F G a).trans (leftKanUnit_component T (externalObject F G) a).symm))

/-- The original genuine Kan unit becomes the original Day generator transformation. -/
theorem unit_fromKan :
    leftKanUnit T (externalObject F G) ≫ restrictionMap T (fromKan T F G) =
      Generators.transformation T F G :=
  leftKanHomToRestriction_transpose T (externalObject F G) (dayObject T F G)
    (Generators.transformation T F G)

end Units

section InputNaturality

variable {F F' : EnrichedFunctor V C V} {G G' : EnrichedFunctor V D V}
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F' G' k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F' G' k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F' G' k)
    (EnrichedDayKernel.rightMap T F' G' k)]

/-- The actual forward comparison is natural in both complete genuine input maps. -/
theorem input_toKan
    (p : (⟨F⟩ : EnrichedFunctorCat V C) ⟶ ⟨F'⟩)
    (q : (⟨G⟩ : EnrichedFunctorCat V D) ⟶ ⟨G'⟩) :
    Input.natTrans T p q ≫ toKan T F' G' =
      toKan T F G ≫ leftKanMap T (X := externalObject F G) (X' := externalObject F' G')
        (EnrichedFunctor.externalMap p q) := by
  let d : dayObject T F G ⟶ dayObject T F' G' := Input.natTrans T p q
  let r : externalObject F G ⟶ externalObject F' G' := EnrichedFunctor.externalMap p q
  let l := leftKanMap T r
  apply EnrichedFunctorCat.hom_ext
  intro k
  refine (component_comp d (toKan T F' G') k).trans ?_
  refine Eq.trans ?_ (component_comp (toKan T F G) l k).symm
  apply EnrichedDayKernel.hom_ext T F G k
  intro a
  let W : V := T.obj a ⟶[V] k
  let c : (F.externalTensor G).obj a ⟶ (F'.externalTensor G').obj a :=
    component p a.1 ⊗ₘ component q a.2
  let cW := 𝟙 W ⊗ₘ c
  let γ : W ⊗ (F.externalTensor G).obj a ⟶ EnrichedDayKernel.obj T F G k :=
    EnrichedDayKernel.gen T F G k a
  let γ' : W ⊗ (F'.externalTensor G').obj a ⟶ EnrichedDayKernel.obj T F' G' k :=
    EnrichedDayKernel.gen T F' G' k a
  let ι : W ⊗ (F.externalTensor G).obj a ⟶ leftKanCoendObject T (F.externalTensor G) k :=
    Enriched.weightedCoend.ι (leftKanWeight T k) (F.externalTensor G) a
  let ι' : W ⊗ (F'.externalTensor G').obj a ⟶ leftKanCoendObject T (F'.externalTensor G') k :=
    Enriched.weightedCoend.ι (leftKanWeight T k) (F'.externalTensor G') a
  have hDay : γ ≫ component d k = cW ≫ γ' :=
    (congrArg (fun s => γ ≫ s) (Input.natTrans_component T p q k)).trans
      (Input.gen_mapAt T p q k a)
  have hKan : ι ≫ component l k = cW ≫ ι' :=
    (congrArg (fun s => ι ≫ s) (leftKanMap_component T r k)).trans
      ((leftKanMapComponent_ι T r k a).trans
        (congrArg (fun s => (𝟙 W ⊗ₘ s) ≫ ι') (EnrichedFunctor.externalMap_component p q a)))
  have hLeft : γ ≫ (component d k ≫ component (toKan T F' G') k) = cW ≫ ι' :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun s => s ≫ component (toKan T F' G') k) hDay).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun s => cW ≫ s) (gen_toKan T F' G' k a))))
  have hRight : γ ≫ (component (toKan T F G) k ≫ component l k) = cW ≫ ι' :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun s => s ≫ component l k) (gen_toKan T F G k a)).trans hKan)
  exact hLeft.trans hRight.symm

/-- Inverse input naturality is derived from the actual two whole inverse laws. -/
theorem input_fromKan
    (p : (⟨F⟩ : EnrichedFunctorCat V C) ⟶ ⟨F'⟩)
    (q : (⟨G⟩ : EnrichedFunctorCat V D) ⟶ ⟨G'⟩) :
    leftKanMap T (X := externalObject F G) (X' := externalObject F' G')
        (EnrichedFunctor.externalMap p q) ≫ fromKan T F' G' =
      fromKan T F G ≫ Input.natTrans T p q := by
  let d : dayObject T F G ⟶ dayObject T F' G' := Input.natTrans T p q
  let r : externalObject F G ⟶ externalObject F' G' := EnrichedFunctor.externalMap p q
  let l := leftKanMap T r
  have hLeft : toKan T F G ≫ (l ≫ fromKan T F' G') = d :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun s => s ≫ fromKan T F' G') (input_toKan T p q).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun s => d ≫ s) (toKan_fromKan T F' G')).trans (Category.comp_id d))))
  have hRight : toKan T F G ≫ (fromKan T F G ≫ d) = d :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun s => s ≫ d) (toKan_fromKan T F G)).trans (Category.id_comp d))
  exact (cancel_epi (iso T F G).hom).1 (hLeft.trans hRight.symm)

end InputNaturality

end CategoryTheory.EnrichedDayKernel.LeftKanComparison
