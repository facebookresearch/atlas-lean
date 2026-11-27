/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.TransformationDescent
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Generators
public import MathlibExt.CategoryTheory.Enriched.LeftKanExtension

/-!
# Day convolution as an enriched left Kan extension

The selected Day coends and the selected left Kan coends are compared through
their original universal properties. The forward map contracts the genuine Kan
unit, and the inverse is the Kan transpose of the genuine Day generators.
Both maps preserve the entire original generator families. No identification
of chosen colimit presentations is used, and the base need only be braided.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uV vV uC uD uK

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.LeftKanComparison

open EnrichedFunctorCat

attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]

/-- The actual external tensor, bundled in the category of genuine transformations. -/
abbrev externalObject (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) :
    EnrichedFunctorCat V (C × D) := ⟨F.externalTensor G⟩

variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- The original enriched Day output with its full output-Hom action. -/
abbrev dayObject : EnrichedFunctorCat V K := ⟨Output.functor T F G⟩

variable
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) A.toEnrichedFunctor)]
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) A.toEnrichedFunctor)]
  [∀ (A : EnrichedFunctorCat V (C × D)) (k : K),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) A.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) A.toEnrichedFunctor)]

/-- Contract the original Day coend using the actual genuine left Kan unit. -/
def toKan : dayObject T F G ⟶ leftKanObject T (externalObject F G) :=
  ActionFromTransformation.transformation T F G
    (leftKanObject T (externalObject F G)).toEnrichedFunctor
    (leftKanUnit T (externalObject F G))

/-- Transpose the actual Day generator transformation through the original Kan coend. -/
def fromKan : leftKanObject T (externalObject F G) ⟶ dayObject T F G :=
  leftKanTransposeMap T (externalObject F G) (dayObject T F G)
    (Generators.transformation T F G)

/-- The forward component is literally the original Day contraction. -/
theorem toKan_component (k : K) :
    component (toKan T F G) k =
      ActionFromTransformation.desc T F G
        (leftKanObject T (externalObject F G)).toEnrichedFunctor
        (leftKanUnit T (externalObject F G)) k :=
  ActionFromTransformation.transformation_component _ _ _ _ _ _

/-- The inverse component is literally the original Kan transpose. -/
theorem fromKan_component (k : K) :
    component (fromKan T F G) k =
      leftKanTransposeMapComponent T (externalObject F G) (dayObject T F G)
        (Generators.transformation T F G) k :=
  leftKanTransposeMap_component _ _ _ _ _

/-- Every whole original Day generator maps to the whole original Kan generator. -/
@[reassoc]
theorem gen_toKan (k : K) (a : C × D) :
    EnrichedDayKernel.gen T F G k a ≫ component (toKan T F G) k =
      Enriched.weightedCoend.ι (leftKanWeight T k) (F.externalTensor G) a := by
  change EnrichedDayKernel.gen T F G k a ≫
    (eHomEquiv V).symm ((ActionFromTransformation.transformation T F G
      (leftKanObject T (externalObject F G)).toEnrichedFunctor
      (leftKanUnit T (externalObject F G))).app k) = _
  rw [ActionFromTransformation.gen_transformation, ActionFromTransformation.generator_eq]
  change ((T.obj a ⟶[V] k) ◁ component (leftKanUnit T (externalObject F G)) a) ≫
      (β_ (T.obj a ⟶[V] k)
        (leftKanCoendObject T (F.externalTensor G) (T.obj a))).hom ≫
      MonoidalClosed.uncurry (leftKanCoendMap T (F.externalTensor G) (T.obj a) k) = _
  rw [leftKanUnit_component, leftKanCoendMap_uncurry]
  exact (congrArg
    (fun q => ((T.obj a ⟶[V] k) ◁ leftKanUnitComponent T (externalObject F G) a) ≫ q)
    (Iso.hom_inv_id_assoc
      (β_ (T.obj a ⟶[V] k) (leftKanCoendObject T (F.externalTensor G) (T.obj a)))
      (leftKanCoendAction T (F.externalTensor G) (T.obj a) k))).trans
    (leftKanUnitComponent_action T (externalObject F G) a k)

/-- Every whole original Kan generator maps to the whole original Day generator. -/
@[reassoc]
theorem ι_fromKan (k : K) (a : C × D) :
    Enriched.weightedCoend.ι (leftKanWeight T k) (F.externalTensor G) a ≫
        component (fromKan T F G) k = EnrichedDayKernel.gen T F G k a := by
  rw [fromKan_component, leftKanTransposeMapComponent_ι, leftKanTransposeCocone_eq]
  change (𝟙 (T.obj a ⟶[V] k) ⊗ₘ
      (eHomEquiv V).symm ((Generators.transformation T F G).app a)) ≫
      (β_ (T.obj a ⟶[V] k) (EnrichedDayKernel.obj T F G (T.obj a))).hom ≫
      MonoidalClosed.uncurry (Output.map T F G (T.obj a) k) = _
  rw [Generators.transformation_component]
  let W : V := T.obj a ⟶[V] k
  let Q : V := (F.externalTensor G).obj a
  let E : V := EnrichedDayKernel.obj T F G (T.obj a)
  let p : Q ⟶ E := Generators.point T F G a
  let m : E ⊗ W ⟶ EnrichedDayKernel.obj T F G k :=
    MonoidalClosed.uncurry (Output.map T F G (T.obj a) k)
  let γ : W ⊗ Q ⟶ EnrichedDayKernel.obj T F G k := EnrichedDayKernel.gen T F G k a
  have hPoint : (p ⊗ₘ 𝟙 W) ≫ m =
      (β_ W Q).inv ≫ γ := by
    have h := Generators.point_output T F G a k (𝟙 W)
    have h' : (p ⊗ₘ 𝟙 W) ≫ m = (β_ W Q).inv ≫ (𝟙 W ⊗ₘ 𝟙 Q) ≫ γ := by
      simpa only [W, Q, E, p, m, γ, whiskerLeft_id, Category.id_comp] using h
    exact h'.trans ((congrArg (fun q => (β_ W Q).inv ≫ q ≫ γ) (id_tensorHom_id W Q)).trans
      (congrArg (fun q => (β_ W Q).inv ≫ q) (Category.id_comp γ)))
  have hBraid := braiding_naturality (𝟙 W) p
  change (𝟙 W ⊗ₘ p) ≫ (β_ W E).hom ≫ m = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ m) hBraid).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => (β_ W Q).hom ≫ q) hPoint).trans
          (Iso.hom_inv_id_assoc (β_ W Q) γ))))

/-- Both whole Day compositions are tested on the complete original Day family. -/
theorem toKan_fromKan : toKan T F G ≫ fromKan T F G = 𝟙 (dayObject T F G) := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  refine (component_comp (toKan T F G) (fromKan T F G) k).trans ?_
  refine Eq.trans ?_ (component_id (dayObject T F G) k).symm
  apply EnrichedDayKernel.hom_ext T F G k
  intro a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ component (fromKan T F G) k)
      (gen_toKan T F G k a)).trans
        ((ι_fromKan T F G k a).trans (Category.comp_id _).symm))

/-- Both whole Kan compositions are tested on the complete original Kan family. -/
theorem fromKan_toKan :
    fromKan T F G ≫ toKan T F G = 𝟙 (leftKanObject T (externalObject F G)) := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  refine (component_comp (fromKan T F G) (toKan T F G) k).trans ?_
  refine Eq.trans ?_ (component_id (leftKanObject T (externalObject F G)) k).symm
  apply Enriched.weightedCoend.hom_ext (leftKanWeight T k) (F.externalTensor G)
  intro a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ component (toKan T F G) k)
      (ι_fromKan T F G k a)).trans
        ((gen_toKan T F G k a).trans (Category.comp_id _).symm))

/-- The genuine enriched Day/Kan isomorphism has the two original universal-property maps. -/
def iso : dayObject T F G ≅ leftKanObject T (externalObject F G) where
  hom := toKan T F G
  inv := fromKan T F G
  hom_inv_id := toKan_fromKan T F G
  inv_hom_id := fromKan_toKan T F G

/-- The chosen forward map is the actual Day contraction of the Kan unit. -/
theorem iso_hom : (iso T F G).hom = toKan T F G := rfl

/-- The chosen inverse is the actual Kan transpose of the Day generators. -/
theorem iso_inv : (iso T F G).inv = fromKan T F G := rfl

/-- Full output-Hom naturality of the original forward comparison. -/
theorem toKan_full_naturality (k l : K) :
    MonoidalClosed.uncurry ((Output.functor T F G).map k l) ≫
        component (toKan T F G) l =
      (component (toKan T F G) k ⊗ₘ 𝟙 (k ⟶[V] l)) ≫
        MonoidalClosed.uncurry
          ((leftKanObject T (externalObject F G)).toEnrichedFunctor.map k l) :=
  GradedNatTrans.uncurriedNaturality (toKan T F G) k l

/-- Full output-Hom naturality of the original inverse comparison. -/
theorem fromKan_full_naturality (k l : K) :
    MonoidalClosed.uncurry
        ((leftKanObject T (externalObject F G)).toEnrichedFunctor.map k l) ≫
        component (fromKan T F G) l =
      (component (fromKan T F G) k ⊗ₘ 𝟙 (k ⟶[V] l)) ≫
        MonoidalClosed.uncurry ((Output.functor T F G).map k l) :=
  GradedNatTrans.uncurriedNaturality (fromKan T F G) k l

end CategoryTheory.EnrichedDayKernel.LeftKanComparison
