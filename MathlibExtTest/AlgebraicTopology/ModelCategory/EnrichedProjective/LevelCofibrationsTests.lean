/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective.LevelCofibrations

/-!
# Complete original generated-level and chosen-factor clients

All original tensor labels and arbitrary arrow domains are retained. Given
model generation data identify their actual left classes; actual supplied
factor maps are only evaluated, and are never replaced or recomputed.
-/

set_option autoImplicit false
noncomputable section
universe w uA uV vV

open CategoryTheory Limits MorphismProperty MonoidalCategory HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective

namespace EnrichedGeneratedLevelTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [HasColimitsOfSize.{w, w} V]
  (Q : MorphismProperty V)
  [Q.RespectsIso] [Q.IsStableUnderRetracts]
  [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
  [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]

section WholeLeftClass

variable (P : MorphismProperty V)
  [(generators (A := A) P).IsCardinalForSmallObjectArgument κ]
  (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    P f → Q (f ▷ (a ⟶[V] b)))

include κ hTensor in
/-- All original generated left arrows satisfy the fixed full evaluation predicate. -/
theorem whole_generated_class :
    (generators (A := A) P).rlp.llp ≤
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) Q :=
  generatedLeft_le_evaluationProperty (κ := κ) P Q hTensor

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y)
    (hf : (generators (A := A) P).rlp.llp f) (a : A) :
    Q ((EnrichedFunctorCat.evaluation a).map f) :=
  (EvaluationTransfer.evaluationProperty_iff _ Q f).1
    (generatedLeft_le_evaluationProperty (κ := κ) P Q hTensor f hf) a

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y)
    (hf : (generators (A := A) P).rlp.llp f) (a : A) :
    Q (EnrichedFunctorCat.component f a) := by
  exact (EvaluationTransfer.evaluationProperty_iff _ Q f).1
    (generatedLeft_le_evaluationProperty (κ := κ) P Q hTensor f hf) a

example {X Y : V} (f : X ⟶ Y) (hf : P f) (a b : A) :
    Q (EnrichedFunctorCat.component ((EnrichedFunctorCat.Free.functor a).map f) b) := by
  rw [EnrichedFunctorCat.Free.coefficientMap_component]
  exact hTensor a b f hf

example {X Y : V} (f : X ⟶ Y) (hf : P f) (a b : A) :
    Q ((EnrichedFunctorCat.evaluation b).map ((EnrichedFunctorCat.Free.functor a).map f)) := by
  have hgen : generators (A := A) P ((EnrichedFunctorCat.Free.functor a).map f) :=
    map_mem_adjointFamilyGenerators _ P a f hf
  exact (EvaluationTransfer.evaluationProperty_iff _ Q _).1
    (generatedLeft_le_evaluationProperty (κ := κ) P Q hTensor _
      ((generators (A := A) P).le_llp_rlp _ hgen)) b

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y)
    (hf : generators (A := A) P f) :
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) Q f :=
  generatedLeft_le_evaluationProperty (κ := κ) P Q hTensor f
    ((generators (A := A) P).le_llp_rlp f hf)

end WholeLeftClass

section ActualGivenModel

variable [ModelCategory (EnrichedFunctorCat V A)]
  (d : CofibrantGenerationData (EnrichedFunctorCat V A) κ)
  (P : MorphismProperty V)

section GivenI

variable (hI : d.I = generators (A := A) P)
  (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    P f → Q (f ▷ (a ⟶[V] b)))

example :
    cofibrations (EnrichedFunctorCat V A) ≤
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) Q :=
  cofibrations_le_evaluationProperty d P Q hI hTensor

example :
    cofibrations (EnrichedFunctorCat V A) = (generators (A := A) P).rlp.llp := by
  rw [← trivialFibrations_llp, ← d.I_rlp, hI]

example : (generators (A := A) P).IsCardinalForSmallObjectArgument κ := by
  rw [← hI]
  exact d.I_smallObject

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) [Cofibration f] :
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) Q f :=
  cofibrations_le_evaluationProperty d P Q hI hTensor f (mem_cofibrations f)

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y) [Cofibration f] (a : A) :
    Q (EnrichedFunctorCat.component f a) :=
  (EvaluationTransfer.evaluationProperty_iff _ Q f).1
    (cofibrations_le_evaluationProperty d P Q hI hTensor f (mem_cofibrations f)) a

example
    (F : FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A))) (f : Arrow (EnrichedFunctorCat V A)) :
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) Q (F.i.app f) :=
  cofibrations_le_evaluationProperty d P Q hI hTensor (F.i.app f) (F.hi f)

example
    (F : FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A))) (f : Arrow (EnrichedFunctorCat V A))
    (a : A) : Q (EnrichedFunctorCat.component (F.i.app f) a) :=
  (EvaluationTransfer.evaluationProperty_iff _ Q (F.i.app f)).1
    (cofibrations_le_evaluationProperty d P Q hI hTensor (F.i.app f) (F.hi f)) a

example
    (F : FunctorialFactorizationData (cofibrations (EnrichedFunctorCat V A))
      (trivialFibrations (EnrichedFunctorCat V A)))
    {f g : Arrow (EnrichedFunctorCat V A)} (square : f ⟶ g) (a : A) :
    EnrichedFunctorCat.component square.left a ≫
        EnrichedFunctorCat.component (F.i.app g) a =
      EnrichedFunctorCat.component (F.i.app f) a ≫
        EnrichedFunctorCat.component (F.Z.map square) a := by
  have h := congrArg (fun z => EnrichedFunctorCat.component z a) (F.i.naturality square)
  simpa only [EnrichedFunctorCat.component_comp, Arrow.leftFunc_map, Arrow.leftFunc_obj] using h

end GivenI

section GivenJ

variable (hJ : d.J = generators (A := A) P)
  (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    P f → Q (f ▷ (a ⟶[V] b)))

example :
    trivialCofibrations (EnrichedFunctorCat V A) ≤
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) Q :=
  trivialCofibrations_le_evaluationProperty d P Q hJ hTensor

example :
    trivialCofibrations (EnrichedFunctorCat V A) =
      (generators (A := A) P).rlp.llp := by
  rw [← fibrations_llp, ← d.J_rlp, hJ]

example : (generators (A := A) P).IsCardinalForSmallObjectArgument κ := by
  rw [← hJ]
  exact d.J_smallObject

example {X Y : EnrichedFunctorCat V A} (f : X ⟶ Y)
    (hf : trivialCofibrations (EnrichedFunctorCat V A) f) (a : A) :
    Q (EnrichedFunctorCat.component f a) :=
  (EvaluationTransfer.evaluationProperty_iff _ Q f).1
    (trivialCofibrations_le_evaluationProperty d P Q hJ hTensor f hf) a

example
    (F : FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat V A))
      (fibrations (EnrichedFunctorCat V A))) (f : Arrow (EnrichedFunctorCat V A)) :
    EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) Q (F.i.app f) :=
  trivialCofibrations_le_evaluationProperty d P Q hJ hTensor (F.i.app f) (F.hi f)

example
    (F : FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat V A))
      (fibrations (EnrichedFunctorCat V A))) (f : Arrow (EnrichedFunctorCat V A))
    (a : A) : Q (EnrichedFunctorCat.component (F.i.app f) a) :=
  (EvaluationTransfer.evaluationProperty_iff _ Q (F.i.app f)).1
    (trivialCofibrations_le_evaluationProperty d P Q hJ hTensor (F.i.app f) (F.hi f)) a

example
    (F : FunctorialFactorizationData (trivialCofibrations (EnrichedFunctorCat V A))
      (fibrations (EnrichedFunctorCat V A))) (f : Arrow (EnrichedFunctorCat V A))
    (a : A) :
    EnrichedFunctorCat.component (F.i.app f) a ≫
        EnrichedFunctorCat.component (F.p.app f) a =
      EnrichedFunctorCat.component f.hom a := by
  have h := congrArg (fun z => EnrichedFunctorCat.component z a) (F.fac_app (f := f))
  simpa only [EnrichedFunctorCat.component_comp] using h

end GivenJ
end ActualGivenModel

section EmptyOriginalFamily

variable
  [(generators (A := A) (⊥ : MorphismProperty V)).IsCardinalForSmallObjectArgument κ]

example :
    (generators (A := A) (⊥ : MorphismProperty V)).rlp.llp ≤
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) Q :=
  generatedLeft_le_evaluationProperty (κ := κ) (⊥ : MorphismProperty V) Q
    (by intro a b X Y f hf; exact False.elim hf)

end EmptyOriginalFamily

section InfiniteOriginalIndex

variable [EnrichedCategory V (ULift.{uA} ℕ)]
  (P : MorphismProperty V)
  [(generators (A := ULift.{uA} ℕ) P).IsCardinalForSmallObjectArgument κ]
  (hTensor : ∀ a b : ULift.{uA} ℕ, ∀ {X Y : V} (f : X ⟶ Y),
    P f → Q (f ▷ (a ⟶[V] b)))

example :
    (generators (A := ULift.{uA} ℕ) P).rlp.llp ≤
      EvaluationTransfer.evaluationProperty
        (fun a : ULift.{uA} ℕ => EnrichedFunctorCat.evaluation a) Q :=
  generatedLeft_le_evaluationProperty (κ := κ) P Q hTensor

end InfiniteOriginalIndex

section IndependentRaisedTypes

variable {V₂ : Type 2} [Category.{1} V₂] [MonoidalCategory V₂]
  [BraidedCategory V₂] [MonoidalClosed V₂]
  [HasColimitsOfSize.{0, 0} V₂]
  {A₃ : Type 3} [EnrichedCategory V₂ A₃]
  {κ₀ : Cardinal.{0}} [Fact κ₀.IsRegular] [OrderBot κ₀.ord.ToType]
  (P₂ Q₂ : MorphismProperty V₂)
  [(generators (A := A₃) P₂).IsCardinalForSmallObjectArgument κ₀]
  [Q₂.RespectsIso] [Q₂.IsStableUnderRetracts]
  [Q₂.IsStableUnderCoproducts.{0}] [Q₂.IsStableUnderCobaseChange]
  [Q₂.IsStableUnderTransfiniteCompositionOfShape κ₀.ord.ToType]
  (hTensor : ∀ a b : A₃, ∀ {X Y : V₂} (f : X ⟶ Y),
    P₂ f → Q₂ (f ▷ (a ⟶[V₂] b)))

example :
    (generators (A := A₃) P₂).rlp.llp ≤
      EvaluationTransfer.evaluationProperty
        (fun a : A₃ => EnrichedFunctorCat.evaluation a) Q₂ :=
  generatedLeft_le_evaluationProperty (κ := κ₀) P₂ Q₂ hTensor

end IndependentRaisedTypes

#check @HomotopicalAlgebra.EnrichedProjective.generatedLeft_le_evaluationProperty
#check @HomotopicalAlgebra.EnrichedProjective.cofibrations_le_evaluationProperty
#check @HomotopicalAlgebra.EnrichedProjective.trivialCofibrations_le_evaluationProperty

end EnrichedGeneratedLevelTests
