/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective

set_option autoImplicit false
noncomputable section
universe w uA uV vV
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite
open MonoidalCategory HomotopicalAlgebra

namespace HomotopicalAlgebra.EnrichedProjectiveTests
open EnrichedProjective
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]

section GenericCardinal
variable (P Q : MorphismProperty V) [P.IsSmall.{w}] [Q.RespectsIso]
  [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
  [Q.IsStableUnderTransfiniteComposition.{w}]
  (hTensor : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y), P f → Q (f ▷ (a ⟶[V] b)))
  (hSource : ∀ {X Y : V} (f : X ⟶ Y), P f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), Q (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))

example (a : A) : generators (A := A) P ≤ Q.inverseImage (EnrichedFunctorCat.evaluation a) :=
  generators_evaluation_le P Q hTensor a

example : (generators (A := A) P).IsCardinalForSmallObjectArgument κ :=
  generators_isCardinalForSmallObjectArgument P Q hTensor hSource
example : (generators (A := A) P).IsSmall.{w} :=
  (generators_isCardinalForSmallObjectArgument P Q hTensor hSource).isSmall
example : LocallySmall.{w} (EnrichedFunctorCat V A) :=
  (generators_isCardinalForSmallObjectArgument P Q hTensor hSource).locallySmall
example : HasPushouts (EnrichedFunctorCat V A) :=
  (generators_isCardinalForSmallObjectArgument P Q hTensor hSource).hasPushouts
example : HasCoproducts.{w} (EnrichedFunctorCat V A) :=
  (generators_isCardinalForSmallObjectArgument P Q hTensor hSource).hasCoproducts
example : HasIterationOfShape κ.ord.ToType (EnrichedFunctorCat V A) :=
  (generators_isCardinalForSmallObjectArgument P Q hTensor hSource).hasIterationOfShape

example {X Y B C : EnrichedFunctorCat V A} (i : X ⟶ Y)
    (hi : generators (A := A) P i) (f : B ⟶ C)
    (c : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => (generators (A := A) P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (op X)) :=
  (generators_isCardinalForSmallObjectArgument P Q hTensor hSource).preservesColimit i hi f c

example : (generators (A := A) P).HasSmallObjectArgument.{w} :=
  generators_hasSmallObjectArgument P Q hTensor hSource

end GenericCardinal

variable [ModelCategory V]
  (d : CofibrantGenerationData V κ)
  (hI : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.I f → cofibrations V (f ▷ (a ⟶[V] b)))
  (hJ : ∀ a b : A, ∀ {X Y : V} (f : X ⟶ Y),
    d.J f → trivialCofibrations V (f ▷ (a ⟶[V] b)))
  (hSourceI : ∀ {X Y : V} (f : X ⟶ Y), d.I f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), cofibrations V (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))
  (hSourceJ : ∀ {X Y : V} (f : X ⟶ Y), d.J f →
    ∀ (F : κ.ord.ToType ⥤ V) [F.IsWellOrderContinuous],
      (∀ ⦃a b⦄ (φ : a ⟶ b), trivialCofibrations V (F.map φ)) →
      PreservesColimit F (coyoneda.obj (op X)))


example (a : A) {X Y : V} (f : X ⟶ Y) (hf : d.I f) :
    generators (A := A) d.I ((EnrichedFunctorCat.Free.functor a).map f) :=
  map_mem_adjointFamilyGenerators _ d.I a f hf

example : ModelCategory (EnrichedFunctorCat V A) :=
  modelCategory d hI hJ hSourceI hSourceJ

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategory d hI hJ hSourceI hSourceJ
    weakEquivalences (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (weakEquivalences V) :=
  weakEquivalences_eq d hI hJ hSourceI hSourceJ

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategory d hI hJ hSourceI hSourceJ
    cofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.I).rlp.llp :=
  cofibrations_eq d hI hJ hSourceI hSourceJ

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategory d hI hJ hSourceI hSourceJ
    fibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (fibrations V) :=
  fibrations_eq d hI hJ hSourceI hSourceJ

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategory d hI hJ hSourceI hSourceJ
    trivialFibrations (EnrichedFunctorCat V A) =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) (trivialFibrations V) :=
  trivialFibrations_eq d hI hJ hSourceI hSourceJ

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategory d hI hJ hSourceI hSourceJ
    trivialCofibrations (EnrichedFunctorCat V A) = (generators (A := A) d.J).rlp.llp :=
  trivialCofibrations_eq d hI hJ hSourceI hSourceJ

example :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategory d hI hJ hSourceI hSourceJ
    HasFunctorialFactorization (cofibrations (EnrichedFunctorCat V A))
        (trivialFibrations (EnrichedFunctorCat V A)) ∧
      HasFunctorialFactorization (trivialCofibrations (EnrichedFunctorCat V A))
        (fibrations (EnrichedFunctorCat V A)) :=
  functorialFactorizations d hI hJ hSourceI hSourceJ

example (a : A) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      modelCategory d hI hJ hSourceI hSourceJ
    (EnrichedFunctorCat.Free.adjunction (V := V) a).IsQuillenAdjunction :=
  freeAtEvaluation_isQuillenAdjunction d hI hJ hSourceI hSourceJ a

#check @EnrichedProjective.generators
#check @EnrichedProjective.generators_evaluation_le
#check @EnrichedProjective.generators_isCardinalForSmallObjectArgument
#check @EnrichedProjective.generators_hasSmallObjectArgument
#check @EnrichedProjective.modelCategory
#check @EnrichedProjective.weakEquivalences_eq
#check @EnrichedProjective.cofibrations_eq
#check @EnrichedProjective.fibrations_eq
#check @EnrichedProjective.trivialFibrations_eq
#check @EnrichedProjective.trivialCofibrations_eq
#check @EnrichedProjective.functorialFactorizations
#check @EnrichedProjective.freeAtEvaluation_isQuillenAdjunction
#print axioms EnrichedProjective.generators_evaluation_le
#print axioms EnrichedProjective.generators_isCardinalForSmallObjectArgument
#print axioms EnrichedProjective.generators_hasSmallObjectArgument
#print axioms EnrichedProjective.modelCategory
#print axioms EnrichedProjective.weakEquivalences_eq
#print axioms EnrichedProjective.cofibrations_eq
#print axioms EnrichedProjective.fibrations_eq
#print axioms EnrichedProjective.trivialFibrations_eq
#print axioms EnrichedProjective.trivialCofibrations_eq
#print axioms EnrichedProjective.functorialFactorizations
#print axioms EnrichedProjective.freeAtEvaluation_isQuillenAdjunction
end HomotopicalAlgebra.EnrichedProjectiveTests
