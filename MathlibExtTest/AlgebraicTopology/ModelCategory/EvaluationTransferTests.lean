/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.EvaluationTransfer

set_option autoImplicit false
noncomputable section
universe w s vC vD uC uD

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.EvaluationTransfer

namespace MathlibExtTest.EvaluationTransfer

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D] {S : Type s}
  (L : S → C ⥤ D) (R : S → D ⥤ C) (adj : ∀ a, L a ⊣ R a)
  (I J W : MorphismProperty C)

-- The arbitrary original evaluations, not a replacement carrier or point predicate.
example {X Y : D} (f : X ⟶ Y) :
    evaluationProperty R W f ↔ ∀ a, W ((R a).map f) :=
  evaluationProperty_iff R W f

example {X Y : D} (f : X ⟶ Y) :
    (MorphismProperty.adjointFamilyGenerators L I).rlp f ↔
      ∀ a, I.rlp ((R a).map f) :=
  MorphismProperty.adjointFamilyGenerators_rlp_iff L R adj I f

variable [W.HasTwoOutOfThreeProperty]
  [(MorphismProperty.adjointFamilyGenerators L I).HasSmallObjectArgument.{w}]
  [(MorphismProperty.adjointFamilyGenerators L J).HasSmallObjectArgument.{w}]
  [HasFiniteLimits D] [HasFiniteColimits D]
  (hBase : I.rlp = J.rlp ⊓ W)
  (hAcyclicity : (MorphismProperty.adjointFamilyGenerators L J).rlp.llp ≤
    evaluationProperty R W)

-- A target model is constructed without any ambient target model instance.
example : ModelCategory D :=
  evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity

section ReturnedDictionary

example {X Y : D} (f : X ⟶ Y) :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    weakEquivalences D f ↔ ∀ a, W ((R a).map f) := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  rw [evaluationProjectiveWeakEquivalences_eq L R adj I J W hBase hAcyclicity]
  exact evaluationProperty_iff R W f

example {X Y : D} (f : X ⟶ Y) :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    fibrations D f ↔ ∀ a, J.rlp ((R a).map f) := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  rw [evaluationProjectiveFibrations_eq L R adj I J W hBase hAcyclicity]
  exact evaluationProperty_iff R J.rlp f

example {X Y : D} (f : X ⟶ Y) :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    trivialFibrations D f ↔ ∀ a, I.rlp ((R a).map f) := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  rw [evaluationProjectiveTrivialFibrations_eq L R adj I J W hBase hAcyclicity]
  exact evaluationProperty_iff R I.rlp f

example :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    cofibrations D = (MorphismProperty.adjointFamilyGenerators L I).rlp.llp := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  exact evaluationProjectiveCofibrations_eq L R adj I J W hBase hAcyclicity

-- Both original small-object arguments give genuine functorial factorization classes.

example :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    HasFunctorialFactorization (cofibrations D) (trivialFibrations D) := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  exact evaluationProjectiveCofibrantFactorization L R adj I J W hBase hAcyclicity

example :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    HasFunctorialFactorization (trivialCofibrations D) (fibrations D) := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  exact evaluationProjectiveFibrantFactorization L R adj I J W hBase hAcyclicity

-- Actual factor maps retain their endpoints and factor the caller's original arrow.

example {X Y : D} (f : X ⟶ Y) :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    let d := factorizationData (cofibrations D) (trivialFibrations D) f
    cofibrations D d.i ∧ trivialFibrations D d.p ∧ d.i ≫ d.p = f := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  let d := factorizationData (cofibrations D) (trivialFibrations D) f
  exact ⟨d.hi, d.hp, d.fac⟩

example {X Y : D} (f : X ⟶ Y) :
    letI : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
    let d := factorizationData (trivialCofibrations D) (fibrations D) f
    trivialCofibrations D d.i ∧ fibrations D d.p ∧ d.i ≫ d.p = f := by
  let _ : ModelCategory D := evaluationProjectiveModelCategory L R adj I J W hBase hAcyclicity
  let d := factorizationData (trivialCofibrations D) (fibrations D) f
  exact ⟨d.hi, d.hp, d.fac⟩

end ReturnedDictionary

#check @evaluationDiagram
#check @evaluationProperty
#check @evaluationProperty_iff
#check @evaluationProperty_inf
#check @evaluationProperty_hasTwoOutOfThree
#check @evaluatedGenerators_rlp_eq
#check @evaluatedGenerators_trivialFibrations_eq
#check @evaluationRecognitionData
#check @evaluationProjectiveModelCategory
#check @evaluationProjectiveWeakEquivalences_eq
#check @evaluationProjectiveCofibrations_eq
#check @evaluationProjectiveFibrations_eq
#check @evaluationProjectiveTrivialFibrations_eq
#check @evaluationProjectiveTrivialCofibrations_eq
#check @evaluationProjectiveCofibrantFactorization
#check @evaluationProjectiveFibrantFactorization
#print axioms evaluationProjectiveModelCategory
#print axioms evaluationProjectiveCofibrantFactorization
#print axioms evaluationProjectiveFibrantFactorization

end MathlibExtTest.EvaluationTransfer
