/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective

/-!
# The original projective model's generation data

The model is the existing ordinary construction. All original index objects
label the free images, and both eligibility dictionaries retain the supplied
base cardinal. No target model or acyclicity data is an input.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.FunctorProjective

variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]
  [ModelCategory M] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocallySmall.{w} D]

/-- The actual Hom-indexed coproducts required by the original evaluation left adjoints. -/
theorem homCoproducts (d : CofibrantGenerationData M κ) :
    ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := by
  let _ : HasCoproducts.{w} M := d.I_smallObject.hasCoproducts
  exact fun x y => hasCoproductsOfShape_of_small M (x ⟶ y)

/-- The free diagram uses every original index object and its genuine Hom coproducts. -/
def freeFunctor (d : CofibrantGenerationData M κ) (x : D) : M ⥤ D ⥤ M := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact evaluationLeftAdjoint M x

/-- The actual free/evaluation adjunction keeps its original evaluation getter. -/
def freeEvaluationAdjunction (d : CofibrantGenerationData M κ) (x : D) :
    freeFunctor d x ⊣ (evaluation D M).obj x := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact evaluationAdjunctionRight M x

/-- The literal free images of a base class, correlated with all original index labels. -/
def freeGenerators (d : CofibrantGenerationData M κ) (P : MorphismProperty M) :
    MorphismProperty (D ⥤ M) :=
  adjointFamilyGenerators (freeFunctor d) P

/-- Membership retains equality of the entire original free-image arrow. -/
theorem freeGenerators_iff (d : CofibrantGenerationData M κ) (P : MorphismProperty M)
    {X Y : D ⥤ M} (f : X ⟶ Y) :
    freeGenerators d P f ↔
      ∃ q : D × P.toSet, Arrow.mk f = Arrow.mk ((freeFunctor d q.1).map q.2.1.hom) :=
  adjointFamilyGenerators_iff (freeFunctor d) P f

/-- Every original base generator has its actual free image in the literal diagram family. -/
theorem freeGenerator_mem (d : CofibrantGenerationData M κ) (P : MorphismProperty M)
    (x : D) {A B : M} (f : A ⟶ B) (hf : P f) :
    freeGenerators d P ((freeFunctor d x).map f) :=
  map_mem_adjointFamilyGenerators (freeFunctor d) P x f hf

variable [Small.{w} D]

/-- Both fixed-cardinal free families retain all six actual small-object fields. -/
theorem freeGenerators_eligible (d : CofibrantGenerationData M κ) (P : MorphismProperty M)
    (hP : P.IsCardinalForSmallObjectArgument κ) :
    (freeGenerators (D := D) d P).IsCardinalForSmallObjectArgument κ := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  exact isCardinalForSmallObjectArgument_freeDiagrams (J := D) P κ hP

/-- The original I family is eligible at the input cardinal, without a second choice. -/
theorem freeI_eligible (d : CofibrantGenerationData M κ) :
    (freeGenerators (D := D) d d.I).IsCardinalForSmallObjectArgument κ :=
  freeGenerators_eligible d d.I d.I_smallObject

/-- The original J family is eligible at that same input cardinal. -/
theorem freeJ_eligible (d : CofibrantGenerationData M κ) :
    (freeGenerators (D := D) d d.J).IsCardinalForSmallObjectArgument κ :=
  freeGenerators_eligible d d.J d.J_smallObject

omit [Small.{w} D] in
/-- Right lifting against the genuine free family is evaluated on every original object. -/
theorem freeGenerators_rlp (d : CofibrantGenerationData M κ) (P : MorphismProperty M) :
    (freeGenerators (D := D) d P).rlp = P.rlp.functorCategory D := by
  ext X Y f
  exact adjointFamilyGenerators_rlp_iff (freeFunctor d)
    (fun x : D => (evaluation D M).obj x) (freeEvaluationAdjunction d) P f

/-- Every original I-generator is a base cofibration. -/
theorem baseI_le_cofibrations (d : CofibrantGenerationData M κ) : d.I ≤ cofibrations M := by
  have h := d.I.le_llp_rlp
  rw [d.I_rlp, trivialFibrations_llp] at h
  exact h

/-- Every original J-generator is a base trivial cofibration. -/
theorem baseJ_le_trivialCofibrations (d : CofibrantGenerationData M κ) :
    d.J ≤ trivialCofibrations M := by
  have h := d.J.le_llp_rlp
  rw [d.J_rlp, fibrations_llp] at h
  exact h

/-- The actual free-I left class consists of objectwise base cofibrations. -/
theorem freeI_left_le_objectwise (d : CofibrantGenerationData M κ) :
    (freeGenerators (D := D) d d.I).rlp.llp ≤ (cofibrations M).functorCategory D := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  let _ : (cofibrations M).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (cofibrations M) (trivialFibrations M)
      (trivialFibrations_llp M)
  let _ : (cofibrations M).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← trivialFibrations_llp M]
    infer_instance
  exact freeDiagrams_leftClass_le_functorCategory (J := D) d.I (cofibrations M)
    (cofibrations M) κ d.I_smallObject (baseI_le_cofibrations d) le_rfl

/-- The actual free-J left class consists of objectwise base trivial cofibrations. -/
theorem freeJ_left_le_objectwise (d : CofibrantGenerationData M κ) :
    (freeGenerators (D := D) d d.J).rlp.llp ≤ (trivialCofibrations M).functorCategory D := by
  let _ : ∀ x y : D, HasCoproductsOfShape (x ⟶ y) M := homCoproducts d
  let _ : (trivialCofibrations M).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (trivialCofibrations M) (fibrations M) (fibrations_llp M)
  let _ : (trivialCofibrations M).IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType := by
    rw [← fibrations_llp M]
    infer_instance
  exact freeDiagrams_leftClass_le_functorCategory (J := D) d.J (trivialCofibrations M)
    (trivialCofibrations M) κ d.J_smallObject (baseJ_le_trivialCofibrations d) le_rfl

/-- The original evaluated J-cell argument proves acyclicity internally. -/
theorem freeJ_left_le_weakEquivalences (d : CofibrantGenerationData M κ) :
    (freeGenerators (D := D) d d.J).rlp.llp ≤ (weakEquivalences M).functorCategory D := by
  intro X Y f hf x
  exact ((freeJ_left_le_objectwise d) f hf x).2

section ReturnedModel

variable (d : CofibrantGenerationData M κ)

/-- The same original projective cofibrations are exactly the objectwise-TF left lifting class. -/
theorem cofibrations_eq_objectwise_llp :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [← trivialFibrations_eq d]
  exact (trivialFibrations_llp (D ⥤ M)).symm

/-- The same original projective trivial cofibrations are the objectwise-Fib left lifting class. -/
theorem trivialCofibrations_eq_objectwise_llp :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [← fibrations_eq d]
  exact (fibrations_llp (D ⥤ M)).symm

/-- The actual free-I right class is the returned original projective trivial-fibration class. -/
theorem freeI_rlp_eq :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (freeGenerators d d.I).rlp = trivialFibrations (D ⥤ M) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [freeGenerators_rlp, d.I_rlp, trivialFibrations_eq d]

/-- The actual free-J right class is the returned original projective fibration class. -/
theorem freeJ_rlp_eq :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (freeGenerators d d.J).rlp = fibrations (D ⥤ M) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [freeGenerators_rlp, d.J_rlp, fibrations_eq d]

/-- The free-I generated left class is exactly the original projective cofibration class. -/
theorem freeI_left_eq :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (freeGenerators d d.I).rlp.llp = cofibrations (D ⥤ M) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [freeI_rlp_eq d, trivialFibrations_llp]

/-- The free-J generated left class is exactly the original projective trivial-cofibration class. -/
theorem freeJ_left_eq :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (freeGenerators d d.J).rlp.llp = trivialCofibrations (D ⥤ M) := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [freeJ_rlp_eq d, fibrations_llp]

/-- All five prescribed classes are identified on the same original functor category. -/
theorem five_classes :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
      fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
      trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
      cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  ⟨weakEquivalences_eq d, fibrations_eq d, trivialFibrations_eq d,
    cofibrations_eq_objectwise_llp d, trivialCofibrations_eq_objectwise_llp d⟩

/-- Actual projective cofibrations are objectwise cofibrations, for every original arrow. -/
theorem cofibrations_le_objectwise :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    cofibrations (D ⥤ M) ≤ (cofibrations M).functorCategory D := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [← freeI_left_eq d]
  exact freeI_left_le_objectwise d

/-- Actual projective trivial cofibrations are objectwise trivial cofibrations. -/
theorem trivialCofibrations_le_objectwise :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    trivialCofibrations (D ⥤ M) ≤ (trivialCofibrations M).functorCategory D := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  rw [← freeJ_left_eq d]
  exact freeJ_left_le_objectwise d

/-- Public cofibrant-generation data for the unchanged projective model at the input cardinal. -/
def generationData :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    CofibrantGenerationData (D ⥤ M) κ := by
  let _ : ModelCategory (D ⥤ M) := modelCategory (J := D) d
  exact
    { I := freeGenerators d d.I
      J := freeGenerators d d.J
      I_smallObject := freeI_eligible d
      J_smallObject := freeJ_eligible d
      I_rlp := freeI_rlp_eq d
      J_rlp := freeJ_rlp_eq d }

/-- The returned I family is the actual free image of the original base family. -/
theorem generationData_I :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (generationData (D := D) d).I = freeGenerators d d.I := rfl

/-- The returned J family is the actual free image of the original base family. -/
theorem generationData_J :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (generationData (D := D) d).J = freeGenerators d d.J := rfl

/-- The whole returned I eligibility dictionary retains the original free-diagram proof. -/
theorem generationData_I_smallObject :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (generationData (D := D) d).I_smallObject = freeI_eligible d := rfl

/-- The whole returned J eligibility dictionary retains the original free-diagram proof. -/
theorem generationData_J_smallObject :
    letI : ModelCategory (D ⥤ M) := modelCategory (J := D) d
    (generationData (D := D) d).J_smallObject = freeJ_eligible d := rfl

end ReturnedModel

end HomotopicalAlgebra.FunctorProjective
