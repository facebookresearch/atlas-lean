/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalObjectwiseCofibrationClosure
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.BoundedRightAcyclicity
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.StrictSolutions
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalObjectwiseCofibrationGeneration
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Smith construction on the unchanged original functor category

Choose the actual compact profile and diagram generators from the original
coefficient generation and essential-index data. Their native small-object
argument gives the bounded left class. Its trivial intersection is closed by
the original coefficient trivial cofibrations, and the actual weak-arrow
solution families supply Smith's generatorwise solutions. Thus both generating
families and a model dictionary are outputs, not caller-provided outcomes.

Identification of the bounded left class with every objectwise cofibration
uses the separate full original filtration and generation construction.
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.FunctorInjective

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
  [IsCardinalLocallyPresentable C κLP] (s : Functor.EssentialIndexData.{w} D C)

section FixedOriginalProfile

variable (b : BoundedConstruction d κLP s)

/-- The same bounded left/weak intersection consists of original objectwise
trivial cofibrations, without an assumed generation equality. -/
theorem boundedTrivialCofibrations_le_objectwise :
    b.family.generators.rlp.llp ⊓ (weakEquivalences C).functorCategory D ≤
      (trivialCofibrations C).functorCategory D := by
  intro F G f hf x
  exact ⟨originalGenerators_rlp_llp_le_objectwiseCofibrations d κLP s b f hf.1 x,
    hf.2 x⟩

/-- Actual pushouts preserve the bounded left/weak intersection, using the
coefficient model's derived trivial-cofibration closure. -/
theorem boundedTrivialCofibrations_cobase :
    (b.family.generators.rlp.llp ⊓
      (weakEquivalences C).functorCategory D).IsStableUnderCobaseChange := by
  let T := (trivialCofibrations C).functorCategory D
  obtain ⟨_, hCobase, _, _⟩ := objectwiseTrivialCofibrations_stable.{w} (D := D) (C := C)
  let _ : T.IsStableUnderCobaseChange := hCobase
  refine { of_isPushout := fun sq hf => ?_ }
  have hT := T.of_isPushout sq (boundedTrivialCofibrations_le_objectwise d κLP s b _ hf)
  exact ⟨b.family.generators.rlp.llp.of_isPushout sq hf.1, fun x => (hT x).2⟩

/-- Every original continuous whole-arrow composite stays in the same bounded
left/weak intersection; no final weak closure is supplied. -/
theorem boundedTrivialCofibrations_transfinite :
    IsStableUnderTransfiniteComposition.{w}
      (b.family.generators.rlp.llp ⊓ (weakEquivalences C).functorCategory D) := by
  let T := (trivialCofibrations C).functorCategory D
  obtain ⟨_, _, hTransfinite, _⟩ :=
    objectwiseTrivialCofibrations_stable.{w} (D := D) (C := C)
  let _ : IsStableUnderTransfiniteComposition.{w} T := hTransfinite
  refine { isStableUnderTransfiniteCompositionOfShape := fun J _ _ _ _ => ?_ }
  refine { le := ?_ }
  rintro F G f ⟨c⟩
  have hLeft : b.family.generators.rlp.llp f :=
    b.family.generators.rlp.llp.transfiniteCompositionsOfShape_le J f
      (c.ofLE inf_le_left).mem
  have hT : T f := T.transfiniteCompositionsOfShape_le J f
    (c.ofLE (boundedTrivialCofibrations_le_objectwise d κLP s b)).mem
  exact ⟨hLeft, fun x => (hT x).2⟩

/-- The actual original profile supplies all Smith hypotheses. Each solution
is selected from the original accessible weak-arrow inclusion. -/
theorem boundedSmithInput : SmithRecognitionInput.{w}
    b.family.generators ((weakEquivalences C).functorCategory D) := by
  exact
    { weak_two_out_of_three := inferInstance
      weak_retracts := inferInstance
      trivial_fibrations_weak := boundedRight_le_objectwise_weak d κLP s b
      trivial_cofibrations_cobase := boundedTrivialCofibrations_cobase d κLP s b
      trivial_cofibrations_transfinite := boundedTrivialCofibrations_transfinite d κLP s b
      solution_set := fun {F G} i _ => weakArrow_solutionSetCondition d κLP s (Arrow.mk i) }

end FixedOriginalProfile

/-- Construct Smith input from the original base model and index, choosing the
compact rank and representative family internally once. -/
theorem originalSmithInput : SmithRecognitionInput.{w}
    (boundedConstruction d κLP s).family.generators
      ((weakEquivalences C).functorCategory D) :=
  boundedSmithInput d κLP s (boundedConstruction d κLP s)

/-- The real Smith construction produces its second family and both weak
factorization systems on the unchanged original functor category. -/
def originalSmithData : SmithModelStructureData.{w}
    (boundedConstruction d κLP s).family.generators
      ((weakEquivalences C).functorCategory D) := by
  let b := boundedConstruction d κLP s
  let _ : IsCardinalLocallyPresentable (D ⥤ C) κLP := s.isCardinalLocallyPresentable κLP
  let _ : IsLocallyPresentable.{w} (D ⥤ C) := ⟨κLP, inferInstance, inferInstance⟩
  let _ : b.family.generators.HasSmallObjectArgument.{w} := b.hasSmallObjectArgument
  exact Classical.choice (smithRecognition b.family.generators
    ((weakEquivalences C).functorCategory D) (originalSmithInput d κLP s))

/-- Install the actual Smith dictionary on the original D-to-C carrier. Its
cofibrations are the original bounded generated left class. -/
@[instance_reducible]
def originalSmithModelCategory : ModelCategory (D ⥤ C) := by
  let b := boundedConstruction d κLP s
  let M := originalSmithData d κLP s
  let _ : IsCardinalLocallyPresentable (D ⥤ C) κLP := s.isCardinalLocallyPresentable κLP
  letI : CategoryWithCofibrations (D ⥤ C) := ⟨b.family.generators.rlp.llp⟩
  letI : CategoryWithFibrations (D ⥤ C) := ⟨M.J.rlp⟩
  letI : CategoryWithWeakEquivalences (D ⥤ C) := ⟨(weakEquivalences C).functorCategory D⟩
  exact M.modelCategory inferInstance rfl rfl rfl

/-- The actual constructed dictionary has precisely the original objectwise
weak equivalences. -/
theorem originalSmithModel_weakEquivalences :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  rfl

/-- The actual cofibration class retains the full internally selected family. -/
theorem originalSmithModel_cofibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    cofibrations (D ⥤ C) = (boundedConstruction d κLP s).family.generators.rlp.llp := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  rfl

/-- The actual fibrations are the right class of this same bounded left/weak
intersection, derived by Smith recognition. -/
theorem originalSmithModel_fibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    fibrations (D ⥤ C) =
      ((boundedConstruction d κLP s).family.generators.rlp.llp ⊓
        (weakEquivalences C).functorCategory D).rlp := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithData d κLP s).fibrations_eq

/-- Both model predicates in the trivial-cofibration class remain the original
bounded left and objectwise weak predicates. -/
theorem originalSmithModel_trivialCofibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    trivialCofibrations (D ⥤ C) =
      (boundedConstruction d κLP s).family.generators.rlp.llp ⊓
        (weakEquivalences C).functorCategory D := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  rfl

/-- The actual trivial fibrations retain the original entire bounded-family
right lifting class, without a target-fibration premise. -/
theorem originalSmithModel_trivialFibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    trivialFibrations (D ⥤ C) = (boundedConstruction d κLP s).family.generators.rlp := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithData d κLP s).trivialFibrations_eq

/-- The first complete functorial factor retains the original selected compact
family and its actual fixed-rank small-object construction. -/
def originalSmithCofibrantFactorizationData :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    FunctorialFactorizationData (cofibrations (D ⥤ C)) (trivialFibrations (D ⥤ C)) := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (boundedConstruction d κLP s).factorization.ofLE
    (by rw [originalSmithModel_cofibrations d κLP s])
    (by rw [originalSmithModel_trivialFibrations d κLP s])

/-- The second factor source uses the actual produced Smith J-family and its
proved native small-object argument, never a supplied target factor. -/
def originalSmithSecondFactorizationSource :
    FunctorialFactorizationData (originalSmithData d κLP s).J.rlp.llp
      (originalSmithData d κLP s).J.rlp := by
  let M := originalSmithData d κLP s
  let _ : M.J.HasSmallObjectArgument.{w} := M.J_smallObject
  exact functorialFactorizationData M.J.rlp.llp M.J.rlp

/-- Reclassify that same entire second factor record in the constructed model.
Only membership proofs change; its middle functor and transformations remain. -/
def originalSmithFibrantFactorizationData :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    FunctorialFactorizationData (trivialCofibrations (D ⥤ C)) (fibrations (D ⥤ C)) := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  let M := originalSmithData d κLP s
  exact (originalSmithSecondFactorizationSource d κLP s).ofLE
    (by rw [originalSmithModel_trivialCofibrations d κLP s, ← M.trivialCofibrations_eq])
    (by change M.J.rlp ≤ M.J.rlp; rfl)

/-- The first original whole middle functor is unchanged by model reclassification. -/
theorem originalSmithCofibrantFactorizationData_Z :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithCofibrantFactorizationData d κLP s).Z =
      (boundedConstruction d κLP s).factorization.Z := rfl

/-- Every first original source transformation remains the actual native one. -/
theorem originalSmithCofibrantFactorizationData_i :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithCofibrantFactorizationData d κLP s).i =
      (boundedConstruction d κLP s).factorization.i := rfl

/-- Every first original target transformation remains the actual native one. -/
theorem originalSmithCofibrantFactorizationData_p :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithCofibrantFactorizationData d κLP s).p =
      (boundedConstruction d κLP s).factorization.p := rfl

/-- The second original whole middle functor is retained, including all Arrow maps. -/
theorem originalSmithFibrantFactorizationData_Z :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithFibrantFactorizationData d κLP s).Z =
      (originalSmithSecondFactorizationSource d κLP s).Z := rfl

/-- The second original source transformation is unchanged. -/
theorem originalSmithFibrantFactorizationData_i :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithFibrantFactorizationData d κLP s).i =
      (originalSmithSecondFactorizationSource d κLP s).i := rfl

/-- The second original target transformation is unchanged. -/
theorem originalSmithFibrantFactorizationData_p :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithFibrantFactorizationData d κLP s).p =
      (originalSmithSecondFactorizationSource d κLP s).p := rfl

/-- The first original whole natural arrow satisfies its strict factor equation. -/
theorem originalSmithCofibrantFactorizationData_fac (f : Arrow (D ⥤ C)) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithCofibrantFactorizationData d κLP s).i.app f ≫
      (originalSmithCofibrantFactorizationData d κLP s).p.app f = f.hom := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithCofibrantFactorizationData d κLP s).fac_app

/-- The second original whole natural arrow satisfies its strict factor equation. -/
theorem originalSmithFibrantFactorizationData_fac (f : Arrow (D ⥤ C)) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithFibrantFactorizationData d κLP s).i.app f ≫
      (originalSmithFibrantFactorizationData d κLP s).p.app f = f.hom := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithFibrantFactorizationData d κLP s).fac_app

/-- Every original square preserves the whole first factor's left leg. -/
theorem originalSmithCofibrantFactorizationData_i_naturality
    {f g : Arrow (D ⥤ C)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    φ.left ≫ (originalSmithCofibrantFactorizationData d κLP s).i.app g =
      (originalSmithCofibrantFactorizationData d κLP s).i.app f ≫
        (originalSmithCofibrantFactorizationData d κLP s).Z.map φ := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithCofibrantFactorizationData d κLP s).i.naturality φ

/-- Every original square preserves the whole first factor's right leg. -/
theorem originalSmithCofibrantFactorizationData_p_naturality
    {f g : Arrow (D ⥤ C)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithCofibrantFactorizationData d κLP s).Z.map φ ≫
      (originalSmithCofibrantFactorizationData d κLP s).p.app g =
      (originalSmithCofibrantFactorizationData d κLP s).p.app f ≫ φ.right := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithCofibrantFactorizationData d κLP s).p.naturality φ

/-- Every original square preserves the whole second factor's left leg. -/
theorem originalSmithFibrantFactorizationData_i_naturality
    {f g : Arrow (D ⥤ C)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    φ.left ≫ (originalSmithFibrantFactorizationData d κLP s).i.app g =
      (originalSmithFibrantFactorizationData d κLP s).i.app f ≫
        (originalSmithFibrantFactorizationData d κLP s).Z.map φ := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithFibrantFactorizationData d κLP s).i.naturality φ

/-- Every original square preserves the whole second factor's right leg. -/
theorem originalSmithFibrantFactorizationData_p_naturality
    {f g : Arrow (D ⥤ C)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    (originalSmithFibrantFactorizationData d κLP s).Z.map φ ≫
      (originalSmithFibrantFactorizationData d κLP s).p.app g =
      (originalSmithFibrantFactorizationData d κLP s).p.app f ≫ φ.right := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithFibrantFactorizationData d κLP s).p.naturality φ

/-- Actual original generation identifies the constructed cofibration class
with every objectwise coefficient cofibration. -/
theorem originalInjectiveModel_cofibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    cofibrations (D ⥤ C) = (cofibrations C).functorCategory D := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithModel_cofibrations d κLP s).trans
    (originalGenerators_rlp_llp_eq_objectwiseCofibrations d κLP s
      (boundedConstruction d κLP s))

/-- The constructed model's complete trivial cofibrations are exactly the
original objectwise coefficient trivial cofibrations. -/
theorem originalInjectiveModel_trivialCofibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    trivialCofibrations (D ⥤ C) = (trivialCofibrations C).functorCategory D := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  rw [originalSmithModel_trivialCofibrations d κLP s,
    originalGenerators_rlp_llp_eq_objectwiseCofibrations d κLP s
      (boundedConstruction d κLP s)]
  ext F G f
  constructor
  · rintro ⟨hc, hw⟩ x
    exact ⟨hc x, hw x⟩
  · intro h
    exact ⟨fun x => (h x).1, fun x => (h x).2⟩

/-- Actual full generation identifies the entire trivial-fibration lifting
class against all original objectwise cofibrations. -/
theorem originalInjectiveModel_trivialFibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    trivialFibrations (D ⥤ C) = ((cofibrations C).functorCategory D).rlp := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact (originalSmithModel_trivialFibrations d κLP s).trans
    (originalGenerators_rlp_eq_objectwiseRlp d κLP s (boundedConstruction d κLP s))

/-- The constructed fibrations are the complete right lifting class against
all original objectwise trivial cofibrations. -/
theorem originalInjectiveModel_fibrations :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    fibrations (D ⥤ C) = ((trivialCofibrations C).functorCategory D).rlp := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  rw [originalSmithModel_fibrations d κLP s,
    ← originalSmithModel_trivialCofibrations d κLP s,
    originalInjectiveModel_trivialCofibrations d κLP s]

/-- All five class laws concern the same original D-to-C arrows and the
actual constructed model; no class-identification premise is supplied. -/
theorem originalInjectiveModel_fiveClasses :
    letI : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
    weakEquivalences (D ⥤ C) = (weakEquivalences C).functorCategory D ∧
      cofibrations (D ⥤ C) = (cofibrations C).functorCategory D ∧
      trivialCofibrations (D ⥤ C) = (trivialCofibrations C).functorCategory D ∧
      fibrations (D ⥤ C) = ((trivialCofibrations C).functorCategory D).rlp ∧
      trivialFibrations (D ⥤ C) = ((cofibrations C).functorCategory D).rlp := by
  let _ : ModelCategory (D ⥤ C) := originalSmithModelCategory d κLP s
  exact ⟨originalSmithModel_weakEquivalences d κLP s,
    originalInjectiveModel_cofibrations d κLP s,
    originalInjectiveModel_trivialCofibrations d κLP s,
    originalInjectiveModel_fibrations d κLP s,
    originalInjectiveModel_trivialFibrations d κLP s⟩

end HomotopicalAlgebra.FunctorInjective
