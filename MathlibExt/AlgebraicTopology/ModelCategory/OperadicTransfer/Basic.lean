/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import MathlibExt.AlgebraicTopology.ModelCategory.SemiModel.ColorSource
public import MathlibExt.CategoryTheory.Operad.Tensor.FreeAlgebra

/-!
# Recognition on the original tensor-operadic algebra category

The source category is the actual color family category, and the generating
maps are the literal free images of the original supported generators.
The constructor below is the fixed-cardinal recognition step. Its acyclicity
argument is discharged by the separate operadic attachment and source-branch
proofs; it is not an input to the eventual full source theorem.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject
open CategoryTheory.Operad CategoryTheory.Operad.Tensor

namespace HomotopicalAlgebra.OperadicTransfer

variable (S : SourceContext.{uW, v, u, us})

/-- Use the original finite tensor operations from the supplied source context. -/
local instance basicOriginalFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance basicOriginalTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance basicOriginalProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

/-- The literal free images of the caller's original color-supported family. -/
def freeGenerators (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C) :
    MorphismProperty (Algebra O) :=
  (SemiModel.ColorSource.colorGenerators S.C S.W P).strictMap (freeAlgebraFunctor O)

/-- The original algebra adjunction retains the full source right lifting class. -/
theorem freeGenerators_rlp (O : ColoredOperadObj S.W S.C) (P : MorphismProperty S.C) :
    (freeGenerators S O P).rlp =
      (SemiModel.ColorSource.pointwiseProperty S.C S.W P.rlp).inverseImage
        (Algebra.forget O) := by
  rw [freeGenerators, strictMap_rlp_eq_inverseImage_rlp
    _ (freeAlgebraFunctor O) (Algebra.forget O) (S.operadicAdjunction O),
    SemiModel.ColorSource.colorGenerators_rlp_eq]

/-- The actual original weak class is evaluated at every original color. -/
def weakClass (O : ColoredOperadObj S.W S.C) : MorphismProperty (Algebra O) :=
  (SemiModel.ColorSource.pointwiseProperty S.C S.W (weakEquivalences S.C)).inverseImage
    (Algebra.forget O)

/-- The actual underlying fibrations are evaluated at those same colors. -/
def fibrationClass (O : ColoredOperadObj S.W S.C) : MorphismProperty (Algebra O) :=
  (SemiModel.ColorSource.pointwiseProperty S.C S.W (fibrations S.C)).inverseImage
    (Algebra.forget O)

/-- The underlying trivial-fibration class keeps both original conditions. -/
def trivialFibrationClass (O : ColoredOperadObj S.W S.C) : MorphismProperty (Algebra O) :=
  (SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialFibrations S.C)).inverseImage
    (Algebra.forget O)

/-- Cofibrations are the entire left lifting class of the actual trivial fibrations. -/
def cofibrationClass (O : ColoredOperadObj S.W S.C) : MorphismProperty (Algebra O) :=
  (trivialFibrationClass S O).llp

/-- The two original underlying conditions commute with all original color evaluations. -/
theorem trivialFibrationClass_eq (O : ColoredOperadObj S.W S.C) :
    trivialFibrationClass S O = fibrationClass S O ⊓ weakClass S O := by
  ext X Y f
  change (∀ d, fibrations S.C (f.hom d) ∧ weakEquivalences S.C (f.hom d)) ↔
    (∀ d, fibrations S.C (f.hom d)) ∧ (∀ d, weakEquivalences S.C (f.hom d))
  exact forall_and

/-- Both original supported families remain small at the caller's source size. -/
theorem freeGenerators_isSmall (O : ColoredOperadObj S.W S.C)
    (P : MorphismProperty S.C) [P.IsSmall.{us}] : (freeGenerators S O P).IsSmall.{us} := by
  let : (SemiModel.ColorSource.colorGenerators S.C S.W P).IsSmall.{us} :=
    SemiModel.ColorSource.colorGenerators_isSmall S.C S.W P
  exact IsSmall.strictMap inferInstance (freeAlgebraFunctor O)

section FixedCardinal

variable (O : ColoredOperadObj S.W S.C)
  [HasFiniteLimits (Algebra O)] [HasFiniteColimits (Algebra O)]
  (I J : MorphismProperty S.C)
  (hI : I.rlp = trivialFibrations S.C) (hJ : J.rlp = fibrations S.C)
  (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(freeGenerators S O I).IsCardinalForSmallObjectArgument κ]
  [(freeGenerators S O J).IsCardinalForSmallObjectArgument κ]
  (hAcyclicity : (freeGenerators S O J).rlp.llp ≤ weakClass S O)

/-- The actual two small-object arguments and derived acyclicity construct the full model. -/
@[instance_reducible]
def modelCategoryAtCardinal : ModelCategory (Algebra O) := by
  let : (freeGenerators S O I).HasSmallObjectArgument.{us} :=
    ⟨κ, inferInstance, inferInstance, inferInstance⟩
  let : (freeGenerators S O J).HasSmallObjectArgument.{us} :=
    ⟨κ, inferInstance, inferInstance, inferInstance⟩
  let : HasTwoOutOfThreeProperty
      (SemiModel.ColorSource.pointwiseProperty S.C S.W (weakEquivalences S.C)) :=
    SemiModel.ColorSource.pointwiseProperty_hasTwoOutOfThree S.C S.W (weakEquivalences S.C)
  let : (weakClass S O).HasTwoOutOfThreeProperty := by
    dsimp only [weakClass]
    infer_instance
  have hIRight : (freeGenerators S O I).rlp = trivialFibrationClass S O := by
    rw [freeGenerators_rlp, hI]
    rfl
  have hJRight : (freeGenerators S O J).rlp = fibrationClass S O := by
    rw [freeGenerators_rlp, hJ]
    rfl
  have hRight : (freeGenerators S O I).rlp =
      (freeGenerators S O J).rlp ⊓ weakClass S O := by
    rw [hIRight, hJRight, trivialFibrationClass_eq]
  let d := SmithModelStructureData.ofGenerators
    (freeGenerators S O I) (freeGenerators S O J) (weakClass S O)
    inferInstance hRight hAcyclicity
  letI : CategoryWithCofibrations (Algebra O) := ⟨cofibrationClass S O⟩
  letI : CategoryWithFibrations (Algebra O) := ⟨fibrationClass S O⟩
  letI : CategoryWithWeakEquivalences (Algebra O) := ⟨weakClass S O⟩
  exact d.modelCategory inferInstance (congrArg MorphismProperty.llp hIRight).symm
    hJRight.symm rfl

/-- The returned model has exactly the original underlying weak class. -/
theorem weakEquivalencesAtCardinal_eq :
    letI := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
    weakEquivalences (Algebra O) = weakClass S O := rfl

/-- The returned model has exactly the original underlying fibration class. -/
theorem fibrationsAtCardinal_eq :
    letI := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
    fibrations (Algebra O) = fibrationClass S O := rfl

/-- The returned cofibrations retain the full original trivial-fibration lifting class. -/
theorem cofibrationsAtCardinal_eq :
    letI := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
    cofibrations (Algebra O) = cofibrationClass S O := rfl

/-- The returned model has exactly both original trivial-fibration conditions. -/
theorem trivialFibrationsAtCardinal_eq :
    letI := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
    trivialFibrations (Algebra O) = trivialFibrationClass S O := by
  change fibrationClass S O ⊓ weakClass S O = trivialFibrationClass S O
  exact (trivialFibrationClass_eq S O).symm

/-- The selected model's trivial cofibrations are generated by the actual full free-J family. -/
theorem trivialCofibrationsAtCardinal_eq :
    letI := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
    trivialCofibrations (Algebra O) = (freeGenerators S O J).rlp.llp := by
  let := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
  rw [← fibrations_llp (Algebra O),
    fibrationsAtCardinal_eq S O I J hI hJ κ hAcyclicity, freeGenerators_rlp, hJ]
  rfl

/-- The generation record retains the caller's actual free families and original cardinal. -/
def generationDataAtCardinal :
    letI := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
    CofibrantGenerationData (Algebra O) κ := by
  letI := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
  exact
    { I := freeGenerators S O I
      J := freeGenerators S O J
      I_smallObject := inferInstance
      J_smallObject := inferInstance
      I_rlp := by
        rw [freeGenerators_rlp, hI,
          trivialFibrationsAtCardinal_eq S O I J hI hJ κ hAcyclicity]
        rfl
      J_rlp := by
        rw [freeGenerators_rlp, hJ,
          fibrationsAtCardinal_eq S O I J hI hJ κ hAcyclicity]
        rfl }

end FixedCardinal


end HomotopicalAlgebra.OperadicTransfer
