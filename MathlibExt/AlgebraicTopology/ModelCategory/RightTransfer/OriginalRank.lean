/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction

/-!
# Full right transfer at the original fixed source rank

This construction uses both complete small-object eligibility dictionaries
at the caller's original cardinal and ordinal bottom. It retains those
actual algorithms and creates the original weak/fibration classes. Fixed
eligibility is not enlarged into uniform relative smallness. The model,
generation and replacement factories are output of the construction.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty CategoryTheory.SmallObject

namespace HomotopicalAlgebra.RightTransfer

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D]
  (L : C ⥤ D) (R : D ⥤ C) (I J : MorphismProperty C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The full actual model and original generation at one unchanged source rank. -/
structure OriginalRankModelTransfer where
  complete : HasLimitsOfSize.{w, w} D
  cocomplete : HasColimitsOfSize.{w, w} D
  /-- The model created from both original fixed-rank small-object algorithms. -/
  model : ModelCategory D
  weak_eq : letI := model; weakEquivalences D = weakClass R
  fibrations_eq : letI := model; fibrations D = fibrationClass R
  cofibrations_eq : letI := model; cofibrations D = cofibrationClass R
  trivialFibrations_eq : letI := model; trivialFibrations D = trivialFibrationClass R
  trivialCofibrations_eq : letI := model; trivialCofibrations D = (J.strictMap L).rlp.llp
  /-- Cofibrant generation by the original free I/J families at the same cardinal. -/
  generation : letI := model; CofibrantGenerationData D κ
  generation_I : letI := model; generation.I = I.strictMap L
  generation_J : letI := model; generation.J = J.strictMap L

variable [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D]
  [(I.strictMap L).IsCardinalForSmallObjectArgument κ]
  [(J.strictMap L).IsCardinalForSmallObjectArgument κ]

/-- Both original fixed-rank algorithms and the actual acyclic-cell proof construct the full target model. -/
def originalRankModelTransfer (adj : L ⊣ R)
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (hAcyclicity : (J.strictMap L).rlp.llp ≤ weakClass R) :
    OriginalRankModelTransfer L R I J κ := by
  letI : HasLimitsOfSize.{0, 0} D := hasLimitsOfSizeOfUnivLE.{w, w} D
  letI : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeOfUnivLE.{w, w} D
  letI : (I.strictMap L).HasSmallObjectArgument.{w} :=
    ⟨κ, inferInstance, inferInstance, inferInstance⟩
  letI : (J.strictMap L).HasSmallObjectArgument.{w} :=
    ⟨κ, inferInstance, inferInstance, inferInstance⟩
  have hIRight : (I.strictMap L).rlp = trivialFibrationClass R := by
    rw [strictMap_rlp_eq_inverseImage_rlp I L R adj, hI]
  have hJRight : (J.strictMap L).rlp = fibrationClass R := by
    rw [strictMap_rlp_eq_inverseImage_rlp J L R adj, hJ]
  have hRight : (I.strictMap L).rlp = (J.strictMap L).rlp ⊓ weakClass R := by
    rw [hIRight, hJRight]
    rfl
  let M : ModelCategory D := by
    let smith := SmithModelStructureData.ofGenerators (I.strictMap L) (J.strictMap L)
      (weakClass R) inferInstance hRight hAcyclicity
    letI : CategoryWithCofibrations D := ⟨cofibrationClass R⟩
    letI : CategoryWithFibrations D := ⟨fibrationClass R⟩
    letI : CategoryWithWeakEquivalences D := ⟨weakClass R⟩
    exact smith.modelCategory inferInstance (congrArg MorphismProperty.llp hIRight).symm hJRight.symm rfl
  letI : ModelCategory D := M
  have hTF : trivialFibrations D = trivialFibrationClass R := rfl
  have hF : fibrations D = fibrationClass R := rfl
  have hTC : trivialCofibrations D = (J.strictMap L).rlp.llp := by
    rw [← fibrations_llp D, hF, ← hJRight]
  refine
    { complete := inferInstance
      cocomplete := inferInstance
      model := M
      weak_eq := rfl
      fibrations_eq := hF
      cofibrations_eq := rfl
      trivialFibrations_eq := hTF
      trivialCofibrations_eq := hTC
      generation :=
        { I := I.strictMap L
          J := J.strictMap L
          I_smallObject := inferInstance
          J_smallObject := inferInstance
          I_rlp := ?_
          J_rlp := ?_ }
      generation_I := rfl
      generation_J := rfl }
  · rw [hIRight, hTF]
  · rw [hJRight, hF]

namespace OriginalRankModelTransfer

variable {L R I J κ} (t : OriginalRankModelTransfer L R I J κ)

/-- The same original rank and both full generation records construct the actual Q/R factories. -/
def replacements :
    letI : ModelCategory D := t.model
    GeneratedFunctorialReplacements.Data (C := D) := by
  letI : ModelCategory D := t.model
  exact GeneratedFunctorialReplacements.fromGeneration t.generation

end OriginalRankModelTransfer
end HomotopicalAlgebra.RightTransfer
