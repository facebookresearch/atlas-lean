/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkSmithInput
import MathlibExt.AlgebraicTopology.SimplicialSpace.TerminalFibrancy

/-!
# The Rezk model structure on simplicial spaces

Smith recognition is applied directly to the literal Reedy boundary family
and the genuine all-complete-Segal-space Rezk weak class.  The resulting model
has monomorphisms as cofibrations and right orthogonals of monic Rezk weak maps
as fibrations.  The recognition family, both weak factorization systems, one
common generation cardinal, cofibrant-generation data, and the exact class
identities are all retained.

The selected model is exposed as a named, opt-in instance.  Its fibrant
objects are exactly the complete Segal spaces by the already proved full
terminal lifting criterion.  No simplicial-model, Cartesian-model, comparison,
or derived mapping assertion is made here.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace.RezkModel

/-- The complete Rezk model witness, including Smith's selected second family,
both weak factorization systems, common-cardinal generation data, and the
complete-Segal fibrancy characterization. -/
theorem exists_modelCategory :
    let C := SimplicialSpace.{u}
    let I := ReedyGeneratingFamilies.I.{u}
    let W := rezkWeakEquivalences.{u}
    let Monos := monomorphisms C
    let T := Monos ⊓ W
    let F := T.rlp
    ∃ (s : SmithModelStructureData.{u} (C := C) I W)
      (M : ModelCategory C),
      letI : ModelCategory C := M
      let G := s.J
      ∃ ν : Cardinal.{u},
      ∃ regular : Fact ν.IsRegular,
      letI : Fact ν.IsRegular := regular
      ∃ bottom : OrderBot ν.ord.ToType,
      letI : OrderBot ν.ord.ToType := bottom
      ∃ cg : CofibrantGenerationData C ν,
        M.categoryWithCofibrations.cofibrations = Monos ∧
        M.categoryWithWeakEquivalences.weakEquivalences = W ∧
        M.categoryWithFibrations.fibrations = F ∧
        trivialCofibrations C = T ∧
        trivialFibrations C = I.rlp ∧
        I.rlp = Monos.rlp ∧
        F ⊓ W = I.rlp ∧
        IsWeakFactorizationSystem Monos I.rlp ∧
        IsWeakFactorizationSystem T F ∧
        G.rlp = F ∧
        G.rlp.llp = T ∧
        G ≤ T ∧
        I.IsSmall.{u} ∧ G.IsSmall.{u} ∧
        I.HasSmallObjectArgument.{u} ∧ G.HasSmallObjectArgument.{u} ∧
        IsCardinalLocallyPresentable C ν ∧
        I.IsCardinalForSmallObjectArgument ν ∧
        G.IsCardinalForSmallObjectArgument ν ∧
        cg.I = I ∧ cg.J = G ∧
        IsCombinatorialModelCategory.{u} C ∧
        (∀ X : C, IsFibrant X ↔ completeSegalSpaces X) := by
  let C := SimplicialSpace.{u}
  let I := ReedyGeneratingFamilies.I.{u}
  let W := rezkWeakEquivalences.{u}
  let Monos := monomorphisms C
  let T := Monos ⊓ W
  let F := T.rlp
  let _ : IsLocallyPresentable.{u} C := SimplicialSpace.isLocallyPresentable
  let _ : HasLimitsOfSize.{u, u} C :=
    { has_limits_of_shape := fun J _ => SimplicialSpace.hasLimitsOfShape J }
  let _ : HasColimitsOfSize.{u, u} C :=
    { has_colimits_of_shape := fun J _ => SimplicialSpace.hasColimitsOfShape J }
  let _ : I.IsSmall.{u} := ReedyGeneratingFamilies.isSmall_I
  let _ : I.HasSmallObjectArgument.{u} :=
    hasSmallObjectArgument_of_isSmall I
  let h := rezkSmithRecognitionInput.{u}
  obtain ⟨s⟩ := smithRecognition I W h
  have hILeft : I.rlp.llp = Monos :=
    ReedyGeneratingFamilies.I_rlp_llp_eq_monomorphisms
  have hIRight : I.rlp = Monos.rlp := by
    calc
      I.rlp = I.rlp.llp.rlp := I.rlp_llp_rlp.symm
      _ = Monos.rlp := congrArg MorphismProperty.rlp hILeft
  have hLeft : s.J.rlp.llp = T := by
    rw [s.trivialCofibrations_eq, hILeft]
  have hFib : s.J.rlp = F := by
    rw [s.fibrations_eq, hILeft]
  have hTF : F ⊓ W = I.rlp := by
    rw [← hFib]
    exact s.trivialFibrations_eq
  have hFirst : IsWeakFactorizationSystem Monos I.rlp := by
    simpa only [hILeft] using s.cofibration_wfs
  have hSecond : IsWeakFactorizationSystem T F := by
    rw [← hLeft, ← hFib]
    exact s.trivialCofibration_wfs
  let _ : CategoryWithCofibrations C := ⟨Monos⟩
  let _ : CategoryWithWeakEquivalences C := ⟨W⟩
  let _ : CategoryWithFibrations C := ⟨F⟩
  let M : ModelCategory C :=
    s.modelCategory h.weak_two_out_of_three hILeft.symm hFib.symm rfl
  have hMCof : M.categoryWithCofibrations.cofibrations = Monos := rfl
  have hMW : M.categoryWithWeakEquivalences.weakEquivalences = W := rfl
  have hMFib : M.categoryWithFibrations.fibrations = F := rfl
  refine ⟨s, M, ?_⟩
  let _ : ModelCategory C := M
  let _ : s.J.HasSmallObjectArgument.{u} := s.J_smallObject
  obtain ⟨ν, regular, bottom, hLP, hIν, hGν⟩ :=
    exists_common_generation_cardinal I s.J
  refine ⟨ν, regular, ?_⟩
  let _ : Fact ν.IsRegular := regular
  refine ⟨bottom, ?_⟩
  let _ : OrderBot ν.ord.ToType := bottom
  have hTCModel : trivialCofibrations C = T := rfl
  have hTFModel : trivialFibrations C = I.rlp := hTF
  let cg : CofibrantGenerationData C ν :=
    { I := I
      J := s.J
      I_smallObject := hIν
      J_smallObject := hGν
      I_rlp := hTFModel.symm
      J_rlp := hFib }
  have hISmall : I.IsSmall.{u} := hIν.isSmall
  have hGSmall : s.J.IsSmall.{u} := hGν.isSmall
  have hGMem : s.J ≤ T := s.J.le_llp_rlp.trans hLeft.le
  have hFibrant : ∀ X : C, IsFibrant X ↔ completeSegalSpaces X := by
    intro X
    rw [isFibrant_iff_of_isTerminal (terminal.from X) terminalIsTerminal,
      HomotopicalAlgebra.fibration_iff]
    change F (terminal.from X) ↔ completeSegalSpaces X
    exact
      monomorphisms_inf_rezkWeakEquivalences_terminal_rlp_iff_completeSegalSpaces X
  refine ⟨cg, hMCof, hMW, hMFib, hTCModel, hTFModel, hIRight, hTF,
    hFirst, hSecond, hFib, hLeft, hGMem, hISmall, hGSmall,
    inferInstance, s.J_smallObject, hLP, hIν, hGν, rfl, rfl, ?_, hFibrant⟩
  exact { exists_cardinal := ⟨ν, regular, bottom, hLP, ⟨cg⟩⟩ }

/-- The selected Rezk model structure on the designated simplicial-space
carrier. -/
@[instance_reducible]
noncomputable def modelCategory : ModelCategory SimplicialSpace.{u} :=
  exists_modelCategory.{u}.choose_spec.choose

private theorem modelCategory_classifying_properties :
    modelCategory.{u}.categoryWithCofibrations.cofibrations =
        monomorphisms SimplicialSpace.{u} ∧
      modelCategory.{u}.categoryWithWeakEquivalences.weakEquivalences =
        rezkWeakEquivalences.{u} ∧
      modelCategory.{u}.categoryWithFibrations.fibrations =
        (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}).rlp ∧
      (letI : ModelCategory SimplicialSpace.{u} := modelCategory
       trivialCofibrations SimplicialSpace.{u} =
         monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}) ∧
      (letI : ModelCategory SimplicialSpace.{u} := modelCategory
       trivialFibrations SimplicialSpace.{u} =
         ReedyGeneratingFamilies.I.{u}.rlp) ∧
      (∀ X : SimplicialSpace.{u},
        letI : ModelCategory SimplicialSpace.{u} := modelCategory
        IsFibrant X ↔ completeSegalSpaces X) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  obtain ⟨ν, regular, h⟩ := exists_modelCategory.{u}.choose_spec.choose_spec
  let _ : Fact ν.IsRegular := regular
  obtain ⟨bottom, h⟩ := h
  let _ : OrderBot ν.ord.ToType := bottom
  obtain ⟨_, hCof, hW, hFib, hTC, hTF, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hFibrant⟩ := h
  exact ⟨hCof, hW, hFib, hTC, hTF, hFibrant⟩

/-- Cofibrations in the selected Rezk model are the original monomorphisms. -/
theorem modelCategory_cofibrations :
    modelCategory.{u}.categoryWithCofibrations.cofibrations =
      monomorphisms SimplicialSpace.{u} :=
  modelCategory_classifying_properties.{u}.1

/-- Weak equivalences in the selected Rezk model are exactly the genuine
all-CSS Rezk weak equivalences. -/
theorem modelCategory_weakEquivalences :
    modelCategory.{u}.categoryWithWeakEquivalences.weakEquivalences =
      rezkWeakEquivalences.{u} :=
  modelCategory_classifying_properties.{u}.2.1

/-- Fibrations in the selected Rezk model are the right orthogonals of the
original monic Rezk weak maps. -/
theorem modelCategory_fibrations :
    modelCategory.{u}.categoryWithFibrations.fibrations =
      (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}).rlp :=
  modelCategory_classifying_properties.{u}.2.2.1

/-- Trivial cofibrations in the selected Rezk model are exactly the original
monic Rezk weak maps. -/
theorem modelCategory_trivialCofibrations :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    trivialCofibrations SimplicialSpace.{u} =
      monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u} :=
  modelCategory_classifying_properties.{u}.2.2.2.1

/-- Trivial fibrations in the selected Rezk model are the literal Reedy
boundary-RLP maps. -/
theorem modelCategory_trivialFibrations :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    trivialFibrations SimplicialSpace.{u} =
      ReedyGeneratingFamilies.I.{u}.rlp :=
  modelCategory_classifying_properties.{u}.2.2.2.2.1

/-- Fibrant objects in the selected Rezk model are exactly complete Segal
spaces in the adopted locality definition. -/
theorem isFibrant_iff_completeSegalSpaces (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsFibrant X ↔ completeSegalSpaces X :=
  modelCategory_classifying_properties.{u}.2.2.2.2.2 X

/-- Combinatoriality of the selected scalar model uses its same original
common-cardinal witness and generating families. -/
theorem modelCategory_isCombinatorial :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    IsCombinatorialModelCategory.{u} SimplicialSpace.{u} := by
  letI : ModelCategory SimplicialSpace.{u} := modelCategory
  obtain ⟨κ, regular, h⟩ := exists_modelCategory.{u}.choose_spec.choose_spec
  letI : Fact κ.IsRegular := regular
  obtain ⟨bottom, h⟩ := h
  letI : OrderBot κ.ord.ToType := bottom
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCombinatorial, _⟩ := h
  exact hCombinatorial

namespace ModelCategory

/-- Opt-in Rezk model-category instance on simplicial spaces. -/
noncomputable scoped instance instModelCategory :
    HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} :=
  RezkModel.modelCategory

/-- Opt-in combinatoriality belongs to that same selected scalar model. -/
scoped instance instIsCombinatorialModelCategory :
    letI : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    IsCombinatorialModelCategory.{u} SimplicialSpace.{u} :=
  modelCategory_isCombinatorial

end ModelCategory

end SimplicialSpace.RezkModel
