/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.ModelCategory.HomotopyFunctionComplexCalculus
public import
  MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith

/-!
# Smith existence for generic left Bousfield localization

This file combines generic Beke--Smith recognition with explicit
tensor--Hom, SM7, and homotopy-function-complex calculus data.  It returns
complete left-localization recognition data and installs no model structure,
instance, or specialization on the ambient category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [SimplicialCategory C]
variable [HasFunctorialFactorization
  (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]

/-- Generic Smith recognition and explicit mapping-space calculus produce
complete left Bousfield localization data. -/
theorem leftBousfieldLocalizationDataOfSmith
    (sm : SimplicialModelCategoryData (C := C))
    (precomp : HomotopyFunctionComplexPrecompData (C := C))
    (calculus : HomotopyFunctionComplexCalculusData (C := C))
    {K : Type w} (S : K → Arrow C)
    (I : MorphismProperty C)
    [IsLocallyPresentable.{w} C]
    [I.HasSmallObjectArgument.{w}]
    (hI : I.rlp = trivialFibrations C)
    (hSmith : SmithRecognitionInput.{w}
      (C := C) I (localEquivalences S)) :
    Nonempty (LeftBousfieldLocalizationData S) := by
  let W := localEquivalences S
  obtain ⟨M⟩ := smithRecognition I W hSmith
  have hCof : I.rlp.llp = cofibrations C := by
    rw [hI]
    exact trivialFibrations_llp C
  have hLeft : M.J.rlp.llp = cofibrations C ⊓ W := by
    calc
      M.J.rlp.llp = I.rlp.llp ⊓ W := M.trivialCofibrations_eq
      _ = cofibrations C ⊓ W := congrArg (fun P ↦ P ⊓ W) hCof
  have hRight : M.J.rlp = localizedFibrations S := by
    rw [M.fibrations_eq, hCof]
    rfl
  have hLocalizedWfs : IsWeakFactorizationSystem
      (cofibrations C ⊓ W) (localizedFibrations S) := by
    rw [← hLeft, ← hRight]
    exact M.trivialCofibration_wfs
  have hTrivialFibrations :
      localizedFibrations S ⊓ W = trivialFibrations C := by
    calc
      localizedFibrations S ⊓ W = M.J.rlp ⊓ W :=
        congrArg (fun P ↦ P ⊓ W) hRight.symm
      _ = I.rlp := M.trivialFibrations_eq
      _ = trivialFibrations C := hI
  have hSelected (k : K) : W (S k).hom := by
    intro Z hZ
    exact hZ.2 k
  exact ⟨{
    localizingMaps := hSelected
    baseWeak_le := weakEquivalences_le_localEquivalences precomp S
    two_out_of_three := localEquivalences_hasTwoOutOfThreeProperty S
    retracts := localEquivalences_isStableUnderRetracts S
    localized_wfs := hLocalizedWfs
    trivialFibrations_eq := hTrivialFibrations
    fibrant_iff :=
      localizedFibrations_terminal_iff sm precomp calculus S
    weakEquivalence_iff_of_local :=
      localEquivalences_weakEquivalence_iff_of_local
        sm precomp calculus S
  }⟩

end HomotopicalAlgebra
