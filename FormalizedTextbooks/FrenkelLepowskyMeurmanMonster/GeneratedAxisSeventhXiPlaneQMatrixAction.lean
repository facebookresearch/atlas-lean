/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneQMatrixCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisExt

/-! The certified full central-bit matrix is the genuine corrected Xi automorphism of actual Q. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The exact source cocycle certificate defines a homomorphism of the unchanged actual Q. -/
def generatedSeventhXiPlaneQMatrixHom : Q →* Q :=
  generatedFourthLiftQMatrixHom generatedSeventhXiPlaneQMatrix
    generatedSeventhXiPlaneQPhaseMatrix generatedSeventhXiPlaneQMatrix_cocycle

/-- Preferred-basis and center equality identifies the full genuine source automorphism. -/
theorem generatedSeventhXiPlaneQMatrixHom_eq_actual :
    generatedSeventhXiPlaneQMatrixHom =
      (spinConjugation generatedSeventhXiPlaneFiber.val.1).toMonoidHom := by
  apply generatedFourth_lift_q_hom_ext
  · intro j
    rw [MulEquiv.coe_toMonoidHom, generatedSeventhXiPlaneQImage_actual]
    have h := generatedSeventhXiPlaneQMatrix_basis j
    apply NormalizedCocycleExtension.Extension.ext
    · exact (toAdd.injective h.1).symm
    · apply toAdd.injective
      change 0 + generatedFourthLiftQMatrixPhase generatedSeventhXiPlaneQPhaseMatrix
          (Pi.single j 1) = _
      rw [zero_add]
      exact h.2.symm
  · change generatedSeventhXiPlaneQMatrixHom (qCentral 1) = spinConjugation _ (qCentral 1)
    rw [spinConjugation_central]
    apply NormalizedCocycleExtension.Extension.ext
    · change ofAdd (generatedSeventhXiPlaneQMatrix *ᵥ 0) = ofAdd 0
      rw [Matrix.mulVec_zero]
    · change ofAdd (1 + generatedFourthLiftQMatrixPhase generatedSeventhXiPlaneQPhaseMatrix 0) =
        ofAdd 1
      simp only [generatedFourthLiftQMatrixPhase, map_zero, add_zero]

/-- The finite formula gives every genuine preferred-Q image and its full central coefficient. -/
theorem generatedSeventhXiPlaneQMatrixHom_apply (q : Q) :
    generatedSeventhXiPlaneQMatrixHom q = generatedSeventhXiPlaneQImage q := by
  have h := DFunLike.congr_fun generatedSeventhXiPlaneQMatrixHom_eq_actual q
  exact h.trans (generatedSeventhXiPlaneQImage_actual q)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
