/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneLiftWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortBasisExt
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

/-! Full preferred-Q image equality binds the original word to its compact conjugating operator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original source word and the compact operator have identical full automorphisms of Q. -/
theorem generatedSeventhXiPlane_compact_conjugation :
    spinConjugation generatedSeventhXiPlanePermutationFiber.val.1 =
      spinConjugation generatedSeventhXiPlaneCompactSpin := by
  apply MulEquiv.toMonoidHom_injective
  apply generatedFourth_lift_q_hom_ext
  · intro j
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
      generatedSeventhXiPlanePermutationFiber_basis,
      generatedSeventhXiPlaneCompactSpin_conjugation]
    have h := generatedSeventhXiPlaneCompactImage_basis j
    exact (NormalizedCocycleExtension.Extension.ext
      (toAdd.injective h.1) (toAdd.injective h.2)).symm
  · change spinConjugation _ (qCentral 1) = spinConjugation _ (qCentral 1)
    rw [spinConjugation_central, spinConjugation_central]

private theorem kernel_commutes (k : spinConjugation.ker) (s : SpinHolomorph) :
    k.val * s = s * k.val := by
  obtain ⟨c, _, hc⟩ := spinHolomorph_conjugation_kernel_scalar k
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change k.val.val (s.val x) = s.val (k.val.val x)
  rw [hc, hc, map_smul]

private theorem conjugate_eq (p c s : SpinHolomorph)
    (he : spinConjugation p = spinConjugation c) :
    p * s * p⁻¹ = c * s * c⁻¹ := by
  have hk : p * c⁻¹ ∈ spinConjugation.ker := by
    change spinConjugation (p * c⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have h := kernel_commutes ⟨p * c⁻¹, hk⟩ (c * s * c⁻¹)
  change (p * c⁻¹) * (c * s * c⁻¹) = (c * s * c⁻¹) * (p * c⁻¹) at h
  calc
    p * s * p⁻¹ = ((p * c⁻¹) * (c * s * c⁻¹)) * c * p⁻¹ := by group
    _ = ((c * s * c⁻¹) * (p * c⁻¹)) * c * p⁻¹ := by rw [h]
    _ = c * s * c⁻¹ := by group

/-- Scalar ambiguity cancels in conjugation, so every conjugated spin operator is exact. -/
theorem generatedSeventhXiPlane_compact_conjugate (s : SpinHolomorph) :
    generatedSeventhXiPlanePermutationFiber.val.1 * s *
        generatedSeventhXiPlanePermutationFiber.val.1⁻¹ =
      generatedSeventhXiPlaneCompactSpin * s * generatedSeventhXiPlaneCompactSpin⁻¹ :=
  conjugate_eq _ _ s generatedSeventhXiPlane_compact_conjugation

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
