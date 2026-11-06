/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthStabilizerProjection

/-! Exact actual tensor stabilization and the remaining short-phase condition for the full axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Fixing the actual fourth-axis tensor is exactly membership in the verified affine subgroup. -/
theorem generatedFourthQAffineTensor_actual_fixed_iff (q : Q) :
    (∀ j, spinRepresentation q (fun t => (griessConwayEncode generatedFourthAxis).2.2 t j) =
      fun t => (griessConwayEncode generatedFourthAxis).2.2 t j) ↔
    q ∈ generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases
          generatedAxisFourthQAffineParameterCharacters := by
  rw [generatedFourthQAffineTensor_actual]
  exact generatedFourthQAffineTensor_fixed_iff q

/-- Exactly 128 genuine Q elements fix the entire actual fourth-axis tensor. -/
theorem generatedFourthQAffineTensor_actual_stabilizer_card :
    Nat.card {q : Q // ∀ j,
      spinRepresentation q (fun t => (griessConwayEncode generatedFourthAxis).2.2 t j) =
        fun t => (griessConwayEncode generatedFourthAxis).2.2 t j} = 128 := by
  rw [generatedFourthQAffineTensor_actual]
  exact generatedFourthQAffineTensor_stabilizer_card

/-- Full axis fixation additionally requires every supported original short phase to vanish. -/
theorem generatedFourthAxisQStabilizer_mem_affine_iff (q : Q) :
    q ∈ generatedFourthAxisQStabilizer ↔
      (∀ r, (griessConwayEncode generatedFourthAxis).2.1 r ≠ 0 → localAxisQPhase r q = 1) ∧
        q ∈ generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
          generatedAxisFourthQAffineParameterBases
          generatedAxisFourthQAffineParameterCharacters := by
  rw [generatedFourthAxisQStabilizer_mem_iff, generatedFourthQAffineTensor_actual_fixed_iff]

/-- The genuine full-axis Q stabilizer is contained in the exactly counted affine subgroup. -/
theorem generatedFourthAxisQStabilizer_le_affine :
    generatedFourthAxisQStabilizer ≤
      generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
        generatedAxisFourthQAffineParameterBases
          generatedAxisFourthQAffineParameterCharacters := by
  intro q hq
  exact ((generatedFourthAxisQStabilizer_mem_affine_iff q).mp hq).2

/-- The actual projection kernel has at most 128 elements; equality still needs short fixation. -/
theorem generatedFourthLocalAxisProjection_kernel_card_le :
    Nat.card generatedFourthLocalAxisProjection.ker ≤ 128 := by
  rw [generatedFourthLocalAxisProjection_kernel_card]
  let f : generatedFourthAxisQStabilizer →
      generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
        generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters :=
    fun q => ⟨q.val, generatedFourthAxisQStabilizer_le_affine q.property⟩
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    exact congrArg (fun y : generatedAxisFourthQAffineFamilyStabilizer
      generatedAxisFourthQAffineParameterPlane generatedAxisFourthQAffineParameterBases
      generatedAxisFourthQAffineParameterCharacters => y.val) h
  exact (Nat.card_le_card_of_injective f hf).trans_eq
    generatedAxisFourthQAffineParameter_stabilizer_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
