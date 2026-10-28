/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorStabilizerActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasis

/-! Exact full-axis Q stabilization from the genuine seven-generator short fixes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine affine generator fixes both the actual short and actual tensor blocks. -/
theorem generatedFourth_axis_q_basis_mem (i : Fin 7) :
    generatedFourthQAffineParameterBasis i ∈ generatedFourthAxisQStabilizer := by
  rw [generatedFourthAxisQStabilizer_mem_affine_iff]
  constructor
  · exact (generatedFourthQ_short_fixed_iff _ _).mp
      (generatedFourthQShortBasis_short_fixed i)
  · change (generatedFourthQAffineParameterGroupEquiv.symm
      (Multiplicative.ofAdd (Pi.single i 1))).val ∈ _
    exact (generatedFourthQAffineParameterGroupEquiv.symm
      (Multiplicative.ofAdd (Pi.single i 1))).property

/-- The genuine full-axis Q stabilizer is exactly the already counted affine tensor subgroup. -/
theorem generatedFourth_axis_q_stabilizer_eq_affine :
    generatedFourthAxisQStabilizer =
      generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
        generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters := by
  apply le_antisymm generatedFourthAxisQStabilizer_le_affine
  exact generatedFourthQAffineParameterBasis_generates _ generatedFourth_axis_q_basis_mem

/-- Exactly 128 genuine Q elements fix the entire original fourth axis. -/
theorem generatedFourth_axis_q_stabilizer_card : Nat.card generatedFourthAxisQStabilizer = 128 := by
  rw [generatedFourth_axis_q_stabilizer_eq_affine]
  exact generatedAxisFourthQAffineParameter_stabilizer_card

/-- The actual fourth local-axis projection has full-axis kernel of order 128. -/
theorem generatedFourth_local_axis_projection_kernel_card :
    Nat.card generatedFourthLocalAxisProjection.ker = 128 := by
  rw [generatedFourthLocalAxisProjection_kernel_card, generatedFourth_axis_q_stabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
