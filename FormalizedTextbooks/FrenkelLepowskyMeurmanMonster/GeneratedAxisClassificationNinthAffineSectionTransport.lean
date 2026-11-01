/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineTransportNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpatialStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthMonomialMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitAction

/-! The literal genuine Ninth transport sends the actual whole matrix section to the
original selected E8 coordinate section. Entire spatial stabilizers therefore conjugate
into the genuine original section group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The coordinate projection of the original selected genuine Golay octad. -/
def generatedNinthAffineOriginalProjection : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.diagonal (fun i => if golayOctadWord generatedFifthFlagOctad i = 0 then 0 else 1)

/-- The original permutation word carries the actual destination octad to the original section. -/
theorem generatedNinth_affine_octad_transport :
    golayPermute generatedNinthAffineOctadPermutation.val
      (golayOctadWord generatedNinthSectionOctad) = golayOctadWord generatedFifthFlagOctad := by
  simp only [golayOctadWord, generatedNinth_section_octad_label, generatedFifthFlagOctad_label]
  exact generatedNinth_affine_octad_word

/-- The genuine original permutation transports the whole actual coordinate projection. -/
theorem generatedNinth_affine_coordinate_projection_transport :
    conwayMatrixAction (golayPermutationIsometry generatedNinthAffineOctadPermutation)
      generatedNinthSectionProjection = generatedNinthAffineOriginalProjection := by
  have hm := generatedEighth_monomial_diagonal (0 : golayCode)
    generatedNinthAffineOctadPermutation
    (fun i => if golayOctadWord generatedNinthSectionOctad i = 0 then (0 : ℝ) else 1)
  have hz : golaySignIsometry 0 = 1 := golaySignHom.map_one
  rw [golayMonomialPair, hz, one_mul] at hm
  trans Matrix.diagonal (fun i => if golayOctadWord generatedNinthSectionOctad
    (generatedNinthAffineOctadPermutation.val.symm i) = 0 then (0 : ℝ) else 1)
  · exact hm
  change Matrix.diagonal (fun i => if golayOctadWord generatedNinthSectionOctad
      (generatedNinthAffineOctadPermutation.val.symm i) = 0 then (0 : ℝ) else 1) =
    Matrix.diagonal (fun i => if golayOctadWord generatedFifthFlagOctad i = 0 then 0 else 1)
  apply congrArg Matrix.diagonal
  funext i
  have hi := congrFun generatedNinth_affine_octad_transport i
  change golayOctadWord generatedNinthSectionOctad
      (generatedNinthAffineOctadPermutation.val.symm i) =
    golayOctadWord generatedFifthFlagOctad i at hi
  rw [hi]

/-- The complete genuine transport carries the original actual low projection to the E8 section. -/
theorem generatedNinth_affine_low_projection_transport :
    conwayMatrixAction generatedNinthAffineTransport generatedNinthLowProjection =
      generatedNinthAffineOriginalProjection := by
  change conwayMatrixAction
      (golayPermutationIsometry generatedNinthAffineOctadPermutation *
        generatedNinthSectionTransport) generatedNinthLowProjection = _
  rw [map_mul]
  change conwayMatrixAction (golayPermutationIsometry generatedNinthAffineOctadPermutation)
      (conwayMatrixAction generatedNinthSectionTransport generatedNinthLowProjection) = _
  rw [generatedNinth_section_projection_transport,
    generatedNinth_affine_coordinate_projection_transport]

/-- Every actual whole-matrix stabilizer conjugates into the genuine original E8 section group. -/
theorem generatedNinth_affine_spatial_conjugate_mem_section
    (g : leechIsomSubgroup) (hg : g ∈ generatedNinthSpatialStabilizer) :
    generatedNinthAffineTransport * g * generatedNinthAffineTransport⁻¹ ∈
      generatedAxisE8FrameSystemSectionGroup := by
  rw [generatedAxisE8SectionStabilizer_mem]
  apply (generatedAxisE8_matrix_action_iff_section_stabilizer
    (golayOctadWord generatedFifthFlagOctad) _).mp
  have hfix : conwayMatrixAction g generatedNinthLowProjection = generatedNinthLowProjection :=
    (generatedNinth_matrix_stabilizer_iff g).mp hg
  have hinv : conwayMatrixAction generatedNinthAffineTransport⁻¹
      generatedNinthAffineOriginalProjection = generatedNinthLowProjection := by
    rw [map_inv]
    exact (conwayMatrixAction generatedNinthAffineTransport).symm_apply_eq.mpr
      generatedNinth_affine_low_projection_transport.symm
  change conwayMatrixAction (generatedNinthAffineTransport * g * generatedNinthAffineTransport⁻¹)
    generatedNinthAffineOriginalProjection = generatedNinthAffineOriginalProjection
  rw [map_mul, map_mul]
  change conwayMatrixAction generatedNinthAffineTransport
      (conwayMatrixAction g (conwayMatrixAction generatedNinthAffineTransport⁻¹
        generatedNinthAffineOriginalProjection)) = generatedNinthAffineOriginalProjection
  rw [hinv, hfix, generatedNinth_affine_low_projection_transport]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
