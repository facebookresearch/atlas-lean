/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual transport of the four-point coefficient and its line-word centralizer to H. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsFourPointLattice
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLineCentralizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaNormEight
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual norm-eight transitivity supplies the required Conway binary transport. -/
theorem monsterNortonFourPoint_binaryTransport :
    ∃ c : Co1, co1BinaryAction c
      (Multiplicative.toAdd (qQuotHom (sourceQCocode (golayLabelCoefficients 924)))) =
        Multiplicative.toAdd (qQuotHom sourceOmegaQ) :=
  localOmega_binary_transport_of_normEight _ _ monsterNortonFourPointLattice_squareSum
    monsterNortonFourPointLattice_binary

/-- The actual four-point lift is locally conjugate to Ω, including its central phase. -/
theorem monsterNortonFourPoint_localConjugate :
    ∃ h : H, h * inclQ (sourceQCocode (golayLabelCoefficients 924)) * h⁻¹ =
      inclQ sourceOmegaQ :=
  localOmega_conjugate_of_normEight _ _ monsterNortonFourPointLattice_squareSum
    monsterNortonFourPointLattice_binary

/-- The first remaining actual line ratio has an actual local-group conjugate. -/
theorem monsterNortonLineZeroOne_localConjugate :
    ∃ h : H, extraIntoGenerated *
      (localIntoGenerated h *
        (y555NortonLine monsterSourceTriality 0 *
          (y555NortonLine monsterSourceTriality 1)⁻¹) * (localIntoGenerated h)⁻¹) *
      extraIntoGenerated⁻¹ ∈ localIntoGenerated.range :=
  generated_commuting_q_conjugate_local_of_normEight _ _
    monsterNortonFourPointLattice_squareSum monsterNortonFourPointLattice_binary _
    monsterNortonLineZeroOne_commutes_fourPoint

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
