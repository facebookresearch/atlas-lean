/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A global twenty-three-coordinate identity test using the actual Q commutator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTwentyThreeIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- One fixed hyperbolic coordinate pair has the genuine central involution as commutator. -/
theorem monsterNortonCoordinate_commutator_zero_twelve :
    qCoordinateGenerator 0 * qCoordinateGenerator 12 *
      (qCoordinateGenerator 0)⁻¹ * (qCoordinateGenerator 12)⁻¹ = qCentralInvolution := by
  apply NormalizedCocycleExtension.Extension.ext
  · funext i
    revert i
    decide +kernel
  · decide +kernel

/-- Commuting with the twenty-three stated coordinates already centralizes actual z. -/
theorem monsterNortonGenerated_twentyThree_centralizes (g : G)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute g (qIntoGenerated (qCoordinateGenerator i))) :
    Commute g (qIntoGenerated qCentralInvolution) := by
  have h0 := hi 0 (by decide)
  have h12 := hi 12 (by decide)
  have hc := ((h0.mul_right h12).mul_right h0.inv_right).mul_right h12.inv_right
  have he : qIntoGenerated
      (qCoordinateGenerator 0 * qCoordinateGenerator 12 *
        (qCoordinateGenerator 0)⁻¹ * (qCoordinateGenerator 12)⁻¹) =
      qIntoGenerated (qCoordinateGenerator 0) * qIntoGenerated (qCoordinateGenerator 12) *
        (qIntoGenerated (qCoordinateGenerator 0))⁻¹ *
          (qIntoGenerated (qCoordinateGenerator 12))⁻¹ := by
    simp only [map_mul, map_inv]
  rw [← he, monsterNortonCoordinate_commutator_zero_twelve] at hc
  exact hc

/-- The actual full centralizer theorem supplies local membership from these finite checks. -/
theorem monsterNortonGenerated_twentyThree_mem_local (g : G)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute g (qIntoGenerated (qCoordinateGenerator i))) :
    g ∈ localIntoGenerated.range := by
  have hg : g ∈ Subgroup.centralizer {qIntoGenerated qCentralInvolution} :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (monsterNortonGenerated_twentyThree_centralizes g hi)
  rw [generatedCentralizer_eq_local_range] at hg
  exact hg

/-- Twenty-three genuine Q checks and the actual delta-zero tensor suffice globally. -/
theorem monsterNortonGenerated_twentyThree_global_identity (g : G)
    (hi : ∀ i : Fin 24, i ≠ 23 → Commute g (qIntoGenerated (qCoordinateGenerator i)))
    (hx : g.val monsterNortonTwentyThreeTensorVector = monsterNortonTwentyThreeTensorVector) :
    g = 1 :=
  monsterNortonGenerated_twentyThree_identity g
    (monsterNortonGenerated_twentyThree_mem_local g hi) hi hx

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
