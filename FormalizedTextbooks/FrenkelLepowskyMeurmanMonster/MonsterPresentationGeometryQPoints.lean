/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact classification of central-involution conjugates inside the genuine extraspecial Q. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryShortTrace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometrySingularCover
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFramePhases

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual central-involution conjugates inside Q have singular binary coordinates. -/
theorem monsterGeometryQ_point_singular (q : Q)
    (h : IsConj generatedCentralInvolution (qIntoGenerated q)) :
    squareQuad (toAdd (qQuotHom q)) = 0 := by
  have hs : q * q = 1 := by
    apply qIntoGenerated_injective
    rw [map_mul, map_one]
    exact (pow_two (qIntoGenerated q)).symm.trans (monsterGeometryPoint_square ⟨_, h⟩)
  rw [squareQuad_eq_centerMap_square]
  have he : (⟨q * q, q_square_mem_center q⟩ : centerQ) = 1 := Subtype.ext hs
  rw [he, map_one]
  rfl

/-- An actual central-involution conjugate in Q is not the identity. -/
theorem monsterGeometryQ_point_ne_one (q : Q)
    (h : IsConj generatedCentralInvolution (qIntoGenerated q)) : q ≠ 1 := by
  intro hq
  rw [hq, map_one, isConj_one_left] at h
  apply qCentralInvolution_ne_one
  apply qIntoGenerated_injective
  exact h.trans qIntoGenerated.map_one.symm

/-- The short family is excluded from actual 2B points by its checked Griess trace 4372. -/
theorem monsterGeometryQ_point_not_short (q : Q)
    (h : IsConj generatedCentralInvolution (qIntoGenerated q)) (r : GriessShortIndex) :
    toAdd (qQuotHom q) ≠ leechHyperbolicCoordinates (griessShortClass r) := by
  intro hb
  have hb' : q.base = (griessShortQ r).base := Multiplicative.toAdd.injective hb
  have hshort := monsterGeometryQ_short_trace4372 q r hb'
  have hpoint := monsterGeometryPoint_trace276 (⟨qIntoGenerated q, h⟩ : MonsterGeometryPoint)
  change monsterGeometryTrace (qIntoGenerated q) = 276 at hpoint
  linarith

/-- The actual 2B elements in Q are exactly z and both phases over genuine norm-eight frames. -/
theorem monsterGeometryQ_point_iff (q : Q) :
    IsConj generatedCentralInvolution (qIntoGenerated q) ↔
      q = qCentralInvolution ∨ toAdd (qQuotHom q) ∈ generatedCo1GeometryPoints := by
  constructor
  · intro h
    rcases monsterGeometrySquareQuad_zero_cases _ (monsterGeometryQ_point_singular q h) with
      hz | ⟨r, hr⟩ | hp
    · left
      have hc : q ∈ centerQ := by
        rw [← qQuotHom_ker]
        change qQuotHom q = 1
        exact Multiplicative.toAdd.injective hz
      exact qCentralInvolution_eq_of_mem_center_ne_one q hc
        (monsterGeometryQ_point_ne_one q h)
    · exact (monsterGeometryQ_point_not_short q h r hr).elim
    · exact Or.inr hp
  · rintro (rfl | hp)
    · exact IsConj.refl _
    · exact monsterGeometryFrame_lift_isConj ⟨_, hp⟩ q rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
