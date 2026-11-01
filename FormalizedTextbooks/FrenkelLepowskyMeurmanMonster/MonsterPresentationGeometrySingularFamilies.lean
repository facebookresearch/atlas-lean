/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual zero, short-class and Conway-frame families give distinct singular binary vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine Conway frame coordinates are singular for the actual extraspecial square form. -/
theorem monsterGeometryFrame_squareQuad_zero (p : MonsterCo1GeometryPoint) :
    squareQuad p.val = 0 := by
  obtain ⟨x, ⟨e, he⟩, hx⟩ := p.property
  change leechReduction (leechIntegralAction e (leechCoordinateFrameLattice 0)) = x at he
  rw [← hx, ← he, ← leechHyperbolicCoordinates_halfNorm, leechIntegralAction_squareSum]
  change ((leechSquareSum (leechCoordinateFrameVector 0) / 16 : ℤ) : ZMod 2) = 0
  rw [leechCoordinateFrameVector_square]
  decide

/-- The actual short binary coordinates are nonzero. -/
theorem monsterGeometryShort_binary_ne_zero (r : GriessShortIndex) :
    leechHyperbolicCoordinates (griessShortClass r) ≠ 0 := by
  intro h
  apply griessShortClass_ne_zero r
  apply leechHyperbolicCoordinates.injective
  simpa only [map_zero] using h

/-- The three actual geometric families used in the singular-vector count. -/
abbrev MonsterGeometrySingularFamily := PUnit.{1} ⊕ (GriessShortIndex ⊕ MonsterCo1GeometryPoint)

/-- Actual binary values for zero, preferred short-vector classes and genuine Conway frames. -/
def monsterGeometrySingularFamilyValue : MonsterGeometrySingularFamily → (Fin 24 → ZMod 2)
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl r) => leechHyperbolicCoordinates (griessShortClass r)
  | Sum.inr (Sum.inr p) => p.val

/-- Every member of the three actual families is singular for the literal square form. -/
theorem monsterGeometrySingularFamilyValue_singular (x : MonsterGeometrySingularFamily) :
    squareQuad (monsterGeometrySingularFamilyValue x) = 0 := by
  rcases x with x | (r | p)
  · exact squareQuad.map_zero
  · exact griessShortQ_squareQuad r
  · exact monsterGeometryFrame_squareQuad_zero p

/-- The three geometric families have distinct actual binary values. -/
theorem monsterGeometrySingularFamilyValue_injective :
    Function.Injective monsterGeometrySingularFamilyValue := by
  intro x y h
  rcases x with x | (r | p) <;> rcases y with y | (s | q)
  · exact congrArg Sum.inl (Subsingleton.elim x y)
  · exact (monsterGeometryShort_binary_ne_zero s h.symm).elim
  · exact (monsterCo1GeometryPoint_ne_zero q h.symm).elim
  · exact (monsterGeometryShort_binary_ne_zero r h).elim
  · exact congrArg (Sum.inr ∘ Sum.inl)
      (griessShortClass_injective (leechHyperbolicCoordinates.injective h))
  · have hm := generatedCo1GeometryPoints_short_not_mem r
    apply False.elim
    apply hm
    change leechHyperbolicCoordinates (griessShortClass r) = q.val at h
    rw [h]
    exact q.property
  · exact (monsterCo1GeometryPoint_ne_zero p h).elim
  · have hm := generatedCo1GeometryPoints_short_not_mem s
    apply False.elim
    apply hm
    change p.val = leechHyperbolicCoordinates (griessShortClass s) at h
    rw [← h]
    exact p.property
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext h)

/-- The actual three-family population equals the exact hyperbolic singular-vector count. -/
theorem monsterGeometrySingularFamily_card : Nat.card MonsterGeometrySingularFamily = 8390656 := by
  rw [Nat.card_sum, Nat.card_sum, monsterCo1GeometryPoint_card]
  rw [Nat.card_eq_fintype_card (α := GriessShortIndex), griessShortIndex_card]
  simp only [Nat.card_eq_fintype_card, Fintype.card_punit]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
