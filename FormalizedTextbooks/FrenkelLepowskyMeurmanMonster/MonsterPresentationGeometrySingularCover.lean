/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact exhaustion of the actual hyperbolic singular vectors by genuine Leech families. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometrySingularCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometrySingularFamilies

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine geometric families, mapped into the actual singular-vector subtype. -/
def monsterGeometrySingularFamilyInto : MonsterGeometrySingularFamily →
    {v : Fin 24 → ZMod 2 // squareQuad v = 0} :=
  fun x => ⟨monsterGeometrySingularFamilyValue x, monsterGeometrySingularFamilyValue_singular x⟩

/-- Exact actual family enumeration follows from checked injectivity and matching finite counts. -/
theorem monsterGeometrySingularFamilyInto_bijective :
    Function.Bijective monsterGeometrySingularFamilyInto := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro x y h
    exact monsterGeometrySingularFamilyValue_injective (congrArg Subtype.val h)
  · rw [monsterGeometrySingularFamily_card, monsterGeometrySquareQuad_singular_card]

/-- The actual singular-vector set is exactly zero, actual short classes and actual frame points. -/
def monsterGeometrySingularFamilyEquiv : MonsterGeometrySingularFamily ≃
    {v : Fin 24 → ZMod 2 // squareQuad v = 0} :=
  Equiv.ofBijective monsterGeometrySingularFamilyInto monsterGeometrySingularFamilyInto_bijective

/-- Every actual singular vector belongs to one of the three genuine geometric families. -/
theorem monsterGeometrySquareQuad_zero_cases (v : Fin 24 → ZMod 2) (hv : squareQuad v = 0) :
    v = 0 ∨ (∃ r : GriessShortIndex, v = leechHyperbolicCoordinates (griessShortClass r)) ∨
      v ∈ generatedCo1GeometryPoints := by
  obtain ⟨x, hx⟩ := monsterGeometrySingularFamilyInto_bijective.surjective ⟨v, hv⟩
  have he := congrArg Subtype.val hx
  rcases x with x | (r | p)
  · exact Or.inl he.symm
  · exact Or.inr (Or.inl ⟨r, he.symm⟩)
  · apply Or.inr ∘ Or.inr
    change p.val = v at he
    rw [← he]
    exact p.property

/-- A binary vector is singular exactly when it is zero, a genuine short class or a frame point. -/
theorem monsterGeometrySquareQuad_zero_iff (v : Fin 24 → ZMod 2) :
    squareQuad v = 0 ↔
      v = 0 ∨ (∃ r : GriessShortIndex, v = leechHyperbolicCoordinates (griessShortClass r)) ∨
        v ∈ generatedCo1GeometryPoints := by
  constructor
  · exact monsterGeometrySquareQuad_zero_cases v
  · rintro (rfl | ⟨r, rfl⟩ | hv)
    · exact squareQuad.map_zero
    · exact griessShortQ_squareQuad r
    · exact monsterGeometryFrame_squareQuad_zero ⟨v, hv⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
