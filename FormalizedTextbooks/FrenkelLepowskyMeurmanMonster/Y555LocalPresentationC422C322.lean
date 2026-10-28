/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine original C322 parabolic homomorphism and finite-image bound inside C422/S/Q. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Faithfulness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact original C322 letter inclusion, omitting only the source e1 letter. -/
def y422C322Letter : Fin 8 → Fin 9 := ![0, 1, 2, 3, 5, 6, 7, 8]

/-- The source letter inclusion preserves the original independent syntactic labels. -/
theorem y422C322Letter_vertex (i : Fin 8) :
    y422Vertex (y422C322Letter i) = y444C322Vertex i := by
  revert i
  decide +kernel

/-- These eight source letters remain distinct. -/
theorem y422C322Letter_injective : Function.Injective y422C322Letter := by decide +kernel

/-- Every original C322 relator is an actual original C422/S/Q consequence. -/
theorem y422C322Relations_valid (r : FreeGroup (Fin 8)) (hr : r ∈ y322Relations) :
    FreeGroup.lift (fun i => (PresentedGroup.of (y422C322Letter i) : Y422Presentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y422_generator_sq (y422C322Letter v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, y422C322Letter_vertex,
      y444Adjacent, y444C322Vertex_embed] using
      y422_coxeter_relation (y422C322Letter u) (y422C322Letter v)
        (fun h => huv (y422C322Letter_injective h))
  · have h := PresentedGroup.one_of_mem (rels := y422Relations)
      (show y422Spider ^ 10 ∈ y422Relations from Or.inr (Or.inr (Or.inl rfl)))
    simpa [y322Spider, y422Spider, y422C322Letter, map_pow, map_mul,
      FreeGroup.lift_apply_of, PresentedGroup.of, mul_assoc] using h

/-- The genuine original C322 parabolic homomorphism into original C422/S/Q. -/
def y422C322Hom : Y322Presentation →* Y422Presentation :=
  PresentedGroup.toGroup y422C322Relations_valid

/-- Every original C322 generator retains its exact original C422 letter value. -/
@[simp] theorem y422C322Hom_generator (i : Fin 8) :
    y422C322Hom (PresentedGroup.of i) = PresentedGroup.of (y422C322Letter i) :=
  PresentedGroup.toGroup.of y422C322Relations_valid

/-- The actual image parabolic used by the C422 source coset certificate. -/
def y422C322Subgroup : Subgroup Y422Presentation := y422C322Hom.range

/-- Each of the eight supplied coset-subgroup letters lies in this actual image parabolic. -/
theorem y422C322Letter_mem (i : Fin 8) :
    (PresentedGroup.of (y422C322Letter i) : Y422Presentation) ∈ y422C322Subgroup := by
  exact ⟨PresentedGroup.of i, y422C322Hom_generator i⟩

/-- The actual image parabolic is finite and bounded by the proved original C322 order. -/
theorem y422C322Subgroup_finite_card :
    Finite y422C322Subgroup ∧ Nat.card y422C322Subgroup ≤ 9170703360 := by
  have : Finite Y322Presentation := y322Presentation_finite_card.1
  let f : Y322Presentation → y422C322Subgroup := fun x => ⟨y422C322Hom x, ⟨x, rfl⟩⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, x, rfl⟩
    exact ⟨x, rfl⟩
  refine ⟨Finite.of_surjective f hsurj, ?_⟩
  have h := Nat.card_le_card_of_surjective f hsurj
  rwa [y322Orthogonal3_exact_order_faithful.1] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
