/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original C422/S/Q source relations and their actual independent-Y444 interpretation.
Source: L.H. Soicher, Cambridge thesis (1985), printed pp.51–53,
DOI 10.17863/CAM.110463. The local Q cubic is proved inside Y444 by the C431/R certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444C431

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact nine C422 vertices a,b1,c1,d1,e1,b2,c2,b3,c3. -/
def y422Vertex : Fin 9 → Y444Vertex :=
  ![none, some (0, 0), some (0, 1), some (0, 2), some (0, 3),
    some (1, 0), some (1, 1), some (2, 0), some (2, 1)]

/-- All nine original local source vertices are distinct. -/
theorem y422Vertex_injective : Function.Injective y422Vertex := by decide +kernel

/-- The exact corrected first longest spelling in the original nine-letter source alphabet. -/
def y422F12 : FreeGroup (Fin 9) :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 5 * FreeGroup.of 7 *
    FreeGroup.of 2 * FreeGroup.of 6 * FreeGroup.of 3) ^ 9

/-- The literal original three-arm spider in this local source alphabet. -/
def y422Spider : FreeGroup (Fin 9) :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 *
    FreeGroup.of 0 * FreeGroup.of 5 * FreeGroup.of 6 *
      FreeGroup.of 0 * FreeGroup.of 7 * FreeGroup.of 8

/-- The published Q cubic on the corrected first longest word and e1. -/
def y422Cubic : FreeGroup (Fin 9) := (y422F12 * FreeGroup.of 4) ^ 3

/-- Exact original Coxeter relations, original spider10, and the source Q relation. -/
def y422Relations : Set (FreeGroup (Fin 9)) :=
  {w | (∃ v, w = FreeGroup.of v ^ 2) ∨
    (∃ u v, u ≠ v ∧ w = (FreeGroup.of u * FreeGroup.of v) ^
      (if y444Adjacent (y422Vertex u) (y422Vertex v) then 3 else 2 : ℕ)) ∨
        w = y422Spider ^ 10 ∨ w = y422Cubic}

/-- The independently presented original C422/S/Q quotient. -/
abbrev Y422Presentation := PresentedGroup y422Relations

/-- Every original source generator satisfies its exact defining square. -/
theorem y422_generator_sq (v : Fin 9) : (PresentedGroup.of v : Y422Presentation) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y422Relations)
    (show FreeGroup.of v ^ 2 ∈ y422Relations from Or.inl ⟨v, rfl⟩)
  simpa only [map_pow, PresentedGroup.of] using h

/-- Every original source pair satisfies its exact defining Coxeter relation. -/
theorem y422_coxeter_relation (u v : Fin 9) (huv : u ≠ v) :
    ((PresentedGroup.of u : Y422Presentation) * PresentedGroup.of v) ^
      (if y444Adjacent (y422Vertex u) (y422Vertex v) then 3 else 2 : ℕ) = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y422Relations)
    (show (FreeGroup.of u * FreeGroup.of v) ^
      (if y444Adjacent (y422Vertex u) (y422Vertex v) then 3 else 2 : ℕ) ∈ y422Relations from
        Or.inr (Or.inl ⟨u, v, huv, rfl⟩))
  simpa only [map_pow, map_mul, PresentedGroup.of] using h

/-- The exact local longest word evaluates to the actual independent-Y444 first longest word. -/
theorem y422F12_source_value :
    FreeGroup.lift (fun v => (PresentedGroup.of (y422Vertex v) : Y444Presentation))
      y422F12 = y444LocalF1 := by
  rw [y444LocalF1_word12]
  simp [y422F12, y422Vertex, y444LocalRestrictedWord, y555LocalF1Support12,
    y444C322Vertex, map_pow, map_mul, FreeGroup.lift_apply_of, mul_assoc]

/-- All original local relations hold in independent Y444, including its proved Q cubic. -/
theorem y422Relations_valid_Y444 (r : FreeGroup (Fin 9)) (hr : r ∈ y422Relations) :
    FreeGroup.lift (fun v => (PresentedGroup.of (y422Vertex v) : Y444Presentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y444_generator_sq (y422Vertex v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of] using
      y444_coxeter_relation (y422Vertex u) (y422Vertex v)
        (fun h => huv (y422Vertex_injective h))
  · have h := PresentedGroup.one_of_mem (rels := y444Relations)
      (show y444Spider ^ 10 ∈ y444Relations from Or.inr (Or.inr rfl))
    simpa [y422Spider, y444Spider, y422Vertex, map_pow, map_mul,
      FreeGroup.lift_apply_of, PresentedGroup.of, mul_assoc] using h
  · rw [y422Cubic, map_pow, map_mul, y422F12_source_value, FreeGroup.lift_apply_of]
    exact y444LocalF1_e1_cube

/-- The actual original local-source homomorphism into independent Y444. -/
def y422IntoY444 : Y422Presentation →* Y444Presentation :=
  PresentedGroup.toGroup y422Relations_valid_Y444

/-- Every original local generator retains its exact independent-Y444 value. -/
@[simp] theorem y422IntoY444_generator (v : Fin 9) :
    y422IntoY444 (PresentedGroup.of v) = PresentedGroup.of (y422Vertex v) :=
  PresentedGroup.toGroup.of y422Relations_valid_Y444

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
