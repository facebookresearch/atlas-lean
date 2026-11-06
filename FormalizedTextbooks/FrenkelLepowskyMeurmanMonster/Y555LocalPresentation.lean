/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact C322 local presentation maps into the independent Y555 presentation.
Source: L.H. Soicher, Presentations of Some Finite Groups, Cambridge PhD thesis (1985),
Chapter Y, printed pp.49–50, DOI 10.17863/CAM.110463. No enumeration is assumed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555Parity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source C322 vertices in order a,b1,c1,d1,b2,c2,b3,c3, inside the actual Y555 tree. -/
def y322Vertex : Fin 8 → Y555Vertex :=
  ![none, some (0, 0), some (0, 1), some (0, 2),
    some (1, 0), some (1, 1), some (2, 0), some (2, 1)]

/-- The eight source vertices are distinct. -/
theorem y322Vertex_injective : Function.Injective y322Vertex := by
  decide +kernel

/-- The source spider uses the same three two-step branches in this restricted diagram. -/
def y322Spider : FreeGroup (Fin 8) :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 2 *
    FreeGroup.of 0 * FreeGroup.of 4 * FreeGroup.of 5 *
      FreeGroup.of 0 * FreeGroup.of 6 * FreeGroup.of 7

/-- Complete local Coxeter relators and the tenth spider power, with inherited adjacency. -/
def y322Relations : Set (FreeGroup (Fin 8)) :=
  {w | (∃ v, w = FreeGroup.of v ^ 2) ∨
    (∃ u v, u ≠ v ∧ w = (FreeGroup.of u * FreeGroup.of v) ^
      (if y555Adjacent (y322Vertex u) (y322Vertex v) then 3 else 2 : ℕ)) ∨
      w = y322Spider ^ 10}

/-- The independently presented source local quotient, before any finite-order recognition. -/
abbrev Y322Presentation := PresentedGroup y322Relations

/-- Every local relator is a defining relation in the existing independent Y555 quotient. -/
theorem y322Relations_valid (r : FreeGroup (Fin 8)) (hr : r ∈ y322Relations) :
    FreeGroup.lift (fun v => (PresentedGroup.of (y322Vertex v) : BimonsterPresentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y555_generator_sq (y322Vertex v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of] using
      y555_coxeter_relation (y322Vertex u) (y322Vertex v)
        (fun h => huv (y322Vertex_injective h))
  · have hs := PresentedGroup.one_of_mem (rels := y555Relations)
      (show y555Spider ^ 10 ∈ y555Relations from Or.inr (Or.inr rfl))
    simpa [y322Spider, y555Spider, PresentedGroup.of, y322Vertex] using hs

/-- Canonical local presentation map into the independently defined bimonster presentation. -/
def y322IntoY555 : Y322Presentation →* BimonsterPresentation :=
  PresentedGroup.toGroup y322Relations_valid

/-- This map sends every local generator to its actual restricted Y555 vertex. -/
@[simp] theorem y322IntoY555_generator (v : Fin 8) :
    y322IntoY555 (PresentedGroup.of v) = PresentedGroup.of (y322Vertex v) :=
  PresentedGroup.toGroup.of y322Relations_valid

/-- The first E7 longest word, with the source's necessary c2 before d1. -/
def y322E7Word12 : FreeGroup (Fin 8) :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 4 * FreeGroup.of 6 *
    FreeGroup.of 2 * FreeGroup.of 5 * FreeGroup.of 3) ^ 9

/-- The second E7 longest word, with c3 before d1. -/
def y322E7Word13 : FreeGroup (Fin 8) :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 4 * FreeGroup.of 6 *
    FreeGroup.of 2 * FreeGroup.of 7 * FreeGroup.of 3) ^ 9

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
