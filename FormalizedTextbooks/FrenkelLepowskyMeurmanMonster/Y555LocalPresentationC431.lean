/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact C431/R local source presentation and its genuine independent-Y555 map.
Source: L.H. Soicher, Cambridge thesis (1985), printed pp.51–53,
DOI 10.17863/CAM.110463. Page53 specifies R=[F21,D1]; the p52 formula is corrected by hand.
No local cubic or finite-order recognition is assumed. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationLongestRotation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact C431 vertices a,b1,c1,d1,e1,b2,c2,d2,b3 in independent Y555. -/
def y431Vertex : Fin 9 → Y555Vertex :=
  ![none, some (0, 0), some (0, 1), some (0, 2), some (0, 3),
    some (1, 0), some (1, 1), some (1, 2), some (2, 0)]

/-- The nine original local vertices are distinct. -/
theorem y431Vertex_injective : Function.Injective y431Vertex := by decide +kernel

/-- The exact corrected seven-letter F21 spelling from the original local source. -/
def y431F21 : FreeGroup (Fin 9) :=
  (FreeGroup.of 0 * FreeGroup.of 5 * FreeGroup.of 1 * FreeGroup.of 8 *
    FreeGroup.of 6 * FreeGroup.of 2 * FreeGroup.of 7) ^ 9

/-- The source R relation is literally the commutator of F21 with d1. -/
def y431R : FreeGroup (Fin 9) :=
  y431F21 * FreeGroup.of 3 * y431F21⁻¹ * (FreeGroup.of 3)⁻¹

/-- All original C431 Coxeter relations together with the specified R relation. -/
def y431Relations : Set (FreeGroup (Fin 9)) :=
  {w | (∃ v, w = FreeGroup.of v ^ 2) ∨
    (∃ u v, u ≠ v ∧ w = (FreeGroup.of u * FreeGroup.of v) ^
      (if y555Adjacent (y431Vertex u) (y431Vertex v) then 3 else 2 : ℕ)) ∨ w = y431R}

/-- The independent original C431/R quotient, before any further local recognition. -/
abbrev Y431RPresentation := PresentedGroup y431Relations

/-- Evaluation of the exact source F21 gives the proved actual second-arm longest word. -/
theorem y431F21_source_value :
    FreeGroup.lift (fun v => (PresentedGroup.of (y431Vertex v) : BimonsterPresentation))
      y431F21 = y555LocalF2 := by
  simpa [y431F21, y431Vertex, map_pow, map_mul, FreeGroup.lift_apply_of] using
    y555LocalF2_word21.symm

/-- Every original C431/R relation already holds in the independent Y555 group. -/
theorem y431Relations_valid (r : FreeGroup (Fin 9)) (hr : r ∈ y431Relations) :
    FreeGroup.lift (fun v => (PresentedGroup.of (y431Vertex v) : BimonsterPresentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y555_generator_sq (y431Vertex v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of] using
      y555_coxeter_relation (y431Vertex u) (y431Vertex v)
        (fun h => huv (y431Vertex_injective h))
  · simp only [y431R, map_mul, map_inv, y431F21_source_value, FreeGroup.lift_apply_of]
    change y555LocalF2 * PresentedGroup.of (some (0, 2)) * y555LocalF2⁻¹ *
      (PresentedGroup.of (some (0, 2)) : BimonsterPresentation)⁻¹ = 1
    rw [y555LocalF2_commute_d1.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The genuine local-source homomorphism into the original independent Y555 group. -/
def y431IntoY555 : Y431RPresentation →* BimonsterPresentation :=
  PresentedGroup.toGroup y431Relations_valid

/-- This source homomorphism preserves every specified original generator. -/
@[simp] theorem y431IntoY555_generator (v : Fin 9) :
    y431IntoY555 (PresentedGroup.of v) = PresentedGroup.of (y431Vertex v) :=
  PresentedGroup.toGroup.of y431Relations_valid

/-- The exact first-arm longest word in this original local alphabet. -/
def y431F12 : FreeGroup (Fin 9) :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 5 * FreeGroup.of 8 *
    FreeGroup.of 2 * FreeGroup.of 6 * FreeGroup.of 3) ^ 9

/-- The concrete original-source cubic word required for the next redundancy step. -/
def y431LongestCube : FreeGroup (Fin 9) := (y431F12 * FreeGroup.of 4) ^ 3

/-- The exact first-arm source word has its already proved independent-Y555 value. -/
theorem y431F12_source_value :
    FreeGroup.lift (fun v => (PresentedGroup.of (y431Vertex v) : BimonsterPresentation))
      y431F12 = y555LocalF1 := by
  rw [y555LocalF1_word12]
  simp [y431F12, y431Vertex, y555LocalRestrictedWord, y555LocalF1Support12,
    y322Vertex, map_pow, map_mul, FreeGroup.lift_apply_of, mul_assoc]

/-- The local target maps to the literal longest/e1 cube; the cubic identity is still open. -/
theorem y431LongestCube_source_value :
    FreeGroup.lift (fun v => (PresentedGroup.of (y431Vertex v) : BimonsterPresentation))
      y431LongestCube = (y555LocalF1 * PresentedGroup.of (some (0, 3))) ^ 3 := by
  simp only [y431LongestCube, map_pow, map_mul, y431F12_source_value,
    FreeGroup.lift_apply_of]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
