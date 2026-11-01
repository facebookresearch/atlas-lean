/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The original C431/R cubic certificate interpreted in independent Y444. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444Cycle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431LongestCube

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact original C431 vertices inside the independent thirteen-generator source. -/
def y444C431Vertex : Fin 9 → Y444Vertex :=
  ![none, some (0, 0), some (0, 1), some (0, 2), some (0, 3),
    some (1, 0), some (1, 1), some (1, 2), some (2, 0)]

/-- These nine labels embed to the exact original C431 syntactic labels. -/
theorem y444C431Vertex_embed (i : Fin 9) :
    y444EmbedVertex (y444C431Vertex i) = y431Vertex i := by
  revert i
  decide +kernel

/-- The nine original local vertices remain distinct. -/
theorem y444C431Vertex_injective : Function.Injective y444C431Vertex := by decide +kernel

/-- Exact source F21 evaluates to the genuine second longest word in independent Y444. -/
theorem y444C431F21_source_value :
    FreeGroup.lift (fun v => (PresentedGroup.of (y444C431Vertex v) : Y444Presentation))
      y431F21 = y444LocalF2 := by
  simpa [y431F21, y444C431Vertex, map_pow, map_mul, FreeGroup.lift_apply_of] using
    y444LocalF2_word21.symm

/-- Every original C431/R relation follows in independent Y444 from proved local source facts. -/
theorem y444C431Relations_valid (r : FreeGroup (Fin 9)) (hr : r ∈ y431Relations) :
    FreeGroup.lift (fun v =>
      (PresentedGroup.of (y444C431Vertex v) : Y444Presentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using y444_generator_sq (y444C431Vertex v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, y444Adjacent,
      y444C431Vertex_embed] using
      y444_coxeter_relation (y444C431Vertex u) (y444C431Vertex v)
        (fun h => huv (y444C431Vertex_injective h))
  · simp only [y431R, map_mul, map_inv, y444C431F21_source_value, FreeGroup.lift_apply_of]
    change y444LocalF2 * PresentedGroup.of (some (0, 2)) * y444LocalF2⁻¹ *
      (PresentedGroup.of (some (0, 2)) : Y444Presentation)⁻¹ = 1
    rw [y444LocalF2_commute_d1.eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The genuine original C431/R homomorphism into the independent thirteen-generator source. -/
def y444C431Hom : Y431RPresentation →* Y444Presentation :=
  PresentedGroup.toGroup y444C431Relations_valid

/-- Each original local generator retains its actual independent-Y444 value. -/
@[simp] theorem y444C431Hom_generator (i : Fin 9) :
    y444C431Hom (PresentedGroup.of i) = PresentedGroup.of (y444C431Vertex i) :=
  PresentedGroup.toGroup.of y444C431Relations_valid

/-- The source map agrees with the literal free-word evaluation on every local source word. -/
theorem y444C431Hom_comp_mk :
    y444C431Hom.comp (PresentedGroup.mk y431Relations) =
      FreeGroup.lift (fun v =>
        (PresentedGroup.of (y444C431Vertex v) : Y444Presentation)) := by
  apply FreeGroup.ext_hom
  intro v
  change y444C431Hom (PresentedGroup.of v) =
    FreeGroup.lift (fun v =>
      (PresentedGroup.of (y444C431Vertex v) : Y444Presentation)) (FreeGroup.of v)
  rw [FreeGroup.lift_apply_of]
  exact y444C431Hom_generator v

/-- The exact original F12 source spelling is the first independent-Y444 longest word. -/
theorem y444C431F12_source_value :
    FreeGroup.lift (fun v => (PresentedGroup.of (y444C431Vertex v) : Y444Presentation))
      y431F12 = y444LocalF1 := by
  rw [y444LocalF1_word12]
  simp [y431F12, y444C431Vertex, y444LocalRestrictedWord, y555LocalF1Support12,
    y444C322Vertex, map_pow, map_mul, FreeGroup.lift_apply_of, mul_assoc]

/-- The actual source map sends original F12 to the genuine independent-Y444 longest word. -/
theorem y444C431Hom_F12 :
    y444C431Hom (PresentedGroup.mk y431Relations y431F12) = y444LocalF1 := by
  change (y444C431Hom.comp (PresentedGroup.mk y431Relations)) y431F12 = y444LocalF1
  rw [y444C431Hom_comp_mk]
  exact y444C431F12_source_value

/-- The original C431/R certificate proves the first e-cubic inside independent Y444. -/
theorem y444LocalF1_e1_cube :
    (y444LocalF1 * (PresentedGroup.of (some (0, 3)) : Y444Presentation)) ^ 3 = 1 := by
  have h := congrArg y444C431Hom y431F12_e1_cube
  rw [map_pow, map_mul, map_one, y444C431Hom_F12, y444C431Hom_generator] at h
  exact h

/-- The second e-cubic is a genuine cyclic image inside independent Y444. -/
theorem y444LocalF2_e2_cube :
    (y444LocalF2 * (PresentedGroup.of (some (1, 3)) : Y444Presentation)) ^ 3 = 1 := by
  have h := congrArg y444CycleHom y444LocalF1_e1_cube
  have hv : y444VertexCycle (some (0, 3)) = some (1, 3) := by decide +kernel
  simpa only [map_pow, map_mul, map_one, y444LocalF2, y444CycleHom_generator, hv] using h

/-- The third e-cubic is the next genuine cyclic image inside independent Y444. -/
theorem y444LocalF3_e3_cube :
    (y444LocalF3 * (PresentedGroup.of (some (2, 3)) : Y444Presentation)) ^ 3 = 1 := by
  have h := congrArg y444CycleHom y444LocalF2_e2_cube
  have hv : y444VertexCycle (some (1, 3)) = some (2, 3) := by decide +kernel
  simpa only [map_pow, map_mul, map_one, y444LocalF3, y444CycleHom_generator, hv] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
