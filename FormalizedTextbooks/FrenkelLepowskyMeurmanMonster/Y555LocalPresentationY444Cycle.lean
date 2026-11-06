/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine cyclic source symmetry and rotated longest words in independent Y444. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationY444Local
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555ArmRotation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Cyclically permute the three independent source arms, retaining every level. -/
def y444VertexCycle (v : Y444Vertex) : Y444Vertex :=
  v.map fun p => (y555ArmCycle p.1, p.2)

/-- Cyclic relabeling agrees with the actual original syntactic inclusion. -/
theorem y444EmbedVertex_cycle (v : Y444Vertex) :
    y444EmbedVertex (y444VertexCycle v) = y555VertexCycle (y444EmbedVertex v) := by
  revert v
  decide +kernel

/-- Every independent source edge is preserved by the literal cyclic relabeling. -/
theorem y444Adjacent_vertexCycle (u v : Y444Vertex) :
    y444Adjacent (y444VertexCycle u) (y444VertexCycle v) ↔ y444Adjacent u v := by
  unfold y444Adjacent
  rw [y444EmbedVertex_cycle, y444EmbedVertex_cycle, y555Adjacent_vertexCycle]

/-- The cyclic source relabeling preserves distinct vertices. -/
theorem y444VertexCycle_injective : Function.Injective y444VertexCycle := by decide +kernel

/-- Three literal cyclic relabelings return every independent source vertex. -/
theorem y444VertexCycle_three (v : Y444Vertex) :
    y444VertexCycle (y444VertexCycle (y444VertexCycle v)) = v := by
  revert v
  decide +kernel

/-- Every independent source relation is valid after literal cyclic arm relabeling. -/
theorem y444Cycle_relations_valid (r : FreeGroup Y444Vertex) (hr : r ∈ y444Relations) :
    FreeGroup.lift (fun v =>
      (PresentedGroup.of (y444VertexCycle v) : Y444Presentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using
      y444_generator_sq (y444VertexCycle v)
  · have h := y444_coxeter_relation (y444VertexCycle u) (y444VertexCycle v)
      (fun heq => huv (y444VertexCycle_injective heq))
    simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, y444Adjacent_vertexCycle] using h
  · let x : Y444Presentation :=
      PresentedGroup.of none * PresentedGroup.of (some (0, 0)) * PresentedGroup.of (some (0, 1))
    let y : Y444Presentation :=
      PresentedGroup.of none * PresentedGroup.of (some (1, 0)) * PresentedGroup.of (some (1, 1))
    let z : Y444Presentation :=
      PresentedGroup.of none * PresentedGroup.of (some (2, 0)) * PresentedGroup.of (some (2, 1))
    have hs : (x * y * z) ^ 10 = 1 := by
      have h := PresentedGroup.one_of_mem (rels := y444Relations)
        (show y444Spider ^ 10 ∈ y444Relations from Or.inr (Or.inr rfl))
      simpa [x, y, z, y444Spider, map_pow, map_mul, PresentedGroup.of, mul_assoc] using h
    have h := y555_rotate_power x y z 10 hs
    simpa [x, y, z, y444Spider, map_pow, map_mul, FreeGroup.lift_apply_of,
      y444VertexCycle, y555ArmCycle, mul_assoc] using h

/-- Cyclic arm symmetry is a genuine source endomorphism of independent Y444. -/
def y444CycleHom : Y444Presentation →* Y444Presentation :=
  PresentedGroup.toGroup y444Cycle_relations_valid

/-- Every source generator has exactly its literal cyclically relabeled image. -/
@[simp] theorem y444CycleHom_generator (v : Y444Vertex) :
    y444CycleHom (PresentedGroup.of v) = PresentedGroup.of (y444VertexCycle v) :=
  PresentedGroup.toGroup.of y444Cycle_relations_valid

/-- The actual second corrected longest word is the genuine cyclic image of the first. -/
def y444LocalF2 : Y444Presentation := y444CycleHom y444LocalF1

/-- The actual third corrected longest word is the next genuine cyclic image. -/
def y444LocalF3 : Y444Presentation := y444CycleHom y444LocalF2

/-- The exact source F21 spelling of the second corrected longest word. -/
theorem y444LocalF2_word21 : y444LocalF2 =
    ((PresentedGroup.of none : Y444Presentation) * PresentedGroup.of (some (1, 0)) *
      PresentedGroup.of (some (0, 0)) * PresentedGroup.of (some (2, 0)) *
      PresentedGroup.of (some (1, 1)) * PresentedGroup.of (some (0, 1)) *
      PresentedGroup.of (some (1, 2))) ^ 9 := by
  rw [y444LocalF2, y444LocalF1_word13]
  have hb := y444Source_generator_commute (some (2, 0)) (some (0, 0)) (by decide)
  simp [y444LocalRestrictedWord, y555LocalF1Support13, y444CycleHom_generator,
    y444C322Vertex, y444VertexCycle, y555ArmCycle, map_pow, mul_assoc, hb.left_comm]

/-- The actual second corrected longest word commutes with the first-arm d-generator. -/
theorem y444LocalF2_commute_d1 :
    Commute y444LocalF2 (PresentedGroup.of (some (0, 2))) := by
  have h := (y444LocalF1_commute (some (2, 2)) (by decide)).map y444CycleHom
  have hv : y444VertexCycle (some (2, 2)) = some (0, 2) := by decide +kernel
  simpa only [y444LocalF2, y444CycleHom_generator, hv] using h

/-- The second corrected longest word is an actual source involution. -/
theorem y444LocalF2_square : y444LocalF2 * y444LocalF2 = 1 := by
  simpa only [y444LocalF2, map_mul, map_one] using
    congrArg y444CycleHom y444LocalF1_square

/-- The third corrected longest word is an actual source involution. -/
theorem y444LocalF3_square : y444LocalF3 * y444LocalF3 = 1 := by
  simpa only [y444LocalF3, map_mul, map_one] using
    congrArg y444CycleHom y444LocalF2_square

/-- The second corrected longest word commutes with every source vertex except e2. -/
theorem y444LocalF2_commute (v : Y444Vertex) (hv : v ≠ some (1, 3)) :
    Commute y444LocalF2 (PresentedGroup.of v) := by
  let u := y444VertexCycle (y444VertexCycle v)
  have hu : u ≠ some (0, 3) := by
    intro he
    have h := congrArg y444VertexCycle he
    have hc : y444VertexCycle (some (0, 3)) = some (1, 3) := by decide +kernel
    exact hv (by simpa only [u, y444VertexCycle_three, hc] using h)
  have h := (y444LocalF1_commute u hu).map y444CycleHom
  simpa only [u, y444LocalF2, y444CycleHom_generator, y444VertexCycle_three] using h

/-- The third corrected longest word commutes with every source vertex except e3. -/
theorem y444LocalF3_commute (v : Y444Vertex) (hv : v ≠ some (2, 3)) :
    Commute y444LocalF3 (PresentedGroup.of v) := by
  let u := y444VertexCycle (y444VertexCycle v)
  have hu : u ≠ some (1, 3) := by
    intro he
    have h := congrArg y444VertexCycle he
    have hc : y444VertexCycle (some (1, 3)) = some (2, 3) := by decide +kernel
    exact hv (by simpa only [u, y444VertexCycle_three, hc] using h)
  have h := (y444LocalF2_commute u hu).map y444CycleHom
  simpa only [u, y444LocalF3, y444CycleHom_generator, y444VertexCycle_three] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
