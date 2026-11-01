/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine cyclic arm symmetry of the independent source presentation, including its spider. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555Parity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal cyclic permutation of the three source arms. -/
def y555ArmCycle : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Cyclically relabel all three source arms, preserving the central vertex and each level. -/
def y555VertexCycle (v : Y555Vertex) : Y555Vertex :=
  v.map fun p => (y555ArmCycle p.1, p.2)

/-- Cyclic arm relabeling preserves every actual tree edge. -/
theorem y555Adjacent_vertexCycle (u v : Y555Vertex) :
    y555Adjacent (y555VertexCycle u) (y555VertexCycle v) ↔ y555Adjacent u v := by
  revert u v
  decide +kernel

/-- Cyclic arm relabeling sends distinct actual vertices to distinct vertices. -/
theorem y555VertexCycle_injective : Function.Injective y555VertexCycle := by
  decide +kernel

/-- A cyclic rotation of a three-factor word preserves its proved power relation by conjugation. -/
theorem y555_rotate_power {G : Type*} [Group G] (x y z : G) (n : ℕ)
    (h : (x * y * z) ^ n = 1) : (y * z * x) ^ n = 1 := by
  have hm := congrArg (MulAut.conj x⁻¹) h
  rw [map_pow, map_one] at hm
  simpa [MulAut.conj_apply, mul_assoc] using hm

/-- Every literal source relation remains valid after cyclic arm relabeling. -/
theorem y555Cycle_relations_valid (r : FreeGroup Y555Vertex) (hr : r ∈ y555Relations) :
    FreeGroup.lift (fun v => (PresentedGroup.of (y555VertexCycle v) : BimonsterPresentation)) r =
      1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using
      y555_generator_sq (y555VertexCycle v)
  · have h := y555_coxeter_relation (y555VertexCycle u) (y555VertexCycle v)
      (fun heq => huv (y555VertexCycle_injective heq))
    simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, y555Adjacent_vertexCycle] using h
  · let x : BimonsterPresentation :=
      PresentedGroup.of none * PresentedGroup.of (some (0, 0)) * PresentedGroup.of (some (0, 1))
    let y : BimonsterPresentation :=
      PresentedGroup.of none * PresentedGroup.of (some (1, 0)) * PresentedGroup.of (some (1, 1))
    let z : BimonsterPresentation :=
      PresentedGroup.of none * PresentedGroup.of (some (2, 0)) * PresentedGroup.of (some (2, 1))
    have hs : (x * y * z) ^ 10 = 1 := by
      have h := PresentedGroup.one_of_mem (rels := y555Relations)
        (show y555Spider ^ 10 ∈ y555Relations from Or.inr (Or.inr rfl))
      simpa [x, y, z, y555Spider, map_pow, map_mul, PresentedGroup.of, mul_assoc] using h
    have h := y555_rotate_power x y z 10 hs
    simpa [x, y, z, y555Spider, map_pow, map_mul, FreeGroup.lift_apply_of,
      y555VertexCycle, y555ArmCycle, mul_assoc] using h

/-- The cyclic arm symmetry is a genuine endomorphism of the original source group. -/
def y555CycleHom : BimonsterPresentation →* BimonsterPresentation :=
  PresentedGroup.toGroup y555Cycle_relations_valid

/-- This genuine source map sends each original generator to its cyclically relabeled vertex. -/
@[simp] theorem y555CycleHom_generator (v : Y555Vertex) :
    y555CycleHom (PresentedGroup.of v) = PresentedGroup.of (y555VertexCycle v) :=
  PresentedGroup.toGroup.of y555Cycle_relations_valid

/-- Three literal cyclic relabelings return every original source vertex. -/
theorem y555VertexCycle_three (v : Y555Vertex) :
    y555VertexCycle (y555VertexCycle (y555VertexCycle v)) = v := by
  revert v
  decide +kernel

/-- Three applications of the proved source homomorphism are the actual identity. -/
theorem y555CycleHom_three :
    y555CycleHom.comp (y555CycleHom.comp y555CycleHom) = MonoidHom.id BimonsterPresentation := by
  apply PresentedGroup.ext
  intro v
  simp only [MonoidHom.comp_apply, y555CycleHom_generator, y555VertexCycle_three,
    MonoidHom.id_apply]

/-- The cyclic arm symmetry is an actual automorphism, with inverse the second cyclic power. -/
def y555CycleEquiv : BimonsterPresentation ≃* BimonsterPresentation where
  toFun := y555CycleHom
  invFun := fun g => y555CycleHom (y555CycleHom g)
  left_inv g := congrArg (fun f : BimonsterPresentation →* BimonsterPresentation => f g)
    y555CycleHom_three
  right_inv g := congrArg (fun f : BimonsterPresentation →* BimonsterPresentation => f g)
    y555CycleHom_three
  map_mul' := y555CycleHom.map_mul

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
