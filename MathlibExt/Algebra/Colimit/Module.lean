/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Data.Fintype.EquivFin

/-!
# Simultaneous eventual vanishing of a finite family

For a directed system of semimodules over any semiring, a finite family represented at one
stage and vanishing in the direct limit is killed at one common later stage. Scalar, carrier,
index and finite-family universes are independent. An empty family uses the original stage.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Module Module.DirectLimit

universe uR uI uG uF

namespace Module.DirectLimit

variable {R : Type uR} {ι : Type uI} [Semiring R] [DecidableEq ι]
variable [Preorder ι] [IsDirectedOrder ι]
variable {G : ι → Type uG} [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G (f · · ·)]

/-- Let R be any semiring and G_i a directed system of R-modules
with additive commutative monoid structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
For a finite index type I and a family x_a ∈ G_i whose images
of_i(x_a) vanish in lim G, there is a single j ≥ i such that
f_ij(x_a) = 0 for every a ∈ I. An empty family is allowed. -/
theorem of.zero_exact_finite_family
    {I : Type uF} [Finite I] {i : ι} (x : I → G i)
    (hx : ∀ a, Module.DirectLimit.of R ι G f i (x a) = 0) :
    ∃ j : ι, ∃ hij : i ≤ j, ∀ a, f i j hij (x a) = 0 := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have aux : ∀ s : Finset I,
      ∃ j : ι, ∃ hij : i ≤ j, ∀ a ∈ s, f i j hij (x a) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨i, le_rfl, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨j, hij, hsj⟩ := ih
        let xaJ := f i j hij (x a)
        have hxaJ : Module.DirectLimit.of R ι G f j xaJ = 0 := by
          change Module.DirectLimit.of R ι G f j (f i j hij (x a)) = 0
          rw [Module.DirectLimit.of_f]
          exact hx a
        obtain ⟨k, hjk, hxaK⟩ := Module.DirectLimit.of.zero_exact hxaJ
        refine ⟨k, hij.trans hjk, ?_⟩
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hbs
        · rw [← DirectedSystem.map_map' f hij hjk]
          exact hxaK
        · rw [← DirectedSystem.map_map' f hij hjk,
            hsj b hbs, map_zero]
  obtain ⟨j, hij, hzero⟩ := aux Finset.univ
  exact ⟨j, hij, fun a => hzero a (Finset.mem_univ a)⟩

end Module.DirectLimit
