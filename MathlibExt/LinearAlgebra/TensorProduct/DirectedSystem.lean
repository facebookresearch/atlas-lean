/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.TensorProduct.DirectLimit.Diagonal

/-!
# Eventual vanishing in directed module and tensor systems

Let R be a commutative ring and G_i a system of R-modules with additive
commutative group structures over a directed preorder with decidable
equality. The R-linear transitions f_ij satisfy identity and composition.

If x ∈ G_i ⊗[R] G_i becomes zero after mapping both factors to lim G,
then (f_ij ⊗ f_ij)(x) is zero at some common later stage j ≥ i.
Likewise, a finite family of elements of G_i whose images vanish in lim G
is killed simultaneously at one later stage. The index set itself need
not be finite, and no injectivity condition on transitions is required.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Module Module.DirectLimit

namespace TensorProduct

variable {R ι : Type*} [CommRing R] [DecidableEq ι]
variable [Preorder ι] [IsDirectedOrder ι]
variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G (f · · ·)]

/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
If x ∈ G_i ⊗[R] G_i maps to zero under of_i ⊗ of_i in
(lim G) ⊗[R] (lim G), then there is j ≥ i with
(f_ij ⊗ f_ij)(x) = 0. Both tensor factors use this same later stage. -/
theorem exists_eq_zero_of_map_to_directLimit_tensor_eq_zero
    {i : ι} (x : G i ⊗[R] G i)
    (hx : TensorProduct.map
      (Module.DirectLimit.of R ι G f i)
      (Module.DirectLimit.of R ι G f i) x = 0) :
    ∃ j : ι, ∃ hij : i ≤ j,
      TensorProduct.map (f i j hij) (f i j hij) x = 0 := by
  exact exists_eq_zero_of_map_to_directLimit_diagonal_eq_zero f f x hx

end TensorProduct

namespace Module.DirectLimit

variable {R ι : Type*} [CommRing R] [DecidableEq ι]
variable [Preorder ι] [IsDirectedOrder ι]
variable {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable [DirectedSystem G (f · · ·)]

/-- Let R be a commutative ring and G_i a directed system of R-modules
with additive commutative group structures, indexed by a directed preorder
with decidable equality. Its transitions f_ij are R-linear and satisfy
the identity and composition laws.
For a finite index type I and a family x_a ∈ G_i whose images
of_i(x_a) vanish in lim G, there is a single j ≥ i such that
f_ij(x_a) = 0 for every a ∈ I. An empty family is allowed. -/
theorem of.zero_exact_finite_family
    {I : Type*} [Finite I] {i : ι} (x : I → G i)
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
