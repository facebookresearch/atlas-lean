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
# Eventual vanishing in directed tensor systems

If a tensor at one stage maps to zero after both factors are included in a
direct limit, then it is already zero after some common later transition.
The proof uses the earned simultaneous tensor/direct-limit equivalence and
the native eventual-zero theorem for the concrete directed limit.
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

/-- A stagewise tensor which vanishes after both factors map to the direct
limit vanishes after one common enlargement. -/
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

/-- A finite family from one stage which vanishes in a module direct limit
is killed simultaneously at one common later stage. -/
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
