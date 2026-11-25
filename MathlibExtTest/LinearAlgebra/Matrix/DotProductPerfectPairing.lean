/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.DotProductPerfectPairing

@[expose] public section

/-- Source consumer with the original binders. -/
private theorem exactSource {ι : Type*} [Fintype ι]
    {L : Type*} [AddCommGroup L] [Module ℤ L]
    (B E : Submodule ℤ (ι → ℤ))
    (hB : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ B → v ∈ B)
    (hE : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → n • v ∈ E → v ∈ E)
    (hBE : ∀ b ∈ B, ∀ e ∈ E, b ⬝ᵥ e = 0)
    (f X : L →ₗ[ℤ] (ι → ℤ))
    (hf : ∀ y, ∀ e ∈ E, f y ⬝ᵥ e = 0) (hX : ∀ x, ∀ b ∈ B, X x ⬝ᵥ b = 0)
    (hfB : ∀ y, f y ∈ B → y = 0) (hXE : ∀ x, X x ∈ E → x = 0)
    (hZ : ∀ v : ι → ℤ, (∀ e ∈ E, v ⬝ᵥ e = 0) → ∃ y, v - f y ∈ B)
    (hsat : ∀ (n : ℤ) (v : ι → ℤ), n ≠ 0 → (∃ x, n • v - X x ∈ E) → ∃ x, v - X x ∈ E) :
    ∃ p : L →ₗ[ℤ] L →ₗ[ℤ] ℤ, (∀ x y, p x y = X x ⬝ᵥ f y) ∧ p.IsPerfPair :=
  Submodule.exists_isPerfPair_dotProduct_of_saturated B E hB hE hBE f X hf hX hfB hXE hZ hsat

/-- With `B = E = ⊥` and `f = X = id` on `L = Fin 2 → ℤ`, the dot product itself is a
perfect pairing. -/
example : ∃ p : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ,
    (∀ x y, p x y = x ⬝ᵥ y) ∧ p.IsPerfPair := by
  refine exactSource (L := Fin 2 → ℤ) ⊥ ⊥ ?_ ?_ ?_ LinearMap.id LinearMap.id ?_ ?_ ?_ ?_ ?_ ?_
  · intro n v hn h
    rw [Submodule.mem_bot] at h ⊢
    exact (smul_eq_zero.mp h).resolve_left hn
  · intro n v hn h
    rw [Submodule.mem_bot] at h ⊢
    exact (smul_eq_zero.mp h).resolve_left hn
  · intro b hb e _
    rw [Submodule.mem_bot] at hb
    simp [hb]
  · intro y e he
    rw [Submodule.mem_bot] at he
    simp [he]
  · intro x b hb
    rw [Submodule.mem_bot] at hb
    simp [hb]
  · intro y hy
    simpa using hy
  · intro x hx
    simpa using hx
  · intro v _
    exact ⟨v, by simp⟩
  · intro n v _ _
    exact ⟨v, by simp⟩

/-- Importing the module keeps the canonical `ℤ`-module structure of an additive group: the
`attribute [-instance] AddCommGroup.toIntModule` used by its proofs does not reach importers. -/
example {A : Type*} [AddCommGroup A] :
    (inferInstance : Module ℤ A) = AddCommGroup.toIntModule A := rfl
