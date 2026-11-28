/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from:

`Theorems/Thm_Algebra_IsPushout_exists_algEquiv_slice_eq_of_flat.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The signatures of `exactSource` and of the independent-universe example restate
that file's theorem statement; the theorem applications, the injective-map
instance and the `ℤ → ℚ` example are original test code.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.Algebra.Algebra.IsPushoutFlatGluing

@[expose] public section

open scoped TensorProduct

universe u v w x y

/-- Consumer with the original binders, all in one universe. The source's
surjectivity hypothesis `_hπ` is kept but no longer needed. -/
private theorem exactSource
    {B B₁ B' M N : Type u} [CommRing B] [CommRing B₁] [CommRing B']
    [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M]
    [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N]
    [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (_hπ : Function.Surjective (algebraMap B B₁))
    (p : Fin 3 → (B' →ₐ[B] B))
    (hp : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (p i x) = algebraMap B' B₁ x)
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B,
      (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) →
        ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'),
      e i (algebraMap B' N x) = algebraMap B M (p i x))
    (t : Fin 3 → (M ≃ₐ[B] M))
    (ht : ∀ (i : Fin 3) (m : M),
      t i m - m ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) :
    ∃ σ : N ≃ₐ[B'] N,
      (∀ (i : Fin 3) (n : N), e i (σ n) = t i (e i n)) ∧
      (∀ n : N,
        σ n - n ∈ (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' N)) ∧
      (∀ σ' : N →ₐ[B'] N,
        (∀ (i : Fin 3) (n : N), e i (σ' n) = t i (e i n)) →
          ∀ n : N, σ' n = σ n) :=
  Algebra.IsPushout.exists_algEquiv_slice_eq_of_flat
    p hp hinj hsurj e heM heB t ht

/-- Higher-universe consumer with no surjectivity hypothesis on `B → B₁`: the
five rings may live in independent universes. -/
example
    {B : Type u} {B₁ : Type v} {B' : Type w} {M : Type x} {N : Type y}
    [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M]
    [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N]
    [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (p : Fin 3 → (B' →ₐ[B] B))
    (hp : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (p i x) = algebraMap B' B₁ x)
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B,
      (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) →
        ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'),
      e i (algebraMap B' N x) = algebraMap B M (p i x))
    (t : Fin 3 → (M ≃ₐ[B] M))
    (ht : ∀ (i : Fin 3) (m : M),
      t i m - m ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) :
    ∃ σ : N ≃ₐ[B'] N,
      (∀ (i : Fin 3) (n : N), e i (σ n) = t i (e i n)) ∧
      (∀ n : N,
        σ n - n ∈ (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' N)) ∧
      (∀ σ' : N →ₐ[B'] N,
        (∀ (i : Fin 3) (n : N), e i (σ' n) = t i (e i n)) →
          ∀ n : N, σ' n = σ n) :=
  Algebra.IsPushout.exists_algEquiv_slice_eq_of_flat
    p hp hinj hsurj e heM heB t ht

/-- The comparison map need not be surjective: for an injective `algebraMap R S`,
the trivial pushout square of `R` with identity slices meets every hypothesis,
and the three identity automorphisms glue to the identity. -/
private theorem exists_algEquiv_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hRS : Function.Injective (algebraMap R S)) :
    ∃ σ : R ≃ₐ[R] R, ∀ n, σ n = n := by
  obtain ⟨σ, hσ, -, -⟩ := Algebra.IsPushout.exists_algEquiv_slice_eq_of_flat
    (B₁ := S) (fun _ => AlgHom.id R R) (fun _ _ => rfl) (fun _ _ h => h 0)
    (fun b hb => ⟨b 0, fun i => (hRS (hb i 0)).symm⟩) (fun _ => AlgHom.id R R)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => AlgEquiv.refl) (fun _ m => by simp)
  exact ⟨σ, hσ 0⟩

/-- `ℤ → ℚ` is injective but not surjective, and the theorem applies to it. -/
example : ¬ Function.Surjective (algebraMap ℤ ℚ) ∧ ∃ σ : ℤ ≃ₐ[ℤ] ℤ, ∀ n, σ n = n := by
  refine ⟨fun h => ?_, exists_algEquiv_of_injective (algebraMap ℤ ℚ).injective_int⟩
  obtain ⟨n, hn⟩ := h (1 / 2)
  rw [eq_intCast] at hn
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by push_cast; rw [hn]; norm_num
  have : 2 * n = 1 := by exact_mod_cast h2
  omega
