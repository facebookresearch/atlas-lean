/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Algebra.IsPushoutFlatGluing

@[expose] public section

open scoped TensorProduct

universe u v w x y

/-- Consumer with the original binders, all in one universe. -/
theorem exactSource
    {B B₁ B' M N : Type u} [CommRing B] [CommRing B₁] [CommRing B']
    [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M]
    [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N]
    [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (hπ : Function.Surjective (algebraMap B B₁))
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
    hπ p hp hinj hsurj e heM heB t ht

/-- Higher-universe consumer: the five rings may live in independent
universes. -/
example
    {B : Type u} {B₁ : Type v} {B' : Type w} {M : Type x} {N : Type y}
    [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M]
    [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N]
    [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (hπ : Function.Surjective (algebraMap B B₁))
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
    hπ p hp hinj hsurj e heM heB t ht
