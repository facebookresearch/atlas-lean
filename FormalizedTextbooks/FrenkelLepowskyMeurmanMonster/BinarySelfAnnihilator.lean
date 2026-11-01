/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

/-! A maximal isotropic subspace of a finite binary space is its own
annihilator. Maximality is expressed by the concrete cardinality identity
|L|² = |V|. The proof uses the finite-field cardinality formula and Mathlib's
orthogonal-complement dimension theorem, with no coordinate enumeration. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Isotropy and the square-root cardinality condition determine the entire
annihilator in a finite binary space with a nondegenerate symmetric form. -/
theorem binary_orthogonal_eq_of_card
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hsym : ∀ x y, B x y = B y x)
    (hnondeg : ∀ x, (∀ y, B x y = 0) → x = 0)
    (L : Submodule (ZMod 2) V) [Fintype L]
    (hisotropic : ∀ x ∈ L, ∀ y ∈ L, B x y = 0)
    (hcard : (Fintype.card L) ^ 2 = Fintype.card V) :
    LinearMap.BilinForm.orthogonal B L = L := by
  have hB : B.Nondegenerate := by
    constructor
    · exact hnondeg
    · intro x hx
      apply hnondeg x
      intro y
      rw [hsym]
      exact hx y
  have hle : L ≤ LinearMap.BilinForm.orthogonal B L := by
    intro x hx y hy
    exact hisotropic y hy x hx
  have hp : (2 : ℕ) ^ (Module.finrank (ZMod 2) L * 2) =
      2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := L),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := V)] at hcard
    simpa only [ZMod.card, ← pow_mul] using hcard
  have hr : Module.finrank (ZMod 2) L * 2 = Module.finrank (ZMod 2) V :=
    Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hp
  apply (Submodule.eq_of_le_of_finrank_le hle _).symm
  rw [LinearMap.BilinForm.finrank_orthogonal hB]
  omega

/-- The orthogonality test used in finite binary Fourier sums follows from
isotropy and the square-root cardinality condition. -/
theorem binary_self_annihilator_of_card
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hsym : ∀ x y, B x y = B y x)
    (hnondeg : ∀ x, (∀ y, B x y = 0) → x = 0)
    (L : Submodule (ZMod 2) V) [Fintype L]
    (hisotropic : ∀ x ∈ L, ∀ y ∈ L, B x y = 0)
    (hcard : (Fintype.card L) ^ 2 = Fintype.card V) (w : V) :
    (∀ l : L, B l w = 0) ↔ w ∈ L := by
  have he := binary_orthogonal_eq_of_card B hsym hnondeg L hisotropic hcard
  constructor
  · intro h
    rw [← he, LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun l hl => h ⟨l, hl⟩
  · intro hw l
    exact hisotropic l l.property w hw

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
