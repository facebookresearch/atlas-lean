/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar.lean`
and
`P2M/Sol/S_ModularCurve_mazurPrinciple_toric_exclusion_of_scalar.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

namespace ModularCurve

/-- The toric Frobenius-square condition: on the submodule `𝒯`, applying
`φ` twice is multiplication by `q ^ 2` (as an integer scalar). -/
public def ToricFrobeniusSq {G : Type*} [Group G] {R : Type*} [CommRing R]
    {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]
    (q : ℕ) (φ : G) (𝒯 : Submodule R J) : Prop :=
  ∀ x ∈ 𝒯, φ • φ • x = ((q : ℤ) ^ 2) • x

/-- Toric scalar exclusion: a two-dimensional representation injected
equivariantly into toric data, on which `φ` acts as the scalar `lam` and
with determinant `q`, forces `q = 0` or `q = 1` in the coefficient field. -/
public theorem mazurPrinciple_toric_exclusion_of_scalar
    {G : Type*} [Group G]
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [DistribMulAction G V] [SMulCommClass G k V]
    {R : Type*} [CommRing R]
    {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]
    {q : ℕ} {φ : G} {𝒯 : Submodule R J}
    (hfrob : ModularCurve.ToricFrobeniusSq q φ 𝒯)
    (ι : V →+ J) (hinj : Function.Injective ι)
    (hequiv : ∀ g : G, ∀ v : V, ι (g • v) = g • ι v)
    (hsub : ∀ v : V, ι v ∈ 𝒯)
    (lam : k) (hscalar : ∀ v : V, φ • v = lam • v)
    (hrank : Module.finrank k V = 2)
    (hdet : LinearMap.det (DistribSMul.toLinearMap k V φ) = (q : k)) :
    (q : k) = 0 ∨ (q : k) = 1 := by
  set A := DistribSMul.toLinearMap k V φ with hAdef
  have hA : A = lam • (LinearMap.id : V →ₗ[k] V) := by
    ext v
    simp only [hAdef, DistribSMul.toLinearMap_apply, hscalar v,
      LinearMap.smul_apply, LinearMap.id_apply]
  have hdetA : LinearMap.det A = lam ^ 2 := by
    rw [hA, LinearMap.det_smul, LinearMap.det_id, mul_one, hrank]
  have hsq : ∀ v : V, A (A v) = ((q : k) ^ 2) • v := by
    intro v
    have hφφ : φ • φ • v = ((q : ℤ) ^ 2) • v := by
      apply hinj
      rw [hequiv, hequiv, map_zsmul]
      exact hfrob (ι v) (hsub v)
    have hcast : ((q : k) ^ 2) • v = ((q : ℤ) ^ 2) • v := by
      have h1 : ((q : k)) ^ 2 = (((q : ℤ) ^ 2 : ℤ) : k) := by push_cast; ring
      rw [h1, Int.cast_smul_eq_zsmul]
    simp only [hAdef, DistribSMul.toLinearMap_apply]
    rw [hcast]
    exact hφφ
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hls : lam ^ 2 = (q : k) ^ 2 := by
    have hlam : (lam ^ 2) • v = ((q : k) ^ 2) • v := by
      have hAA := hsq v
      rw [hA] at hAA
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
        ← pow_two] at hAA
      exact hAA
    by_contra hne
    apply hv
    have hzero : (lam ^ 2 - (q : k) ^ 2) • v = 0 := by
      rw [sub_smul, hlam, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hqeq : (q : k) = (q : k) ^ 2 := hdet.symm.trans (hdetA.trans hls)
  have hfactor : (q : k) * ((q : k) - 1) = 0 := by
    have h1 : (q : k) * ((q : k) - 1) = (q : k) ^ 2 - (q : k) := by ring
    rw [h1, ← hqeq, sub_self]
  rcases mul_eq_zero.mp hfactor with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

end ModularCurve
