/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_Module_free_of_torsionBySet_eq_annihilator_smul.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.LocalRing.FreeOfBalancedPairing

universe u w x

/-- The original statement, with its original binders, follows from the
public theorem. -/
example
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M :=
  Module.free_of_torsionBySet_eq_annihilator_smul πT hη C hC hCb M B hB hBb hrank hsat

/-- Higher-universe consumer: all three types in `Type 1`. -/
example
    {𝒪 : Type 1} {T : Type 1} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (M : Type 1) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M :=
  Module.free_of_torsionBySet_eq_annihilator_smul πT hη C hC hCb M B hB hBb hrank hsat

/-- Over `ℚ`, the identity augmentation has kernel `⊥`. -/
private theorem ker_algHom_id_rat : RingHom.ker (AlgHom.id ℚ ℚ) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id

/-- Multiplication is a perfect pairing on `ℚ`. -/
private theorem bijective_mul_rat : Function.Bijective (LinearMap.mul ℚ ℚ) :=
  ⟨fun a b h => by simpa using LinearMap.congr_fun h 1,
    fun f => ⟨f 1, LinearMap.ext_ring (by simp)⟩⟩

/-- Every element of `ℚ` is killed by the kernel `⊥` of the identity augmentation. -/
private theorem torsionBySet_ker_algHom_id_rat :
    Submodule.torsionBySet ℚ ℚ ↑(RingHom.ker (AlgHom.id ℚ ℚ)) = ⊤ := by
  rw [ker_algHom_id_rat]
  ext m
  simp

/-- The hypotheses hold together: `𝒪 = T = M = ℚ`, with the identity augmentation and
multiplication as both pairings, satisfies every one of them. -/
example : Module.Free ℚ ℚ :=
  Module.free_of_torsionBySet_eq_annihilator_smul (AlgHom.id ℚ ℚ)
    (by rw [ker_algHom_id_rat, Submodule.annihilator_bot, Ideal.map_top]; exact top_ne_bot)
    (LinearMap.mul ℚ ℚ) (fun s t u => by simp only [LinearMap.mul_apply']; ring)
    bijective_mul_rat ℚ (LinearMap.mul ℚ ℚ)
    (fun t m n => by simp only [smul_eq_mul, LinearMap.mul_apply']; ring) bijective_mul_rat
    (by rw [torsionBySet_ker_algHom_id_rat, finrank_top, Module.finrank_self, one_mul])
    (by rw [torsionBySet_ker_algHom_id_rat, ker_algHom_id_rat, Submodule.annihilator_bot,
      Submodule.top_smul])
