/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_isAdicComplete_of_module_finite.lean`
and
`P2M/Sol/S_IsLocalRing_isAdicComplete_of_module_finite.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Over

/-!
# Adic completeness of finite modules and finite local extensions

A finite module over a Noetherian adically complete ring is adically
complete, and a finite local extension of an adically complete local ring
is adically complete at its maximal ideal. The argument compares the adic
topologies of two ideals, one of which is a power of the other.
-/

@[expose] public section

universe u v w

namespace AdicCompleteModuleFiniteAux

open IsLocalRing

section Compare

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I J : Ideal R}

private theorem smul_top_pow_le_of_le (hIJ : I ≤ J) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

private theorem smul_top_pow_mul_le_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) (n : ℕ) :
    (J ^ (N * n) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
  rw [pow_mul]
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)

private theorem isHausdorff_of_le (hIJ : I ≤ J) [h : IsHausdorff J M] : IsHausdorff I M :=
  ⟨fun x hx => h.haus x fun n => (hx n).mono (smul_top_pow_le_of_le hIJ n)⟩

private theorem isHausdorff_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) [h : IsHausdorff I M] :
    IsHausdorff J M :=
  ⟨fun x hx => h.haus x fun n => (hx (N * n)).mono (smul_top_pow_mul_le_of_pow_le hJI n)⟩

private theorem isPrecomplete_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete I M] : IsPrecomplete J M := by
  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec (f := fun n => f (N' * n)) fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left N' hmn)).mono (smul_top_pow_mul_le_of_pow_le hJI' m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans ((hL n).mono (smul_top_pow_le_of_le hIJ n))

private theorem isPrecomplete_of_pow_le_of_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete J M] : IsPrecomplete I M := by
  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec (f := f) fun {m n} hmn =>
    (hf hmn).mono (smul_top_pow_le_of_le hIJ m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans
    ((hL (N' * n)).mono (smul_top_pow_mul_le_of_pow_le hJI' n))

private theorem isAdicComplete_iff_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  constructor
  · intro h
    haveI := isHausdorff_of_pow_le (M := M) hJI
    haveI := isPrecomplete_of_le_of_pow_le (M := M) hIJ hJI
    exact ⟨⟩
  · intro h
    haveI := isHausdorff_of_le (M := M) hIJ
    haveI := isPrecomplete_of_pow_le_of_le (M := M) hIJ hJI
    exact ⟨⟩

end Compare

section ModuleFinite

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

open AdicCompletion

private theorem isPrecomplete_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [IsPrecomplete I M] : IsPrecomplete I N := by
  rw [← AdicCompletion.of_surjective_iff]
  intro z
  obtain ⟨w, rfl⟩ := AdicCompletion.map_surjective I hf z
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M w
  exact ⟨f x, (AdicCompletion.map_of I f x).symm⟩

private theorem isPrecomplete_pi (ι : Type*) [Finite ι] [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [← AdicCompletion.of_surjective_iff]
  intro z
  choose x hx using fun j =>
    AdicCompletion.of_surjective I R (AdicCompletion.piEquivOfFintype I (fun _ : ι => R) z j)
  refine ⟨x, (AdicCompletion.piEquivOfFintype I (fun _ : ι => R)).injective ?_⟩
  funext j
  rw [AdicCompletion.piEquivOfFintype_apply, ← hx j]
  change AdicCompletion.map I (LinearMap.proj j) (AdicCompletion.of I (ι → R) x) = _
  rw [AdicCompletion.map_of]
  rfl

private theorem isPrecomplete_of_module_finite [IsPrecomplete I R] [Module.Finite R M] :
    IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I (Fin n)
  exact isPrecomplete_of_surjective I f hf

private theorem isAdicComplete_of_module_finite [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] : IsAdicComplete I M :=
  haveI := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  haveI := isPrecomplete_of_module_finite I (M := M)
  ⟨⟩

end ModuleFinite

section Local

variable {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing T] [Algebra 𝒪 T]
  [Module.Finite 𝒪 T] [IsLocalRing T]

private theorem exists_maximalIdeal_pow_le_map :
    ∃ N, maximalIdeal T ^ N ≤ (maximalIdeal 𝒪).map (algebraMap 𝒪 T) := by
  letI : Field (𝒪 ⧸ maximalIdeal 𝒪) := Ideal.Quotient.field _
  haveI : Module.Finite (𝒪 ⧸ maximalIdeal 𝒪) (T ⧸ (maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  haveI : IsArtinianRing (T ⧸ (maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    IsArtinianRing.of_finite (𝒪 ⧸ maximalIdeal 𝒪) _
  exact exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _

private theorem isAdicComplete_maximalIdeal_of_module_finite [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] :
    IsAdicComplete (maximalIdeal T) T := by
  let _ : Algebra.IsIntegral 𝒪 T := Algebra.IsIntegral.of_finite 𝒪 T
  let _ : IsLocalHom (algebraMap 𝒪 T) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap 𝒪 T)).out 5 1).mp
    have hmax : ((maximalIdeal T).comap (algebraMap 𝒪 T)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap 𝒪 T)
        (algebraMap_isIntegral_iff.mpr inferInstance) (maximalIdeal T)
    exact ((maximal_ideal_unique 𝒪).unique (maximalIdeal.isMaximal 𝒪) hmax).symm
  haveI h1 : IsAdicComplete (maximalIdeal 𝒪) T := isAdicComplete_of_module_finite _
  haveI h2 : IsAdicComplete ((maximalIdeal 𝒪).map (algebraMap 𝒪 T)) T :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal 𝒪) T).mpr h1
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map (𝒪 := 𝒪) (T := T)
  exact (isAdicComplete_iff_of_le_of_pow_le
    (IsLocalRing.map_maximalIdeal_le (algebraMap 𝒪 T)) hN).mp h2

end Local

end AdicCompleteModuleFiniteAux

namespace IsLocalRing

/-- A finite local extension of an adically complete local ring is adically
complete at its maximal ideal. -/
theorem isAdicComplete_of_module_finite {𝒪 : Type u} {T : Type v} [CommRing 𝒪]
    [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsLocalRing T] :
    IsAdicComplete (IsLocalRing.maximalIdeal T) T :=
  AdicCompleteModuleFiniteAux.isAdicComplete_maximalIdeal_of_module_finite (𝒪 := 𝒪) (T := T)

end IsLocalRing
