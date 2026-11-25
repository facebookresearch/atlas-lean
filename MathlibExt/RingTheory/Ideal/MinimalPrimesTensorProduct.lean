/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Ideal_minimalPrimes_tensorProduct_fractionRing_dictionary.lean`
and
`P2M/Sol/S_Ideal_minimalPrimes_tensorProduct_fractionRing_dictionary.lean`
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

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Ideal

/-- Primes of the generic fibre `F ⊗[S] B`, where `F` is a fraction ring of
the domain `S` and `B` is integral over `S`, correspond to the minimal primes
of `B`: every prime of the tensor product contracts to a minimal prime of
`B`, and every minimal prime of `B` has a unique prime above it. This holds
when every minimal prime of `B` contracts to zero in `S`. -/
public theorem minimalPrimes_tensorProduct_fractionRing_dictionary
    {S B F : Type*} [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.IsIntegral S B] [CommRing F] [Algebra S F] [IsFractionRing S F]
    (hdom : ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap S B) 𝔭 = ⊥) :
    (∀ 𝔓 : Ideal (F ⊗[S] B), 𝔓.IsPrime →
        Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[S] F ⊗[S] B) 𝔓 ∈
          (⊥ : Ideal B).minimalPrimes) ∧
    (∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes, ∃! 𝔓 : Ideal (F ⊗[S] B),
        𝔓.IsPrime ∧
          Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[S] F ⊗[S] B) 𝔓 = 𝔭) := by
  classical
  set M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors S) with hM
  haveI : IsLocalization M (F ⊗[S] B) :=
    IsLocalization.tensorRight (R := S) (S := B) F (nonZeroDivisors S)
  have hcomap : ∀ 𝔓 : Ideal (F ⊗[S] B),
      Ideal.comap (Algebra.TensorProduct.includeRight : B →ₐ[S] F ⊗[S] B) 𝔓 =
        𝔓.under B := fun _ => rfl
  have hdisj : ∀ 𝔮 : Ideal B, Disjoint (M : Set B) 𝔮 ↔
      Ideal.comap (algebraMap S B) 𝔮 = ⊥ := by
    intro 𝔮
    constructor
    · intro hd
      rw [eq_bot_iff]
      intro s hs
      rw [Ideal.mem_comap] at hs
      rw [Ideal.mem_bot]
      by_contra hs0
      have hsM : algebraMap S B s ∈ M :=
        Algebra.mem_algebraMapSubmonoid_of_mem
          (⟨s, mem_nonZeroDivisors_of_ne_zero hs0⟩ : nonZeroDivisors S)
      exact Set.disjoint_left.mp hd hsM hs
    · intro h
      refine Set.disjoint_left.mpr ?_
      rintro b ⟨s, hs, rfl⟩ hmem
      have h' : s ∈ Ideal.comap (algebraMap S B) 𝔮 := hmem
      rw [h, Ideal.mem_bot] at h'
      exact nonZeroDivisors.ne_zero hs h'
  have hmin : ∀ 𝔮 : Ideal B, 𝔮.IsPrime → Ideal.comap (algebraMap S B) 𝔮 = ⊥ →
      𝔮 ∈ (⊥ : Ideal B).minimalPrimes := by
    intro 𝔮 h𝔮 h0
    refine ⟨⟨h𝔮, bot_le⟩, ?_⟩
    rintro 𝔮' ⟨h𝔮', -⟩ hle
    by_contra hne
    haveI : 𝔮'.IsPrime := h𝔮'
    have hlt : 𝔮' < 𝔮 := lt_of_le_of_ne hle (fun h => hne (h ▸ le_rfl))
    have hlt' := Ideal.IsIntegral.under_lt_under (R := S) hlt
    have h0' : 𝔮.under S = ⊥ := h0
    rw [h0'] at hlt'
    exact not_lt_bot hlt'
  constructor
  · intro 𝔓 h𝔓
    obtain ⟨hprime, hd⟩ :=
      (IsLocalization.isPrime_iff_isPrime_disjoint M (F ⊗[S] B) 𝔓).mp h𝔓
    rw [hcomap]
    exact hmin _ hprime ((hdisj _).mp hd)
  · intro 𝔭 h𝔭
    have hprime : 𝔭.IsPrime := h𝔭.1.1
    have hd : Disjoint (M : Set B) 𝔭 := (hdisj 𝔭).mpr (hdom 𝔭 h𝔭)
    refine ⟨Ideal.map (algebraMap B (F ⊗[S] B)) 𝔭,
      ⟨IsLocalization.isPrime_of_isPrime_disjoint M _ 𝔭 hprime hd, ?_⟩, ?_⟩
    · rw [hcomap]
      exact IsLocalization.under_map_of_isPrime_disjoint M _ hprime hd
    · rintro 𝔓' ⟨-, hc⟩
      rw [hcomap] at hc
      rw [← hc]
      exact (IsLocalization.map_under M (F ⊗[S] B) 𝔓').symm

end Ideal
