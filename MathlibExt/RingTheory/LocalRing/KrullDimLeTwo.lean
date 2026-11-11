/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two.lean`
and
`P2M/Sol/S_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two.lean`
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

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Order.KrullDimension

/-!
# Primes in a local domain whose completion has Krull dimension at most two

If the adic completion of a Noetherian local domain `B` has Krull
dimension at most `2`, then any prime `𝔭` strictly below a non-maximal
prime `𝔮` is `⊥`: going down lifts the chain `⊥ < 𝔭 < 𝔮 < maximalIdeal`
to a chain of length `3` in the completion, contradicting the dimension
bound.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace IsLocalRing

/-- In a Noetherian local domain whose adic completion has Krull dimension
at most `2`, any prime strictly below a non-maximal prime is `⊥`. -/
theorem eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
    {B : Type u} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    {R : Type v} [CommRing R] (e : AdicCompletion (maximalIdeal B) B ≃+* R)
    (hR : ringKrullDim R ≤ 2) :
    ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥ := by
  intro 𝔭 𝔮 h𝔭 h𝔮 h𝔮m hlt
  by_contra h0
  set S := AdicCompletion (maximalIdeal B) B with hSdef
  have hS : ringKrullDim S ≤ 2 := (ringKrullDim_eq_of_ringEquiv e).trans_le hR
  have : Module.Flat B S := AdicCompletion.flat_of_isNoetherian (maximalIdeal B)
  have : Algebra.HasGoingDown B S := Algebra.HasGoingDown.of_flat
  have hsurj : Function.Surjective (AdicCompletion.evalOneₐ (maximalIdeal B)) := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap B S b, by rw [AlgHom.commutes]; rfl⟩
  have hmaxB : (maximalIdeal B).IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  let _ : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field (maximalIdeal B)
  set Q₃ : Ideal S := RingHom.ker (AdicCompletion.evalOneₐ (maximalIdeal B)).toRingHom with hQ₃
  have hQ₃max : Q₃.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have : Q₃.IsPrime := hQ₃max.isPrime
  have hunder₃ : Q₃.under B = maximalIdeal B := by
    ext b
    rw [Ideal.under_def, Ideal.mem_comap, hQ₃, RingHom.mem_ker]
    change AdicCompletion.evalOneₐ (maximalIdeal B) (algebraMap B S b) = 0 ↔ _
    rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  have : Q₃.LiesOver (maximalIdeal B) := ⟨hunder₃.symm⟩
  have _ := h𝔮
  have _ := h𝔭
  have h𝔮le : 𝔮 ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal h𝔮.ne_top
  obtain ⟨Q₂, hQ₂₃, hQ₂p, hQ₂o⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := 𝔮) (q := maximalIdeal B) Q₃ h𝔮le
  have _ := hQ₂p
  have _ := hQ₂o
  obtain ⟨Q₁, hQ₁₂, hQ₁p, hQ₁o⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) (q := 𝔮) Q₂ hlt.le
  have _ := hQ₁p
  have _ := hQ₁o
  have : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
  obtain ⟨Q₀, hQ₀₁, hQ₀p, hQ₀o⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal B)) (q := 𝔭) Q₁ bot_le
  have hu₂ : Q₂.under B = 𝔮 := (hQ₂o.over).symm
  have hu₁ : Q₁.under B = 𝔭 := (hQ₁o.over).symm
  have hu₀ : Q₀.under B = ⊥ := (hQ₀o.over).symm
  have h₀₁ : Q₀ < Q₁ := lt_of_le_of_ne hQ₀₁ (fun h => h0 (by rw [← hu₁, ← h, hu₀]))
  have h₁₂ : Q₁ < Q₂ := lt_of_le_of_ne hQ₁₂ (fun h => hlt.ne (by rw [← hu₁, h, hu₂]))
  have h₂₃ : Q₂ < Q₃ := lt_of_le_of_ne hQ₂₃ (fun h => h𝔮m (by rw [← hu₂, h, hunder₃]))
  let c : LTSeries (PrimeSpectrum S) :=
    { length := 3
      toFun := fun i => match i with
        | ⟨0, _⟩ => ⟨Q₀, hQ₀p⟩
        | ⟨1, _⟩ => ⟨Q₁, hQ₁p⟩
        | ⟨2, _⟩ => ⟨Q₂, hQ₂p⟩
        | ⟨_ + 3, _⟩ => ⟨Q₃, inferInstance⟩
      step := by
        intro i
        fin_cases i
        · exact h₀₁
        · exact h₁₂
        · exact h₂₃ }
  have h3 : (3 : WithBot ℕ∞) ≤ ringKrullDim S := Order.LTSeries.length_le_krullDim c
  have : (3 : WithBot ℕ∞) ≤ 2 := h3.trans hS
  exact absurd this (by decide)

end IsLocalRing
