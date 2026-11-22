/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.lean`
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

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

@[expose] public section

namespace IsDiscreteValuationRing

/-- For a discrete valuation ring `R` with maximal ideal `𝔪` and residue
field `k`, the quotient by `𝔪 ^ n` has cardinality `Nat.card k ^ n` for
every `n`.

No finiteness assumption on `k` is needed: when `k` is infinite and
`n > 0`, both sides are `0` under the `Nat.card` convention for infinite
types, and for `n = 0` both sides are `1`. -/
public theorem natCard_quotient_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    Nat.card (R ⧸ IsLocalRing.maximalIdeal R ^ n) =
      Nat.card (IsLocalRing.ResidueField R) ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπ.maximalIdeal_eq
  have hpow : ∀ k : ℕ, IsLocalRing.maximalIdeal R ^ k = Ideal.span {π ^ k} :=
    fun k => by rw [hmax, Ideal.span_singleton_pow]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_of_subsingleton (0 : R ⧸ (⊤ : Ideal R))
  | succ n ih =>
    set T : Submodule R R := IsLocalRing.maximalIdeal R ^ (n + 1) with hT
    set S : Submodule R R := IsLocalRing.maximalIdeal R ^ n with hS
    have hTS : T ≤ S := Ideal.pow_le_pow_right (Nat.le_succ n)
    have hmul := Submodule.card_quotient_mul_card_quotient S T hTS
    let f : R →ₗ[R] R ⧸ T := T.mkQ ∘ₗ LinearMap.lsmul R R (π ^ n)
    have hf : ∀ r, f r = T.mkQ (π ^ n * r) := fun r => rfl
    have hker : LinearMap.ker f = IsLocalRing.maximalIdeal R := by
      ext r
      rw [LinearMap.mem_ker, hf, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hT,
        hpow, hmax, Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ,
        mul_dvd_mul_iff_left (pow_ne_zero n hπ0)]
    have hrange : LinearMap.range f = Submodule.map T.mkQ S := by
      ext y
      constructor
      · rintro ⟨r, rfl⟩
        refine ⟨π ^ n * r, ?_, rfl⟩
        change π ^ n * r ∈ S
        rw [hS, hpow, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
      · rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ S := hx
        rw [hS, hpow, Ideal.mem_span_singleton] at hx'
        obtain ⟨r, rfl⟩ := hx'
        exact ⟨r, rfl⟩
    let g : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] R ⧸ T :=
      (IsLocalRing.maximalIdeal R).liftQ f hker.ge
    have hginj : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
    have hgrange : LinearMap.range g = Submodule.map T.mkQ S := by
      rw [Submodule.range_liftQ, hrange]
    have hcardS : Nat.card (Submodule.map T.mkQ S) =
        Nat.card (IsLocalRing.ResidueField R) := by
      rw [← hgrange]
      exact (Nat.card_congr (LinearEquiv.ofInjective g hginj).toEquiv).symm
    rw [← hmul, hcardS, ih, pow_succ, mul_comm]

end IsDiscreteValuationRing
