/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Valuation_eq_comap_of_valuationSubring_le_comap.lean`
and
`P2M/Sol/S_Valuation_eq_comap_of_valuationSubring_le_comap.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.RingTheory.KrullDimension.PID

@[expose] public section

open scoped WithZero

namespace Valuation

private theorem eq_of_valuationSubring_eq_aux {L : Type*} [Field L]
    (v w : Valuation L ℤᵐ⁰)
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (h : v.valuationSubring = w.valuationSubring) : v = w := by
  have heq : v.IsEquiv w := (Valuation.isEquiv_iff_valuationSubring _ _).mpr h
  obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1))
  obtain ⟨ρ, hρ⟩ := hw (WithZero.exp (-1))
  have hπ0 : π ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hρ0 : ρ ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hρ; exact WithZero.exp_ne_zero hρ.symm
  have hwπ : w π = WithZero.exp (-1) := by
    have hwπ1 : w π < 1 := heq.lt_one_iff_lt_one.mp (by rw [hπ]; decide)
    have hwπ0 : w π ≠ 0 := (w.ne_zero_iff).mpr hπ0
    have hle : w π ≤ w ρ := by
      rw [hρ, ← WithZero.exp_log hwπ0, WithZero.exp_le_exp]
      have hlt : WithZero.log (w π) < 0 := by
        rw [← WithZero.exp_lt_exp, WithZero.exp_log hwπ0]; exact hwπ1
      omega
    have hvle : v π ≤ v ρ := heq.le_iff_le.mpr hle
    have hvρ1 : v ρ < 1 := heq.lt_one_iff_lt_one.mpr (by rw [hρ]; decide)
    have hvρ0 : v ρ ≠ 0 := (v.ne_zero_iff).mpr hρ0
    have hvρ : v ρ = v π := by
      rw [hπ] at hvle ⊢
      rw [← WithZero.exp_log hvρ0, WithZero.exp_le_exp] at hvle
      rw [← WithZero.exp_log hvρ0, ← WithZero.exp_zero,
        WithZero.exp_lt_exp] at hvρ1
      rw [← WithZero.exp_log hvρ0, WithZero.exp_inj]
      omega
    rw [← hρ]
    exact (heq.eq_iff.mp hvρ).symm
  ext x
  by_cases hx : x = 0
  · simp [hx]
  have hvx0 : v x ≠ 0 := (v.ne_zero_iff).mpr hx
  set k := WithZero.log (v x) with hk
  have hvx : v x = v (π ^ (-k)) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one,
      neg_neg, hk, WithZero.exp_log hvx0]
  have hwx : w x = w (π ^ (-k)) := heq.eq_iff.mp hvx
  rw [hwx, map_zpow₀, hwπ, hvx, map_zpow₀, hπ]

private lemma valuationSubring_comap {L L' : Type*} [Field L] [Field L']
    (v : Valuation L' ℤᵐ⁰) (σ : L →+* L') :
    (v.comap σ).valuationSubring = v.valuationSubring.comap σ := by
  ext x
  rw [mem_valuationSubring_iff, ValuationSubring.mem_comap,
    mem_valuationSubring_iff, comap_apply]

/-- Two surjective `ℤᵐ⁰`-valued valuations on fields that are related by a
field isomorphism are equal as soon as the valuation subring of one is
contained in the pullback of the other.

Surjectivity normalizes both valuations, so the subring inclusion forces
the valuation subrings to coincide, and a normalized discrete valuation is
determined by its valuation subring. -/
public theorem eq_comap_of_valuationSubring_le_comap {L L' : Type*}
    [Field L] [Field L']
    {v : Valuation L' (WithZero (Multiplicative ℤ))}
    {w : Valuation L (WithZero (Multiplicative ℤ))}
    (hv : Function.Surjective v) (hw : Function.Surjective w)
    (σ : L ≃+* L')
    (hle : w.valuationSubring ≤ v.valuationSubring.comap σ.toRingHom) :
    w = v.comap σ.toRingHom := by
  have hvσ : Function.Surjective (v.comap σ.toRingHom) := fun γ => by
    obtain ⟨y, hy⟩ := hv γ
    exact ⟨σ.symm y, by
      rw [comap_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply, hy]⟩
  haveI : w.IsNontrivial := by
    obtain ⟨π, hπ⟩ := hw (WithZero.exp (-1))
    exact ⟨π, by rw [hπ]; exact ⟨WithZero.exp_ne_zero, by decide⟩⟩
  have hne : (v.comap σ.toRingHom).valuationSubring ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hvσ (WithZero.exp 1)
    intro h
    have hx' : x ∈ (v.comap σ.toRingHom).valuationSubring :=
      h ▸ ValuationSubring.mem_top x
    rw [mem_valuationSubring_iff, hx] at hx'
    exact absurd hx' (by decide)
  rw [← valuationSubring_comap] at hle
  exact eq_of_valuationSubring_eq_aux w _ hw hvσ
    (ValuationSubring.eq_of_le_of_ne_top _ hle hne)

end Valuation
