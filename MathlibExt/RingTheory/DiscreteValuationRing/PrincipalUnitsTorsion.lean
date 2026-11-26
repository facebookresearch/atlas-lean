/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits.lean`,
`Definitions/Def_LocalRing_PrincipalUnits.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits.lean`
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

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import MathlibExt.RingTheory.LocalRing.PrincipalUnits

import Mathlib.NumberTheory.Multiplicity

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing

/-- Let `R` be a discrete valuation ring with maximal ideal `𝔪`, and let `n e : ℕ` satisfy
`Ideal.span {(n : R)} = 𝔪 ^ e`. If a unit `ζ` of `R` lies in `principalUnits R k`, that is,
`ζ - 1 ∈ 𝔪 ^ k`, for some `k` with `e < k`, and `ζ ^ n = 1`, then `ζ = 1`. The strict bound
`e < k` is sharp: in `ℤ_[2]`, with `n = 2` and `e = k = 1`, the unit `-1` is a counterexample. -/
public theorem eq_one_of_pow_eq_one_of_mem_principalUnits
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} {e : ℕ}
    (hne : Ideal.span {(n : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {ζ : Rˣ} (hζ : ζ ∈ principalUnits R k)
    (hζn : ζ ^ n = 1) : ζ = 1 := by
  by_contra hζne
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
    hπ.maximalIdeal_eq
  have hpow : ∀ n : ℕ, IsLocalRing.maximalIdeal R ^ n =
      Ideal.span {π ^ n} := fun n => by
    rw [hmax, Ideal.span_singleton_pow]
  rw [hpow, Ideal.span_singleton_eq_span_singleton] at hne
  obtain ⟨c, hc⟩ := hne.symm
  set x : R := (ζ : R) - 1 with hx_def
  have hx0 : x ≠ 0 := by
    intro h
    apply hζne
    ext
    rw [Units.val_one]
    exact sub_eq_zero.mp h
  obtain ⟨j, w, hxw⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hjk : k ≤ j := by
    have h : π ^ k ∣ x := by
      have hζ' := hζ
      rw [mem_principalUnits_iff, hpow, Ideal.mem_span_singleton] at hζ'
      exact hζ'
    rw [hxw, mul_comm] at h
    have h' : π ^ k ∣ π ^ j := Units.dvd_mul_right.mp h
    exact (pow_dvd_pow_iff hπ0 hπ.not_isUnit).mp h'
  obtain ⟨d, hd⟩ := sq_dvd_add_pow_sub_sub x 1 n
  simp only [one_pow, one_mul] at hd
  have hζ1 : (ζ : R) = 1 + x := by
    rw [hx_def]
    ring
  have hzero : (n : R) * x + x ^ 2 * d = 0 := by
    have h := congrArg Units.val hζn
    rw [Units.val_pow_eq_pow_val, Units.val_one, hζ1] at h
    linear_combination h - hd
  obtain ⟨m, hm⟩ : ∃ m, j = e + m + 1 := ⟨j - e - 1, by omega⟩
  subst hm
  have hfac : (n : R) * x + x ^ 2 * d =
      π ^ (e + (e + m + 1)) * ((c : R) * w + π ^ (m + 1) * (w ^ 2 * d)) := by
    rw [← hc, hxw]
    ring
  have hunit : IsUnit ((c : R) * w + π ^ (m + 1) * (w ^ 2 * d)) := by
    have hmem : π ^ (m + 1) * (w ^ 2 * d) ∈ IsLocalRing.maximalIdeal R := by
      rw [hmax]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) _
          (Nat.succ_pos m))
    by_contra hnu
    have hsum : (c : R) * w ∈ IsLocalRing.maximalIdeal R := by
      have h2 : (c : R) * w + π ^ (m + 1) * (w ^ 2 * d) ∈
          IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      simpa using (IsLocalRing.maximalIdeal R).sub_mem h2 hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hsum (c.isUnit.mul w.isUnit)
  rw [hfac] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact pow_ne_zero _ hπ0 h
  · exact hunit.ne_zero h

end IsDiscreteValuationRing
