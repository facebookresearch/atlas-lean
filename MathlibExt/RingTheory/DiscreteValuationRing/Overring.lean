/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_exists_algebraMap_eq_of_mem_subring_of_ne_top.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_exists_algebraMap_eq_of_mem_subring_of_ne_top.lean`
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
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

namespace IsDiscreteValuationRing

variable {V K : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

private theorem subring_eq_top_of_inv_mem (W : Subring K)
    (hVW : ∀ v : V, algebraMap V K v ∈ W)
    {ϖ : V} (hϖ : Irreducible ϖ) (hinv : (algebraMap V K ϖ)⁻¹ ∈ W) : W = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  by_cases hy : y = 0
  · rw [hy]; exact W.zero_mem
  obtain ⟨n, u, rfl⟩ := exists_units_eq_smul_zpow_of_irreducible hϖ hy
  rw [Units.smul_def, Algebra.smul_def]
  refine W.mul_mem (hVW _) ?_
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zpow_natCast, ← map_pow]; exact hVW _
  · have hn : n < 0 := lt_of_not_ge hn
    obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact W.pow_mem hinv m

/-- Every element of a proper subring of the fraction field of a discrete
valuation ring that contains the image of the ring already lies in that
image. In other words, there is no subring strictly between a discrete
valuation ring and its fraction field that contains the ring and is
proper: any such subring is the ring itself, viewed inside the fraction
field. -/
public theorem exists_algebraMap_eq_of_mem_subring_of_ne_top
    (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]
    (W : Subring K) (hVW : ∀ v : V, algebraMap V K v ∈ W) (hW : W ≠ ⊤)
    (x : K) (hx : x ∈ W) :
    ∃ v : V, algebraMap V K v = x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible V
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [map_zero, hx0]⟩
  obtain ⟨n, u, rfl⟩ := exists_units_eq_smul_zpow_of_irreducible hϖ hx0
  have hinj := IsFractionRing.injective V K
  have hπ : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hu : algebraMap V K u ≠ 0 := (map_ne_zero_iff _ hinj).mpr u.ne_zero
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact ⟨u * ϖ ^ m, by
      rw [map_mul, map_pow, Units.smul_def, Algebra.smul_def, zpow_natCast]⟩
  · exfalso
    have hn : n < 0 := lt_of_not_ge hn
    obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
    refine hW (subring_eq_top_of_inv_mem W hVW hϖ ?_)
    have key : (algebraMap V K ϖ)⁻¹ =
        (u • algebraMap V K ϖ ^ (-((k + 1 : ℕ) : ℤ))) *
          algebraMap V K (↑u⁻¹ * ϖ ^ k) := by
      rw [Units.smul_def, Algebra.smul_def, map_mul, map_pow, zpow_neg,
        zpow_natCast, map_units_inv]
      field_simp
      ring
    rw [key]
    exact W.mul_mem hx (hVW _)

end IsDiscreteValuationRing
