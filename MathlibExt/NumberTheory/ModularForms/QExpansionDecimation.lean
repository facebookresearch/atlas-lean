/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_X0.lean` and
`Definitions/Def_ModularCurve_XHDifferentialsModL.lean`
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

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.LaurentSeries

@[expose] public section

open HahnSeries

namespace ModularCurve

section QExpand

variable {R : Type*} [CommRing R]

/-- The `q`-expansion map on Laurent series: it replaces `q ^ k` by
`q ^ (N * k)`, stretching the exponents by `N`. -/
public noncomputable def qExpand (R : Type*) [CommRing R] (N : ℕ) [NeZero N] :
    LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

variable (N : ℕ) [NeZero N]

@[simp]
public theorem qExpand_coeff_mul (f : LaurentSeries R) (k : ℤ) :
    (qExpand R N f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff

public theorem qExpand_coeff_of_not_dvd (f : LaurentSeries R) {k : ℤ}
    (hk : ¬ (N : ℤ) ∣ k) :
    (qExpand R N f).coeff k = 0 := by
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, rfl⟩
  exact hk ⟨m, rfl⟩

@[simp]
public theorem qExpand_single (k : ℤ) (r : R) :
    qExpand R N (HahnSeries.single k r) = HahnSeries.single ((N : ℤ) * k) r :=
  HahnSeries.embDomain_single

@[simp]
public theorem qExpand_C (r : R) : qExpand R N (HahnSeries.C r) = HahnSeries.C r :=
  HahnSeries.embDomainRingHom_C

public theorem qExpand_injective : Function.Injective (qExpand R N) :=
  HahnSeries.embDomain_injective

public theorem qExpand_one_apply (f : LaurentSeries R) : qExpand R 1 f = f := by
  ext k
  have h : ((1 : ℕ) : ℤ) * k = k := by simp
  conv_lhs => rw [← h]
  rw [qExpand_coeff_mul]

public theorem qExpand_qExpand (M : ℕ) [NeZero M] (f : LaurentSeries R) :
    qExpand R M (qExpand R N f) = qExpand R (M * N) f := by
  ext k
  by_cases hk : ((M : ℤ) * N) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    trans f.coeff m
    · rw [show (M : ℤ) * N * m = (M : ℤ) * ((N : ℤ) * m) by ring, qExpand_coeff_mul,
        qExpand_coeff_mul]
    · rw [show (M : ℤ) * N * m = (((M * N : ℕ) : ℤ)) * m by push_cast; ring,
        qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd (M * N) f (by push_cast; exact hk)]
    by_cases hkM : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hkM
      rw [qExpand_coeff_mul M _ m]
      refine qExpand_coeff_of_not_dvd N _ ?_
      rintro ⟨c, hc⟩
      exact hk ⟨c, by rw [hc]; ring⟩
    · exact qExpand_coeff_of_not_dvd M _ hkM

end QExpand

section Decimate

variable (K : Type*) (p : ℕ) [NeZero p]

/-- The coefficient support of a decimated Laurent series is bounded
below. -/
public theorem bddBelow_support_decimate [Zero K] (x : LaurentSeries K) :
    BddBelow (Function.support fun k : ℤ => x.coeff ((p : ℤ) * k)) := by
  by_cases hne : x.support.Nonempty
  · refine ⟨min (x.isWF_support.min hne) 0, fun k hk => ?_⟩
    have hk' : (p : ℤ) * k ∈ x.support := hk
    have hmin := x.isWF_support.min_le hne hk'
    have hp : (1 : ℤ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    rcases le_or_gt 0 k with h0 | h0
    · exact (min_le_right _ _).trans h0
    · have hle : (p : ℤ) * k ≤ k := by nlinarith
      exact (min_le_left _ _).trans (hmin.trans hle)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, fun k hk => ?_⟩
    exfalso
    have hk' : (p : ℤ) * k ∈ x.support := hk
    rw [hne] at hk'
    exact hk'

section Semiring

variable [Semiring K]

/-- The decimation map on Laurent series: it keeps only the coefficients
whose index is divisible by `p`, reindexed by division by `p`. This is the
series-level operator whose compatibility with the differential of a
`q`-expansion function field defines the Frobenius pushforward on
differentials. -/
public noncomputable def qDecimate : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun x := HahnSeries.ofSuppBddBelow (fun k : ℤ => x.coeff ((p : ℤ) * k))
    (bddBelow_support_decimate K p x)
  map_add' x y := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_add]
  map_smul' c x := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply]

@[simp]
public theorem coeff_qDecimate (x : LaurentSeries K) (k : ℤ) :
    (qDecimate K p x).coeff k = x.coeff ((p : ℤ) * k) := by
  simp only [qDecimate, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_ofSuppBddBelow]

end Semiring

/-- Decimation undoes `q`-expansion by the same factor. -/
public theorem qDecimate_qExpand [CommRing K] (x : LaurentSeries K) :
    qDecimate K p (qExpand K p x) = x := by
  ext k
  rw [coeff_qDecimate, qExpand_coeff_mul]

end Decimate

end ModularCurve
