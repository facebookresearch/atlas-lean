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

/-!
# Expansion and decimation of Laurent series

For a nonzero natural number `N`, `LaurentSeries.expand R N` is the ring homomorphism that
replaces `X ^ k` by `X ^ (N * k)`. For a nonzero natural number `p`,
`LaurentSeries.decimate K p` is the linear map that keeps the coefficients at indices
divisible by `p` and divides those indices by `p`. Decimation undoes expansion by the same
factor (`LaurentSeries.decimate_expand`), so it is a left inverse of expansion.

The cited source calls these operators `qExpand` and `qDecimate`. It uses `qDecimate` in a
separate predicate, `IsFrobPushDiff K Γ p C`, which says that
`diffQExp (C ω) = qDecimate K p (diffQExp ω)` for every differential `ω` of a `q`-expansion
function field; it describes a Frobenius pushforward on differentials. That predicate is not
defined here.
-/

@[expose] public section

open HahnSeries

namespace LaurentSeries

section Expand

variable {R : Type*} [Semiring R]

/-- **Expansion of Laurent series.** For a semiring `R` and a positive natural number `N`
(`[NeZero N]`), `expand R N` is the ring homomorphism of Laurent series over `R` that replaces
`X ^ k` by `X ^ (N * k)`, stretching the exponents by `N`. -/
public noncomputable def expand (R : Type*) [Semiring R] (N : ℕ) [NeZero N] :
    LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

variable (N : ℕ) [NeZero N]

@[simp]
public theorem coeff_expand_mul (f : LaurentSeries R) (k : ℤ) :
    (expand R N f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff

public theorem coeff_expand_of_not_dvd (f : LaurentSeries R) {k : ℤ}
    (hk : ¬ (N : ℤ) ∣ k) :
    (expand R N f).coeff k = 0 := by
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, rfl⟩
  exact hk ⟨m, rfl⟩

@[simp]
public theorem expand_single (k : ℤ) (r : R) :
    expand R N (HahnSeries.single k r) = HahnSeries.single ((N : ℤ) * k) r :=
  HahnSeries.embDomain_single

@[simp]
public theorem expand_C (r : R) : expand R N (HahnSeries.C r) = HahnSeries.C r :=
  HahnSeries.embDomainRingHom_C

public theorem expand_injective : Function.Injective (expand R N) :=
  HahnSeries.embDomain_injective

public theorem expand_one_apply (f : LaurentSeries R) : expand R 1 f = f := by
  ext k
  have h : ((1 : ℕ) : ℤ) * k = k := by simp
  conv_lhs => rw [← h]
  rw [coeff_expand_mul]

public theorem expand_expand (M : ℕ) [NeZero M] (f : LaurentSeries R) :
    expand R M (expand R N f) = expand R (M * N) f := by
  ext k
  by_cases hk : ((M : ℤ) * N) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    trans f.coeff m
    · rw [show (M : ℤ) * N * m = (M : ℤ) * ((N : ℤ) * m) by ring, coeff_expand_mul,
        coeff_expand_mul]
    · rw [show (M : ℤ) * N * m = (((M * N : ℕ) : ℤ)) * m by push_cast; ring,
        coeff_expand_mul]
  · rw [coeff_expand_of_not_dvd (M * N) f (by push_cast; exact hk)]
    by_cases hkM : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hkM
      rw [coeff_expand_mul M _ m]
      refine coeff_expand_of_not_dvd N _ ?_
      rintro ⟨c, hc⟩
      exact hk ⟨c, by rw [hc]; ring⟩
    · exact coeff_expand_of_not_dvd M _ hkM

end Expand

section Decimate

variable {K : Type*} (p : ℕ) [NeZero p]

/-- **Bounded support of decimated coefficients.** For a positive natural number `p`
(`[NeZero p]`) and a Laurent series `x` whose coefficients lie in a type with zero, the set of
integers `k` with `x.coeff (p * k) ≠ 0` is bounded below. -/
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

variable [Semiring K]

variable (K) in
/-- **Decimation of Laurent series.** For a semiring `K` and a positive natural number `p`
(`[NeZero p]`), `decimate K p` is the `K`-linear map of Laurent series over `K` that keeps only
the coefficients whose index is divisible by `p`, reindexed by division by `p`: the coefficient
of `X ^ k` in `decimate K p x` is the coefficient of `X ^ (p * k)` in `x`. -/
public noncomputable def decimate : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun x := HahnSeries.ofSuppBddBelow (fun k : ℤ => x.coeff ((p : ℤ) * k))
    (bddBelow_support_decimate p x)
  map_add' x y := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_add]
  map_smul' c x := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply]

@[simp]
public theorem coeff_decimate (x : LaurentSeries K) (k : ℤ) :
    (decimate K p x).coeff k = x.coeff ((p : ℤ) * k) := by
  simp only [decimate, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_ofSuppBddBelow]

/-- **Decimation undoes expansion.** For a semiring `K` and a positive natural number `p`
(`[NeZero p]`), decimating by `p` the expansion by `p` of a Laurent series over `K` gives the
series back: `decimate K p (expand K p x) = x`. -/
public theorem decimate_expand (x : LaurentSeries K) :
    decimate K p (expand K p x) = x := by
  ext k
  rw [coeff_decimate, coeff_expand_mul]

end Decimate

end LaurentSeries
