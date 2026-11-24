/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_hasSum_qParam_mul.lean`
and
`P2M/Sol/S_ModularCurve_hasSum_qParam_mul.lean`
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

public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

private theorem norm_qParam_lt_one_of_pos {h : ℝ} (hh : 0 < h) (τ : ℍ) :
    ‖𝕢 h (τ : ℂ)‖ < 1 := by
  have := (Periodic.norm_qParam_lt_iff hh 0 (τ : ℂ)).mpr (by simpa using τ.im_pos)
  simpa using this

private theorem summable_norm_of_hasSum_qParam {h : ℝ} (hh : 0 < h) {a : ℕ → ℂ}
    {F : ℍ → ℂ}
    (hA : ∀ τ : ℍ, HasSum (fun m : ℕ => a m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ}
    (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => ‖a m * q ^ m‖) := by
  obtain ⟨r, hqr, hr1⟩ := exists_between hq
  have hr0 : 0 < r := (norm_nonneg q).trans_lt hqr
  have hr1' : ‖(r : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hrne : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  let τ' : ℍ := ⟨Periodic.invQParam h r, Periodic.im_invQParam_pos_of_norm_lt_one hh hr1' hrne⟩
  have hq' : 𝕢 h (τ' : ℂ) = r := Periodic.qParam_right_inv hh.ne' hrne
  have hs : Summable (fun m : ℕ => a m * (r : ℂ) ^ m) := by
    have := (hA τ').summable
    rwa [hq'] at this
  have hev : ∀ᶠ m : ℕ in cofinite, ‖a m * (r : ℂ) ^ m‖ < 1 :=
    NormedAddGroup.tendsto_nhds_zero.mp hs.tendsto_cofinite_zero 1 one_pos
  refine Summable.of_norm_bounded_eventually (g := fun m : ℕ => (‖q‖ / r) ^ m)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hr0).mpr hqr)) ?_
  filter_upwards [hev] with m hm
  rw [norm_norm, norm_mul, norm_pow, div_pow, le_div_iff₀ (pow_pos hr0 m)]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le] at hm
  calc ‖a m‖ * ‖q‖ ^ m * r ^ m = (‖a m‖ * r ^ m) * ‖q‖ ^ m := by ring
    _ ≤ 1 * ‖q‖ ^ m := by gcongr
    _ = ‖q‖ ^ m := one_mul _

/-- The product of two everywhere convergent `q`-expansions is the
`q`-expansion of the product power series: if `A` sums to `F` and `B`
sums to `G` at every upper-half-plane point (for a positive real period
`h`), then `A * B` sums to `F * G`. This is the Cauchy product for
`q`-series. -/
public theorem hasSum_qParam_mul (h : ℝ) (hh : 0 < h) (A B : PowerSeries ℂ)
    (F G : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum
      (fun m : ℕ => PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : UpperHalfPlane, HasSum
      (fun m : ℕ => PowerSeries.coeff m B * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (A * B) *
      Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ * G τ) := by
  set q : ℂ := 𝕢 h (τ : ℂ) with hqdef
  have hq : ‖q‖ < 1 := norm_qParam_lt_one_of_pos hh τ
  have hsA := summable_norm_of_hasSum_qParam hh hA hq
  have hsB := summable_norm_of_hasSum_qParam hh hB hq
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsA hsB
  have hsum : Summable (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 A * q ^ kl.1) * (PowerSeries.coeff kl.2 B * q ^ kl.2)) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hsA hsB).of_norm
  have H : HasSum (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 A * q ^ kl.1) * (PowerSeries.coeff kl.2 B * q ^ kl.2))
      (F τ * G τ) := by
    rw [← (hA τ).tsum_eq, ← (hB τ).tsum_eq, ← hqdef, key]
    exact hsum.hasSum
  have hfg : (fun m : ℕ => PowerSeries.coeff m (A * B) * q ^ m) =
      (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 A * q ^ kl.1) * (PowerSeries.coeff kl.2 B * q ^ kl.2)) := by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  rw [hfg]
  exact H

end ModularCurve
