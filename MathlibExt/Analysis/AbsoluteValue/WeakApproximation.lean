/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean`
and
`P2M/Sol/S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean`
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

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

namespace AbsoluteValue

/-- Weak approximation for finitely many pairwise inequivalent absolute values.

Given finitely many pairwise inequivalent nontrivial absolute values on a
field and arbitrary targets `a i`, some field element is simultaneously
within `ε` of every target. The approximant is `∑ i, θ i n * a i` for large
`n`, where `θ i n = 1 / (1 + (b i)⁻¹ ^ n)` tends to `1` at `v i` and to `0`
at every other `v j`, for a divergent point `b i` at `v i`. -/
public theorem exists_forall_sub_lt_of_pairwise_not_isEquiv {K : Type*} [Field K]
    {ι : Type*} [Finite ι] {v : ι → AbsoluteValue K ℝ}
    (hv : ∀ i, (v i).IsNontrivial)
    (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K, ∀ i, v i (x - a i) < ε := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => isEmptyElim i⟩
  haveI := Fintype.ofFinite ι
  choose b hb using fun i => AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hv hne i
  have hb0 : ∀ i, b i ≠ 0 := by
    intro i h0
    have h1 := (hb i).1
    rw [h0, map_zero] at h1
    exact absurd h1 (by norm_num)
  set θ : ι → ℕ → K := fun i n => 1 / (1 + (b i)⁻¹ ^ n) with hθ
  have hθ0 : ∀ i j, j ≠ i → Filter.Tendsto (fun n => v j (θ i n)) Filter.atTop (nhds 0) := by
    intro i j hji
    have h1 : 1 < v j (b i)⁻¹ := by
      rw [map_inv₀, one_lt_inv₀ ((v j).pos (hb0 i))]
      exact (hb i).2 j hji
    exact AbsoluteValue.tendsto_div_one_add_pow_nhds_zero h1
  have hθ1 : ∀ i, Filter.Tendsto (fun n => v i (θ i n - 1)) Filter.atTop (nhds 0) := by
    intro i
    have h1 : 1 < v i (b i) := (hb i).1
    have hvinv : v i (b i)⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h1
    have hlim : Filter.Tendsto (fun n => v i (1 / (1 + b i ^ n))) Filter.atTop (nhds 0) :=
      AbsoluteValue.tendsto_div_one_add_pow_nhds_zero h1
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hden : 1 + b i ^ n ≠ 0 := by
      intro h0
      have h2 : v i (b i ^ n) = 1 := by
        rw [eq_neg_of_add_eq_zero_right h0, (v i).map_neg, (v i).map_one]
      rw [map_pow] at h2
      have h3 : 1 < v i (b i) ^ n := one_lt_pow₀ h1 (by omega)
      linarith
    have hden' : 1 + (b i)⁻¹ ^ n ≠ 0 := by
      intro h0
      have h2 : v i ((b i)⁻¹ ^ n) = 1 := by
        rw [eq_neg_of_add_eq_zero_right h0, (v i).map_neg, (v i).map_one]
      rw [map_pow] at h2
      have h3 : v i (b i)⁻¹ ^ n < 1 := pow_lt_one₀ (apply_nonneg _ _) hvinv (by omega)
      linarith
    have hid : θ i n - 1 = -(1 / (1 + b i ^ n)) := by
      have h3 : b i ^ n + 1 ≠ 0 := by rwa [add_comm]
      have hcn : b i ^ n ≠ 0 := pow_ne_zero _ (hb0 i)
      have hden'' : 1 + (b i ^ n)⁻¹ ≠ 0 := by rwa [← inv_pow]
      have h4 : (b i ^ n)⁻¹ + 1 ≠ 0 := by rwa [add_comm]
      simp only [hθ]
      rw [inv_pow]
      field_simp
      ring
    rw [hid, (v i).map_neg]
  let xs : ℕ → K := fun n => ∑ i, θ i n * a i
  have hest : ∀ j n, v j (xs n - a j)
      ≤ v j (θ j n - 1) * v j (a j) + ∑ i ∈ Finset.univ.erase j, v j (θ i n) * v j (a i) := by
    intro j n
    have hsplit : xs n - a j = (θ j n - 1) * a j + ∑ i ∈ Finset.univ.erase j, θ i n * a i := by
      simp only [xs]
      rw [← Finset.add_sum_erase Finset.univ (fun i => θ i n * a i) (Finset.mem_univ j)]
      ring
    rw [hsplit]
    refine ((v j).add_le _ _).trans ?_
    rw [map_mul]
    refine add_le_add le_rfl ?_
    refine ((v j).sum_le _ _).trans ?_
    simp only [map_mul]
    exact le_rfl
  have hlim : ∀ j, Filter.Tendsto (fun n => v j (xs n - a j)) Filter.atTop (nhds 0) := by
    intro j
    have hR : Filter.Tendsto (fun n => v j (θ j n - 1) * v j (a j)
        + ∑ i ∈ Finset.univ.erase j, v j (θ i n) * v j (a i)) Filter.atTop (nhds 0) := by
      have h1 := (hθ1 j).mul_const (v j (a j))
      have h2 : Filter.Tendsto (fun n => ∑ i ∈ Finset.univ.erase j, v j (θ i n) * v j (a i))
          Filter.atTop (nhds (∑ i ∈ Finset.univ.erase j, 0 * v j (a i))) :=
        tendsto_finsetSum _ fun i hi => (hθ0 i j (Finset.ne_of_mem_erase hi).symm).mul_const _
      simpa using h1.add h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR
      (fun n => apply_nonneg _ _) (fun n => hest j n)
  have hev : ∀ᶠ n in Filter.atTop, ∀ j, v j (xs n - a j) < ε :=
    Filter.eventually_all.2 fun j => (hlim j).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨xs n, hn⟩

end AbsoluteValue
