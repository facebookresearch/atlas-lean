/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_exists_analyticOnNhd_div_of_monicRel.lean`
and
`P2M/Sol/S_WLight_exists_analyticOnNhd_div_of_monicRel.lean`
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

public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Analytic quotients from monic relations

This file shows that a quotient `F / G` satisfying a monic relation with analytic coefficients
is analytic.

## Main statement

* `AnalyticOnNhd.exists_div_of_monicRel`
-/
namespace FrickeFunctions.AnalyticDivMonicRel

noncomputable section

open Complex
open Real
open scoped Topology

namespace Aux

section ValuationEngine

private theorem le_meromorphicOrderAt_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} (s : Finset ι) {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) (m : WithTop ℤ)
    (hm : ∀ i ∈ s, m ≤ meromorphicOrderAt (f i) x) :
    m ≤ meromorphicOrderAt (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc m ≤ min (meromorphicOrderAt (f a) x) (meromorphicOrderAt (∑ i ∈ s, f i) x) := by
            refine le_min (hm a (Finset.mem_insert_self a s)) ?_
            exact ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
              (fun i hi ↦ hm i (Finset.mem_insert_of_mem hi))
      _ ≤ meromorphicOrderAt (f a + ∑ i ∈ s, f i) x := by
            apply meromorphicOrderAt_add (hf a (Finset.mem_insert_self a s))
            exact MeromorphicAt.sum (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private theorem meromorphicOrderAt_le_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    meromorphicOrderAt G τ ≤ meromorphicOrderAt F τ := by
  by_contra hlt
  rw [not_le] at hlt
  lift meromorphicOrderAt G τ to ℤ using hGord with m hm
  have hFord : meromorphicOrderAt F τ ≠ ⊤ := hlt.ne_top
  lift meromorphicOrderAt F τ to ℤ using hFord with r hr
  have hrm : r < m := WithTop.coe_lt_coe.mp hlt
  set S := ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k with hS
  have hMerS : ∀ k ∈ Finset.range n, MeromorphicAt (c k * G ^ (n - k) * F ^ k) τ := by
    intro k hk
    exact (((hc k (Finset.mem_range.mp hk)).mul ((hG.pow _))).mul (hF.pow _)).meromorphicAt
  have hsum_ord : (↑(n * r) + 1 : WithTop ℤ) ≤ meromorphicOrderAt S τ := by
    refine le_meromorphicOrderAt_sum _ hMerS _ ?_
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hterm : meromorphicOrderAt (c k * G ^ (n - k) * F ^ k) τ
        = meromorphicOrderAt (c k) τ + ((n - k : ℕ) * meromorphicOrderAt G τ
            + k * meromorphicOrderAt F τ) := by
      rw [meromorphicOrderAt_mul (((hc k hk').mul (hG.pow (n - k))).meromorphicAt)
            ((hF.pow k).meromorphicAt),
          meromorphicOrderAt_mul (hc k hk').meromorphicAt ((hG.pow (n - k)).meromorphicAt),
          meromorphicOrderAt_pow hG.meromorphicAt (n := n - k),
          meromorphicOrderAt_pow hF.meromorphicAt (n := k), add_assoc]
    rw [hterm, ← hm, ← hr]
    have hc_ord : (0 : WithTop ℤ) ≤ meromorphicOrderAt (c k) τ :=
      (hc k hk').meromorphicOrderAt_nonneg
    have hnk : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
    have key : (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := by
      rw [show ((n - k : ℕ) : WithTop ℤ) = (((n - k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          show ((k : ℕ) : WithTop ℤ) = (((k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          ← WithTop.coe_mul, ← WithTop.coe_mul, ← WithTop.coe_add,
          ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe, hnk]
      have h1 : (1 : ℤ) ≤ (n : ℤ) - k := by omega
      nlinarith [h1, hrm]
    calc (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := key
      _ = 0 + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := (zero_add _).symm
      _ ≤ meromorphicOrderAt (c k) τ + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := by
          gcongr
  have hFn_ord : meromorphicOrderAt (F ^ n) τ = (↑(n * r) : WithTop ℤ) := by
    rw [meromorphicOrderAt_pow hF.meromorphicAt, ← hr]; push_cast; ring_nf
  have hlt2 : meromorphicOrderAt (F ^ n) τ < meromorphicOrderAt S τ := by
    rw [hFn_ord]
    refine lt_of_lt_of_le ?_ hsum_ord
    exact_mod_cast lt_add_one (n * r)
  have heq : meromorphicOrderAt (F ^ n + S) τ = meromorphicOrderAt (F ^ n) τ :=
    meromorphicOrderAt_add_eq_left_of_lt
      (MeromorphicAt.sum (fun i hi ↦ hMerS i hi)) hlt2
  have hzero : (F ^ n + S) =ᶠ[𝓝[≠] τ] 0 :=
    hrel.filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt (F ^ n + S) τ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]; exact hzero
  rw [heq, hFn_ord] at htop
  exact WithTop.coe_ne_top htop

open WithTop.LinearOrderedAddCommGroup in
private theorem meromorphicOrderAt_div_nonneg_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    0 ≤ meromorphicOrderAt (F / G) τ := by
  have hle := meromorphicOrderAt_le_of_monicRel hF hG hGord hc hrel
  rw [meromorphicOrderAt_div hF.meromorphicAt hG.meromorphicAt,
      ← LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hGord]
  exact (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top hGord).mpr hle

end ValuationEngine

end Aux

open Aux in
open Filter in
/-- Let `U` be open and preconnected, let `F`, `G` and `c k` (`k < n`) be analytic on `U`, with `G`
not identically zero on `U`. If `F ^ n + ∑_{k < n} c k G ^ (n - k) F ^ k = 0` on `U`, then `F =
G H` on `U` for some `H` analytic on `U`. -/
public theorem _root_.AnalyticOnNhd.exists_div_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {U : Set 𝕜} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ}
    (hF : AnalyticOnNhd 𝕜 F U) (hG : AnalyticOnNhd 𝕜 G U) (hG0 : ∃ z ∈ U, G z ≠ 0)
    (hc : ∀ k < n, AnalyticOnNhd 𝕜 (c k) U)
    (hrel : Set.EqOn (F ^ n + ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) 0 U) :
    ∃ H : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 H U ∧ Set.EqOn F (G * H) U := by
  obtain ⟨τ₀, hτ₀U, hGτ₀⟩ := hG0
  have hGord0 : meromorphicOrderAt G τ₀ ≠ ⊤ := by
    have h0 := (hG τ₀ hτ₀U).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hGτ₀
    simp [h0]
  have hGord : ∀ τ ∈ U, meromorphicOrderAt G τ ≠ ⊤ := fun τ hτ ↦
    hG.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hUc hτ₀U hτ hGord0
  have hdiv_ord : ∀ τ ∈ U, 0 ≤ meromorphicOrderAt (F / G) τ := by
    intro τ hτ
    refine meromorphicOrderAt_div_nonneg_of_monicRel (hF τ hτ) (hG τ hτ) (hGord τ hτ)
      (fun k hk ↦ hc k hk τ hτ) ?_
    filter_upwards [hU.mem_nhds hτ] with z hz using hrel hz
  have hmer : MeromorphicOn (F / G) U :=
    fun τ hτ ↦ (hF τ hτ).meromorphicAt.div (hG τ hτ).meromorphicAt
  set H := toMeromorphicNFOn (F / G) U with hH
  have hHnf : MeromorphicNFOn H U := meromorphicNFOn_toMeromorphicNFOn (F / G) U
  have hHan : AnalyticOnNhd 𝕜 H U := by
    rw [← hHnf.divisor_nonneg_iff_analyticOnNhd]
    intro z
    by_cases hz : z ∈ U
    · simp only [MeromorphicOn.divisor_apply hHnf.meromorphicOn hz,
        Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
      rw [hH, meromorphicOrderAt_toMeromorphicNFOn hmer hz]
      exact WithTop.untop₀_nonneg.mpr (hdiv_ord z hz)
    · simp [hz]
  refine ⟨H, hHan, ?_⟩
  have hGHan : AnalyticOnNhd 𝕜 (G * H) U := hG.mul hHan
  have heq_near : F =ᶠ[𝓝 τ₀] G * H := by
    have hGopen : {z | G z ≠ 0} ∈ 𝓝 τ₀ :=
      (hG τ₀ hτ₀U).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hGτ₀)
    filter_upwards [hGopen, hU.mem_nhds hτ₀U] with z hGz hzU
    have hanalz : AnalyticAt 𝕜 (F / G) z := (hF z hzU).div (hG z hzU) hGz
    have : H z = (F / G) z := by
      rw [hH, toMeromorphicNFOn_eq_toMeromorphicNFAt hmer hzU,
          toMeromorphicNFAt_eq_self.mpr hanalz.meromorphicNFAt]
    simp only [Pi.mul_apply, this, Pi.div_apply]
    field_simp
  have hfreq : ∃ᶠ z in 𝓝[≠] τ₀, F z = (G * H) z := by
    refine (heq_near.filter_mono nhdsWithin_le_nhds).frequently
  exact fun τ hτ ↦ hF.eqOn_of_preconnected_of_frequently_eq hGHan hUc hτ₀U hfreq hτ

end

end AnalyticDivMonicRel

end FrickeFunctions
