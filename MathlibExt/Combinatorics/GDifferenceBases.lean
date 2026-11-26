/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Defs.Filter
public import MathlibExt.Combinatorics.Additive.GDifferenceBases
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Count
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import MathlibExt.Combinatorics.Additive.GDifferenceBasisScaling
import MathlibExt.NumberTheory.PrimeNumberTheorem

/-!
# Convergence of the normalized difference basis numbers

For `g ≥ 1`, the ratio `η_g(n) / √n` converges to a positive limit, answering Kravitz's
question. The proof follows Schmutz and Tait: with `L = liminf η_g(n) / √n`, a fixed good
index `v` and a prime `q` in `[√(n/v), (1+c)√(n/v)]` give, by the Singer scaling bound,
`η_g(n) / √n ≤ (1+c) η_g(v) / √v + o(1)`, forcing the full limit to be `L`. The prime
intervals come from the prime number theorem: `π((1+c)x) - π(x) → ∞` since
`(1+c)x / log((1+c)x) - x / log x → ∞`.
-/

namespace MetaMathlibExt

open Filter
open scoped Topology

/-- `x / log x → ∞`: invert `log x / x → 0` through positive values. -/
private theorem tendsto_id_div_log_atTop :
    Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, (0 : ℝ) < Real.log x / x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have hW : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩
  have hinv := hW.inv_tendsto_nhdsGT_zero
  have heq : (fun x : ℝ => Real.log x / x)⁻¹ =ᶠ[Filter.atTop]
      (fun x : ℝ => x / Real.log x) :=
    Filter.Eventually.of_forall fun x => inv_div _ _
  exact Filter.Tendsto.congr' heq hinv

/-- The bracket in the prime-difference lower bound tends to `(1-ε)(1+c) - (1+ε)`. -/
private theorem tendsto_primeGap_bracket (c ε L : ℝ) :
    Filter.Tendsto (fun x : ℝ => (1 - ε) * ((1 + c) - 1 / x) / (1 + L / Real.log x)
      - (1 + ε) / (1 - Real.log 2 / Real.log x))
      Filter.atTop (𝓝 ((1 - ε) * (1 + c) - (1 + ε))) := by
  have h1x : Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (𝓝 0) := by
    have h := tendsto_const_nhds.div_atTop (a := (1 : ℝ)) (f := fun _ : ℝ => (1 : ℝ))
      (g := id) (l := Filter.atTop) Filter.tendsto_id
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun x => rfl) h
  have hL : Filter.Tendsto (fun x : ℝ => L / Real.log x) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h2 : Filter.Tendsto (fun x : ℝ => Real.log 2 / Real.log x) Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hnum : Filter.Tendsto (fun x : ℝ => (1 + c) - 1 / x) Filter.atTop (𝓝 (1 + c)) := by
    simpa using tendsto_const_nhds.sub h1x
  have hden1 : Filter.Tendsto (fun x : ℝ => 1 + L / Real.log x) Filter.atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hL
  have hden2 : Filter.Tendsto (fun x : ℝ => 1 - Real.log 2 / Real.log x) Filter.atTop
      (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h2
  have hmul : Filter.Tendsto (fun x : ℝ => (1 - ε) * ((1 + c) - 1 / x)) Filter.atTop
      (𝓝 ((1 - ε) * (1 + c))) := by
    simpa using tendsto_const_nhds.mul hnum
  have hT1 : Filter.Tendsto (fun x : ℝ => (1 - ε) * ((1 + c) - 1 / x) / (1 + L / Real.log x))
      Filter.atTop (𝓝 ((1 - ε) * (1 + c))) := by
    have h := hmul.div hden1 (by norm_num)
    rw [div_one] at h
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun x => rfl) h
  have hconst : Filter.Tendsto (fun _ : ℝ => (1 + ε)) Filter.atTop (𝓝 (1 + ε)) :=
    tendsto_const_nhds
  have hT2 : Filter.Tendsto (fun x : ℝ => (1 + ε) / (1 - Real.log 2 / Real.log x))
      Filter.atTop (𝓝 (1 + ε)) := by
    have h := hconst.div hden2 (by norm_num)
    rw [div_one] at h
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun x => rfl) h
  have hC := hT1.sub hT2
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun x => rfl) hC

/-- The prime number theorem gives a prime in every `[x, (1+c)x]` for large `x`. -/
private theorem exists_prime_Icc_mul_self_of_large (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
      ∃ q : ℕ, q.Prime ∧ x ≤ (q : ℝ) ∧ (q : ℝ) ≤ (1 + c) * x := by
  set ε : ℝ := c / (2 * (2 + c)) with hε
  have h2c : (0 : ℝ) < 2 + c := by linarith
  have hε_pos : 0 < ε := by
    rw [hε]
    exact div_pos hc (mul_pos two_pos h2c)
  have hD : (1 - ε) * (1 + c) - (1 + ε) = c / 2 := by
    have hne : (2 : ℝ) * (2 + c) ≠ 0 := ne_of_gt (mul_pos two_pos h2c)
    rw [hε]
    field_simp
    ring
  set m : ℝ → ℕ := fun x => ⌊(1 + c) * x⌋₊ with hm_def
  set k : ℝ → ℕ := fun x => ⌊x⌋₊ with hk_def
  set L : ℝ := Real.log (1 + c) with hL_def
  have h1c : (0 : ℝ) < 1 + c := by linarith
  have hLpos : (0 : ℝ) < L := Real.log_pos (by linarith : (1 : ℝ) < 1 + c)
  have hε_le : ε ≤ 1 := by
    rw [hε, div_le_iff₀ (mul_pos two_pos h2c)]
    linarith
  have hm_top : Filter.Tendsto m Filter.atTop Filter.atTop := by
    have h := tendsto_nat_floor_atTop.comp
      (Filter.Tendsto.const_mul_atTop h1c Filter.tendsto_id)
    exact h
  have hk_top : Filter.Tendsto k Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop.comp Filter.tendsto_id
  have hPm :=
    MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem.comp_tendsto hm_top
  have hPk :=
    MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem.comp_tendsto hk_top
  have hne_m : ∀ᶠ x : ℝ in Filter.atTop,
      (((fun n : ℕ => (n : ℝ) / Real.log n) ∘ m) x) ≠ 0 := by
    filter_upwards [hm_top.eventually (Filter.eventually_ge_atTop 3)] with x hx
    have hpos : (0 : ℝ) < (m x : ℝ) := by exact_mod_cast (by omega : 0 < m x)
    have hm1 : (1 : ℝ) < (m x : ℝ) := by exact_mod_cast (by omega : 1 < m x)
    simp only [Function.comp_apply]
    exact ne_of_gt (div_pos hpos (Real.log_pos hm1))
  have hne_k : ∀ᶠ x : ℝ in Filter.atTop,
      (((fun n : ℕ => (n : ℝ) / Real.log n) ∘ k) x) ≠ 0 := by
    filter_upwards [hk_top.eventually (Filter.eventually_ge_atTop 3)] with x hx
    have hpos : (0 : ℝ) < (k x : ℝ) := by exact_mod_cast (by omega : 0 < k x)
    have hk1 : (1 : ℝ) < (k x : ℝ) := by exact_mod_cast (by omega : 1 < k x)
    simp only [Function.comp_apply]
    exact ne_of_gt (div_pos hpos (Real.log_pos hk1))
  have hRm : Filter.Tendsto
      (fun x : ℝ => (Nat.primeCounting (m x) : ℝ) / ((m x : ℝ) / Real.log (m x)))
      Filter.atTop (𝓝 1) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun x => rfl)
      ((Asymptotics.isEquivalent_iff_tendsto_one hne_m).mp hPm)
  have hRk : Filter.Tendsto
      (fun x : ℝ => (Nat.primeCounting (k x) : ℝ) / ((k x : ℝ) / Real.log (k x)))
      Filter.atTop (𝓝 1) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun x => rfl)
      ((Asymptotics.isEquivalent_iff_tendsto_one hne_k).mp hPk)
  have hb_m_lo : ∀ᶠ x : ℝ in Filter.atTop,
      (1 - ε) < (Nat.primeCounting (m x) : ℝ) / ((m x : ℝ) / Real.log (m x)) :=
    hRm.eventually (lt_mem_nhds (by linarith : (1 : ℝ) - ε < 1))
  have hb_k_hi : ∀ᶠ x : ℝ in Filter.atTop,
      (Nat.primeCounting (k x) : ℝ) / ((k x : ℝ) / Real.log (k x)) < (1 + ε) :=
    hRk.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))
  have hDpos_m : ∀ᶠ x : ℝ in Filter.atTop, (0 : ℝ) < (m x : ℝ) / Real.log (m x) := by
    filter_upwards [hm_top.eventually (Filter.eventually_ge_atTop 3)] with x hx
    have hpos : (0 : ℝ) < (m x : ℝ) := by exact_mod_cast (by omega : 0 < m x)
    have hm1 : (1 : ℝ) < (m x : ℝ) := by exact_mod_cast (by omega : 1 < m x)
    exact div_pos hpos (Real.log_pos hm1)
  have hDpos_k : ∀ᶠ x : ℝ in Filter.atTop, (0 : ℝ) < (k x : ℝ) / Real.log (k x) := by
    filter_upwards [hk_top.eventually (Filter.eventually_ge_atTop 3)] with x hx
    have hpos : (0 : ℝ) < (k x : ℝ) := by exact_mod_cast (by omega : 0 < k x)
    have hk1 : (1 : ℝ) < (k x : ℝ) := by exact_mod_cast (by omega : 1 < k x)
    exact div_pos hpos (Real.log_pos hk1)
  have hC : Filter.Tendsto (fun x : ℝ => (1 - ε) * ((1 + c) - 1 / x) / (1 + L / Real.log x)
      - (1 + ε) / (1 - Real.log 2 / Real.log x)) Filter.atTop (𝓝 (c / 2)) := by
    have h := tendsto_primeGap_bracket c ε L
    rw [hD] at h
    exact h
  have hCge : ∀ᶠ x : ℝ in Filter.atTop, c / 4 <
      (1 - ε) * ((1 + c) - 1 / x) / (1 + L / Real.log x)
        - (1 + ε) / (1 - Real.log 2 / Real.log x) :=
    hC.eventually (lt_mem_nhds (by linarith : c / 4 < c / 2))
  have hBeq : ∀ᶠ x : ℝ in Filter.atTop,
      (1 - ε) * (((1 + c) * x - 1) / (Real.log x + L))
        - (1 + ε) * (x / (Real.log x - Real.log 2))
        = (x / Real.log x) * ((1 - ε) * ((1 + c) - 1 / x) / (1 + L / Real.log x)
          - (1 + ε) / (1 - Real.log 2 / Real.log x)) := by
    filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with x hx2
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    have n1 : (x : ℝ) ≠ 0 := ne_of_gt hx0
    have n2 : Real.log x ≠ 0 := ne_of_gt hlogx
    have n3 : Real.log x + L ≠ 0 := ne_of_gt (by linarith)
    have hpos4 : (0 : ℝ) < Real.log x - Real.log 2 := by
      have e : Real.log x - Real.log 2 = Real.log (x / 2) :=
        (Real.log_div n1 (by norm_num)).symm
      rw [e]
      exact Real.log_pos (by linarith : (1 : ℝ) < x / 2)
    have n4 : Real.log x - Real.log 2 ≠ 0 := ne_of_gt hpos4
    have n5 : (1 : ℝ) + L / Real.log x ≠ 0 := by
      apply ne_of_gt
      have hposL : (0 : ℝ) < L / Real.log x := div_pos hLpos hlogx
      linarith
    have n6 : (1 : ℝ) - Real.log 2 / Real.log x ≠ 0 := by
      have e2 : (1 : ℝ) - Real.log 2 / Real.log x
          = (Real.log x - Real.log 2) / Real.log x := by
        rw [sub_div, div_self n2]
      rw [e2]
      exact ne_of_gt (div_pos hpos4 hlogx)
    field_simp
  have hbig : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ (c / 4) * (x / Real.log x) :=
    (Filter.Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < c / 4)
      tendsto_id_div_log_atTop).eventually (Filter.eventually_ge_atTop 1)
  have hxx : ∀ᶠ x : ℝ in Filter.atTop, (0 : ℝ) ≤ x / Real.log x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (le_of_lt (by linarith)) (le_of_lt (Real.log_pos hx))
  have hmain : ∀ᶠ x : ℝ in Filter.atTop,
      ∃ q : ℕ, q.Prime ∧ x ≤ (q : ℝ) ∧ (q : ℝ) ≤ (1 + c) * x := by
    filter_upwards [hb_m_lo, hb_k_hi, hDpos_m, hDpos_k,
      hm_top.eventually (Filter.eventually_ge_atTop 3),
      hk_top.eventually (Filter.eventually_ge_atTop 3),
      Filter.eventually_ge_atTop (4 : ℝ), hCge, hBeq, hbig, hxx] with x hlo hhi hDm hDk
      hm3 hk3 hx4 hCge_x hBeq_x hbig_x hxx_x
    have hx0 : (0 : ℝ) < x := by linarith
    have hpos_m : (0 : ℝ) < (m x : ℝ) := by exact_mod_cast (by omega : 0 < m x)
    have hm1 : (1 : ℝ) < (m x : ℝ) := by exact_mod_cast (by omega : 1 < m x)
    have hlogm_pos : (0 : ℝ) < Real.log (m x) := Real.log_pos hm1
    have hpos_k : (0 : ℝ) < (k x : ℝ) := by exact_mod_cast (by omega : 0 < k x)
    have hk1 : (1 : ℝ) < (k x : ℝ) := by exact_mod_cast (by omega : 1 < k x)
    have hlogk_pos : (0 : ℝ) < Real.log (k x) := Real.log_pos hk1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
    have hm_le : (m x : ℝ) ≤ (1 + c) * x := by
      simp only [hm_def]
      exact Nat.floor_le (mul_nonneg (le_of_lt h1c) (le_of_lt hx0))
    have hm_gt : (1 + c) * x - 1 < (m x : ℝ) := by
      have h := Nat.lt_floor_add_one ((1 + c) * x)
      simp only [hm_def]
      linarith [h]
    have hk_le : (k x : ℝ) ≤ x := by
      simp only [hk_def]
      exact Nat.floor_le (le_of_lt hx0)
    have hk_ge : x / 2 ≤ (k x : ℝ) := by
      have h := Nat.lt_floor_add_one x
      simp only [hk_def]
      linarith [h, hx4]
    have hkm : k x ≤ m x := by
      have hle : (k x : ℝ) ≤ (1 + c) * x :=
        hk_le.trans (le_mul_of_one_le_left (le_of_lt hx0) (by linarith : (1 : ℝ) ≤ 1 + c))
      simpa [hm_def] using Nat.le_floor hle
    have hlogm : Real.log (m x) ≤ Real.log x + L := by
      have h1 : Real.log (m x) ≤ Real.log ((1 + c) * x) :=
        Real.log_le_log hpos_m hm_le
      have h2 : Real.log ((1 + c) * x) = Real.log (1 + c) + Real.log x :=
        Real.log_mul (ne_of_gt h1c) (ne_of_gt hx0)
      simp only [hL_def]
      linarith [h1, h2]
    have hlogk : Real.log x - Real.log 2 ≤ Real.log (k x) := by
      have h1 : Real.log (x / 2) ≤ Real.log (k x) :=
        Real.log_le_log (by linarith) hk_ge
      have h2 : Real.log (x / 2) = Real.log x - Real.log 2 :=
        Real.log_div (ne_of_gt hx0) (by norm_num)
      linarith [h1, h2]
    have e1 : (1 - ε) * ((m x : ℝ) / Real.log (m x))
        < (Nat.primeCounting (m x) : ℝ) :=
      (lt_div_iff₀ hDm).mp hlo
    have e2 : (Nat.primeCounting (k x) : ℝ)
        < (1 + ε) * ((k x : ℝ) / Real.log (k x)) :=
      (div_lt_iff₀ hDk).mp hhi
    have e3 : ((1 + c) * x - 1) / (Real.log x + L)
        ≤ (m x : ℝ) / Real.log (m x) := by
      have s1 : ((1 + c) * x - 1) / (Real.log x + L)
          ≤ (m x : ℝ) / (Real.log x + L) :=
        div_le_div_of_nonneg_right hm_gt.le (le_of_lt (add_pos hlogx hLpos))
      have s2 : (m x : ℝ) / (Real.log x + L) ≤ (m x : ℝ) / Real.log (m x) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlogm_pos hlogm
      exact s1.trans s2
    have hden2 : (0 : ℝ) < Real.log x - Real.log 2 := by
      have e : Real.log x - Real.log 2 = Real.log (x / 2) :=
        (Real.log_div (ne_of_gt hx0) (by norm_num)).symm
      rw [e]
      exact Real.log_pos (by linarith : (1 : ℝ) < x / 2)
    have e4 : (k x : ℝ) / Real.log (k x) ≤ x / (Real.log x - Real.log 2) := by
      have t1 : (k x : ℝ) / Real.log (k x) ≤ x / Real.log (k x) :=
        div_le_div_of_nonneg_right hk_le (le_of_lt hlogk_pos)
      have t2 : x / Real.log (k x) ≤ x / (Real.log x - Real.log 2) :=
        div_le_div_of_nonneg_left (le_of_lt hx0) hden2 hlogk
      exact t1.trans t2
    have h1ε : (0 : ℝ) ≤ 1 - ε := sub_nonneg.mpr hε_le
    have h1ε' : (0 : ℝ) < 1 + ε := by linarith
    have u1 : (1 - ε) * (((1 + c) * x - 1) / (Real.log x + L))
        ≤ (1 - ε) * ((m x : ℝ) / Real.log (m x)) :=
      mul_le_mul_of_nonneg_left e3 h1ε
    have u2 : (1 + ε) * ((k x : ℝ) / Real.log (k x))
        ≤ (1 + ε) * (x / (Real.log x - Real.log 2)) :=
      mul_le_mul_of_nonneg_left e4 (le_of_lt h1ε')
    have hB_le : (1 - ε) * (((1 + c) * x - 1) / (Real.log x + L))
          - (1 + ε) * (x / (Real.log x - Real.log 2))
          ≤ (1 - ε) * ((m x : ℝ) / Real.log (m x))
            - (1 + ε) * ((k x : ℝ) / Real.log (k x)) :=
      sub_le_sub u1 u2
    have hdiff : (1 - ε) * (((1 + c) * x - 1) / (Real.log x + L))
          - (1 + ε) * (x / (Real.log x - Real.log 2))
          < (Nat.primeCounting (m x) : ℝ) - (Nat.primeCounting (k x) : ℝ) :=
      lt_of_le_of_lt hB_le (sub_lt_sub e1 e2)
    have hle : (x / Real.log x) * (c / 4)
        ≤ (x / Real.log x) * ((1 - ε) * ((1 + c) - 1 / x) / (1 + L / Real.log x)
          - (1 + ε) / (1 - Real.log 2 / Real.log x)) :=
      mul_le_mul_of_nonneg_left (le_of_lt hCge_x) hxx_x
    have heq2 : (x / Real.log x) * (c / 4) = (c / 4) * (x / Real.log x) :=
      mul_comm _ _
    have hBone : (1 : ℝ) ≤ (1 - ε) * (((1 + c) * x - 1) / (Real.log x + L))
        - (1 + ε) * (x / (Real.log x - Real.log 2)) := by
      rw [hBeq_x]
      linarith [hbig_x, hle, heq2]
    have hreal : (Nat.primeCounting (k x) : ℝ) < Nat.primeCounting (m x) := by
      linarith [hBone, hdiff]
    have hlt : Nat.primeCounting (k x) < Nat.primeCounting (m x) := by
      exact_mod_cast hreal
    have hcard_k : (Nat.primesLE (k x)).card = Nat.primeCounting (k x) := by
      rw [Nat.primesLE_eq_filter_range]
      exact (Nat.count_eq_card_filter_range Nat.Prime (k x + 1)).symm
    have hcard_m : (Nat.primesLE (m x)).card = Nat.primeCounting (m x) := by
      rw [Nat.primesLE_eq_filter_range]
      exact (Nat.count_eq_card_filter_range Nat.Prime (m x + 1)).symm
    have hsub : Nat.primesLE (k x) ⊆ Nat.primesLE (m x) := by
      intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨hp.1.trans hkm, hp.2⟩
    have hcardlt : (Nat.primesLE (k x)).card < (Nat.primesLE (m x)).card := by
      rw [hcard_k, hcard_m]
      exact hlt
    obtain ⟨q, hqt, hqs⟩ : ∃ q ∈ Nat.primesLE (m x), q ∉ Nat.primesLE (k x) := by
      by_contra hcon
      have hss : Nat.primesLE (m x) ⊆ Nat.primesLE (k x) := by
        intro q hq
        by_contra hc
        exact hcon ⟨q, hq, hc⟩
      have hle := Finset.card_le_card hss
      omega
    obtain ⟨hqm, hqprime⟩ := Nat.mem_primesLE.mp hqt
    have hqk : k x < q := by
      by_contra hcon
      exact hqs (Nat.mem_primesLE.mpr ⟨not_lt.mp hcon, hqprime⟩)
    have hfl : x < (k x : ℝ) + 1 := Nat.lt_floor_add_one x
    have hqk1 : (k x : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast (by omega : k x + 1 ≤ q)
    have hxq : x ≤ (q : ℝ) := by linarith
    have hqx : (q : ℝ) ≤ (1 + c) * x := (Nat.cast_le.mpr hqm).trans hm_le
    exact ⟨q, hqprime, hxq, hqx⟩
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hmain
  exact ⟨X₀, fun x hx => hX₀ x hx⟩

@[expose] public section

/-- **Kravitz's question: the normalized difference basis numbers converge.** For a finite set
$A$ of integers and an integer $x$, write $r_{A-A}(x)$ for the number of ordered pairs
$(a, a') \in A \times A$ with $a - a' = x$. For every integer $g \ge 1$, let $\eta_g(n)$ be the
least size of a finite set $A$ of integers with $r_{A-A}(x) \ge g$ for every integer
$x \in [1, n]$. Then there is a real number $c > 0$ with $\eta_g(n) / \sqrt{n} \to c$ as
$n \to \infty$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 1 (`integers-2025-A77-thm-1`). -/
public theorem tendsto_diffBasisNumber_div_sqrt (g : ℕ) (hg : 0 < g) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n) atTop (𝓝 c)
    := by
  have h_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ (diffBasisNumber g n : ℝ) / Real.sqrt n := by
    intro n
    exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have h_upper : ∀ n : ℕ, (diffBasisNumber g n : ℝ) / Real.sqrt n ≤ 4 * (g : ℝ) := by
    intro n
    have hcor := diffBasisNumber_div_sqrt_le g n
    by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero, Real.sqrt_zero, div_zero]
      positivity
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
        have h := Real.sqrt_le_sqrt hnR
        rw [Real.sqrt_one] at h
        exact h
      have hrec : (1 : ℝ) / Real.sqrt n ≤ 1 := by
        have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hsqrt1
        simpa using h
      have h2 : 2 * (1 + 1 / Real.sqrt (n : ℝ)) ≤ 4 := by linarith [hrec]
      have hle : 2 * (1 + 1 / Real.sqrt (n : ℝ)) * (g : ℝ) ≤ 4 * (g : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
      exact hcor.trans hle
  have h_lower : ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt (2 * (g : ℝ)) ≤ (diffBasisNumber g n : ℝ) / Real.sqrt n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    exact sqrt_two_mul_le_diffBasisNumber_div_sqrt g n hn
  have B_le : Filter.atTop.IsBoundedUnder (· ≤ ·)
      (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall (fun n => h_upper n))
  have B_ge : Filter.atTop.IsBoundedUnder (· ≥ ·)
      (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (fun n => h_nonneg n))
  set L : ℝ := Filter.liminf (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n)
    Filter.atTop with hL_def
  have hL_ge : Real.sqrt (2 * (g : ℝ)) ≤ L :=
    Filter.le_liminf_of_le B_le.isCoboundedUnder_ge h_lower
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hL_pos : (0 : ℝ) < L := by
    have hsqrt : (0 : ℝ) < Real.sqrt (2 * (g : ℝ)) :=
      Real.sqrt_pos.2 (mul_pos two_pos hgR)
    exact lt_of_lt_of_le hsqrt hL_ge
  have h_low : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      L - ε < (diffBasisNumber g n : ℝ) / Real.sqrt n := by
    intro ε hε
    exact Filter.eventually_lt_of_lt_liminf (sub_lt_self L hε) B_ge
  have h_up : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      (diffBasisNumber g n : ℝ) / Real.sqrt n < L + ε := by
    intro ε hε
    obtain ⟨v, hv1, hav⟩ : ∃ v : ℕ, 1 < v ∧
        (diffBasisNumber g v : ℝ) / Real.sqrt v < L + ε / 2 := by
      by_contra hcon
      push Not at hcon
      have hev : ∀ᶠ v : ℕ in Filter.atTop,
          L + ε / 2 ≤ (diffBasisNumber g v : ℝ) / Real.sqrt v := by
        filter_upwards [Filter.eventually_gt_atTop 1] with v hv
        exact hcon v hv
      have hle : L + ε / 2 ≤ L :=
        Filter.le_liminf_of_le B_le.isCoboundedUnder_ge hev
      linarith
    set cc : ℝ := ε / (4 * (L + ε)) with hcc
    have hLε : (0 : ℝ) < L + ε := by linarith
    have hcc_pos : (0 : ℝ) < cc := by
      rw [hcc]
      exact div_pos hε (mul_pos (by norm_num) hLε)
    obtain ⟨X₀, hX₀⟩ := exists_prime_Icc_mul_self_of_large cc hcc_pos
    set E : ℝ := (diffBasisNumber g v : ℝ) with hE_def
    have hE_nonneg : (0 : ℝ) ≤ E := by
      rw [hE_def]
      exact Nat.cast_nonneg _
    set N0 : ℕ := max 2 (max ⌈X₀ ^ 2 * (v : ℝ)⌉₊ (⌈(4 * E / ε) ^ 2⌉₊ + 1)) with hN0
    have hN0_ge2 : 2 ≤ N0 := by
      rw [hN0]
      exact le_max_left _ _
    have hN0_ceil1 : ⌈X₀ ^ 2 * (v : ℝ)⌉₊ ≤ N0 := by
      rw [hN0]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hN0_ceil2 : ⌈(4 * E / ε) ^ 2⌉₊ + 1 ≤ N0 := by
      rw [hN0]
      exact (le_max_right _ _).trans (le_max_right _ _)
    filter_upwards [Filter.eventually_ge_atTop N0] with n hn
    have hn2 : 2 ≤ n := hN0_ge2.trans hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hsqrt_n : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn_pos
    have hv_pos : (0 : ℝ) < (v : ℝ) := by exact_mod_cast (by omega : 0 < v)
    have hsqrt_v : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.2 hv_pos
    have hNv : X₀ ^ 2 * (v : ℝ) ≤ (N0 : ℝ) :=
      (Nat.le_ceil (X₀ ^ 2 * (v : ℝ))).trans (Nat.cast_le.mpr hN0_ceil1)
    have hnx : X₀ ≤ Real.sqrt ((n : ℝ) / (v : ℝ)) := by
      have h2 : X₀ ^ 2 * (v : ℝ) ≤ (n : ℝ) := hNv.trans (Nat.cast_le.mpr hn)
      have h1 : X₀ ^ 2 ≤ (n : ℝ) / (v : ℝ) := by
        rw [le_div_iff₀ hv_pos]
        exact h2
      have h3 : Real.sqrt (X₀ ^ 2) ≤ Real.sqrt ((n : ℝ) / (v : ℝ)) :=
        Real.sqrt_le_sqrt h1
      have h4 : Real.sqrt (X₀ ^ 2) = |X₀| := Real.sqrt_sq_eq_abs _
      rw [h4] at h3
      exact le_trans (le_abs_self _) h3
    obtain ⟨q, hq_prime, hxq, hqx⟩ := hX₀ _ hnx
    have hnqv : n ≤ q ^ 2 * v := by
      have hnpos : (0 : ℝ) ≤ (n : ℝ) / (v : ℝ) :=
        div_nonneg (le_of_lt hn_pos) (le_of_lt hv_pos)
      have hsq : (Real.sqrt ((n : ℝ) / (v : ℝ))) ^ 2 ≤ (q : ℝ) ^ 2 := by
        have hmul := mul_le_mul hxq hxq (Real.sqrt_nonneg _)
          (le_trans (Real.sqrt_nonneg _) hxq)
        rw [pow_two, pow_two]
        exact hmul
      rw [Real.sq_sqrt hnpos] at hsq
      have hvn : (v : ℝ) ≠ 0 := ne_of_gt hv_pos
      have h1 : (n : ℝ) = ((n : ℝ) / (v : ℝ)) * (v : ℝ) :=
        (div_mul_cancel₀ _ hvn).symm
      have h2 : ((n : ℝ) / (v : ℝ)) * (v : ℝ) ≤ (q : ℝ) ^ 2 * (v : ℝ) :=
        mul_le_mul_of_nonneg_right hsq (le_of_lt hv_pos)
      have h3 : ((q ^ 2 * v : ℕ) : ℝ) = (q : ℝ) ^ 2 * (v : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_pow]
      have hcast : (n : ℝ) ≤ ((q ^ 2 * v : ℕ) : ℝ) := by
        rw [h1, h3]
        exact h2
      exact_mod_cast hcast
    have hcor := diffBasisNumber_le_succ_mul g q n v hq_prime hnqv
    have hcorR : (diffBasisNumber g n : ℝ) ≤ ((q : ℝ) + 1) * E := by
      have h : (diffBasisNumber g n : ℝ) ≤ (((q + 1) * diffBasisNumber g v : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcor
      push_cast at h
      simp only [hE_def]
      exact h
    have hsimp : (((q : ℝ) + 1) * E) / Real.sqrt n
        = (q : ℝ) * E / Real.sqrt n + E / Real.sqrt n := by
      rw [add_mul, one_mul, add_div]
    have hsqrt_div : Real.sqrt ((n : ℝ) / (v : ℝ))
        = Real.sqrt n / Real.sqrt v :=
      Real.sqrt_div (le_of_lt hn_pos) _
    have hqE : (q : ℝ) * E / Real.sqrt n
        ≤ (1 + cc) * ((diffBasisNumber g v : ℝ) / Real.sqrt v) := by
      have h1 : (q : ℝ) * E / Real.sqrt n
          ≤ ((1 + cc) * Real.sqrt ((n : ℝ) / (v : ℝ))) * E / Real.sqrt n := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hsqrt_n)
        exact mul_le_mul_of_nonneg_right hqx hE_nonneg
      have h2 : ((1 + cc) * Real.sqrt ((n : ℝ) / (v : ℝ))) * E / Real.sqrt n
          = (1 + cc) * (E / Real.sqrt v) := by
        rw [hsqrt_div]
        have hn0 : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_n
        have hv0 : Real.sqrt (v : ℝ) ≠ 0 := ne_of_gt hsqrt_v
        field_simp
      rw [h2] at h1
      simpa [hE_def] using h1
    have hN0_3 : (4 * E / ε) ^ 2 < (N0 : ℝ) := by
      have h1 : (4 * E / ε) ^ 2 ≤ (⌈(4 * E / ε) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈(4 * E / ε) ^ 2⌉₊ : ℝ) < (⌈(4 * E / ε) ^ 2⌉₊ : ℝ) + 1 :=
        lt_add_one _
      have h3 : (⌈(4 * E / ε) ^ 2⌉₊ : ℝ) + 1 ≤ (N0 : ℝ) := by
        exact_mod_cast hN0_ceil2
      linarith [h1, h2, h3]
    have hEv : E / Real.sqrt n < ε / 4 := by
      have hNn : (N0 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      have hsqN : (4 * E / ε) ^ 2 < (n : ℝ) := hN0_3.trans_le hNn
      have h4E : (0 : ℝ) ≤ 4 * E / ε :=
        div_nonneg (mul_nonneg (by norm_num) hE_nonneg) (le_of_lt hε)
      have hlt : 4 * E / ε < Real.sqrt n := by
        by_contra hcon
        push Not at hcon
        have hsq_le : Real.sqrt n * Real.sqrt n ≤ (4 * E / ε) * (4 * E / ε) :=
          mul_le_mul hcon hcon (Real.sqrt_nonneg _) (le_trans (Real.sqrt_nonneg _) hcon)
        have hn_eq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt (le_of_lt hn_pos)
        rw [hn_eq, ← pow_two] at hsq_le
        linarith [hsqN, hsq_le]
      have hε0 : (ε : ℝ) ≠ 0 := ne_of_gt hε
      have hEE : (ε / 4) * (4 * E / ε) = E := by
        field_simp
      have hElt : E < (ε / 4) * Real.sqrt n := by
        rw [← hEE]
        exact mul_lt_mul_of_pos_left hlt (by linarith : (0 : ℝ) < ε / 4)
      exact (div_lt_iff₀ hsqrt_n).mpr hElt
    have hmain_le : (diffBasisNumber g n : ℝ) / Real.sqrt n
        ≤ (1 + cc) * ((diffBasisNumber g v : ℝ) / Real.sqrt v) + ε / 4 := by
      have hdiv : (diffBasisNumber g n : ℝ) / Real.sqrt n
          ≤ (((q : ℝ) + 1) * E) / Real.sqrt n :=
        div_le_div_of_nonneg_right hcorR (le_of_lt hsqrt_n)
      rw [hsimp] at hdiv
      exact hdiv.trans (add_le_add hqE (le_of_lt hEv))
    have hcc_bound : cc * (L + ε / 2) ≤ ε / 4 := by
      have hpos : (0 : ℝ) < 4 * (L + ε) := mul_pos (by norm_num) hLε
      rw [hcc, div_mul_eq_mul_div, div_le_iff₀ hpos]
      have he : (ε / 4) * (4 * (L + ε)) = ε * (L + ε) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hε)
    have hfinal : (diffBasisNumber g n : ℝ) / Real.sqrt n < L + ε := by
      have h1 : (1 + cc) * ((diffBasisNumber g v : ℝ) / Real.sqrt v)
          < (1 + cc) * (L + ε / 2) :=
        mul_lt_mul_of_pos_left hav (by linarith : (0 : ℝ) < 1 + cc)
      have h2 : (1 + cc) * (L + ε / 2) + ε / 4 ≤ L + ε := by
        have e : (1 + cc) * (L + ε / 2) = (L + ε / 2) + cc * (L + ε / 2) := by ring
        rw [e]
        linarith [hcc_bound]
      have h3 : (1 + cc) * ((diffBasisNumber g v : ℝ) / Real.sqrt v) + ε / 4
          < L + ε := by
        linarith [h1, h2]
      exact lt_of_le_of_lt hmain_le h3
    exact hfinal
  have h_tendsto : Filter.Tendsto
      (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n)
      Filter.atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((h_low ε hε).and (h_up ε hε))
    exact ⟨N, fun n hn => by
      have hlo := (hN n hn).1
      have hhi := (hN n hn).2
      rw [Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  exact ⟨L, hL_pos, h_tendsto⟩

end

end MetaMathlibExt
