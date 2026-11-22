/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Internal rate of return of a conventional project

A conventional project, an initial outlay followed by nonnegative cash flows at least one of which
is positive, has exactly one internal rate of return above `-1`.

## i. Overview

`npv c N r = ∑ k ∈ range (N + 1), c k / (1 + r) ^ k`; an internal rate of return is a rate
`r > -1` with zero net present value. With nonnegative later flows, at least one positive, the net
present value is strictly decreasing on `(-1, ∞)`; it is negative for large rates and positive near
`-1` when `c 0 < 0`, so the intermediate value theorem gives a root and strict monotonicity gives
uniqueness. Without the sign pattern a project can have several internal rates (see the tests).

## ii. Main results

* `MathlibExt.Economics.Finance.InternalRateOfReturn.strictAntiOn_npv`
* `MathlibExt.Economics.Finance.InternalRateOfReturn.existsUnique_isIRR`

## iii. References

* OpenStax, *Principles of Finance*, ch. 16 (net present value and internal rate of return).
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.InternalRateOfReturn

/-- Net present value at rate `r` of the dated cash flows `c 0, c 1, …, c N` (`c k` arrives at
the end of period `k`; `c 0` is today): `∑ k ∈ range (N + 1), c k / (1 + r) ^ k`. Meaningful
for `r > -1`. -/
noncomputable def npv (c : ℕ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), c k / (1 + r) ^ k

/-- `r` is an internal rate of return of the cash flows `c 0, …, c N`: a rate above `-1` at
which the net present value is zero. -/
def IsIRR (c : ℕ → ℝ) (N : ℕ) (r : ℝ) : Prop :=
  -1 < r ∧ npv c N r = 0

/-- With nonnegative later cash flows, at least one positive, the NPV is strictly decreasing in
the rate on `(-1, ∞)`. -/
theorem strictAntiOn_npv {c : ℕ → ℝ} {N : ℕ} (hnn : ∀ k ∈ Finset.Icc 1 N, 0 ≤ c k)
    (hpos : ∃ k ∈ Finset.Icc 1 N, 0 < c k) : StrictAntiOn (npv c N) (Set.Ioi (-1)) := by
  obtain ⟨j, hjmem, hjpos⟩ := hpos
  rw [Finset.mem_Icc] at hjmem
  obtain ⟨hj1, hjN⟩ := hjmem
  intro r hr s hs hrs
  rw [Set.mem_Ioi] at hr hs
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hlt : (1 : ℝ) + r < 1 + s := by linarith
  have hjrange : j ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range]
    omega
  have hjne : j ≠ 0 := by omega
  have hle : ∀ k ∈ Finset.range (N + 1), c k / (1 + s) ^ k ≤ c k / (1 + r) ^ k := by
    intro k hk
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · have hkN : k ≤ N := by
        rw [Finset.mem_range] at hk
        omega
      have hk1 : 1 ≤ k := by omega
      have hck : 0 ≤ c k := hnn k (Finset.mem_Icc.mpr ⟨hk1, hkN⟩)
      have hpow : (1 + r) ^ k ≤ (1 + s) ^ k := pow_le_pow_left₀ h1r.le hlt.le k
      rw [div_eq_mul_one_div (c k) ((1 + s) ^ k), div_eq_mul_one_div (c k) ((1 + r) ^ k)]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (pow_pos h1r k) hpow) hck
  have hltj : c j / (1 + s) ^ j < c j / (1 + r) ^ j := by
    have hpow : (1 + r) ^ j < (1 + s) ^ j := pow_lt_pow_left₀ hlt h1r.le hjne
    rw [div_eq_mul_one_div (c j) ((1 + s) ^ j), div_eq_mul_one_div (c j) ((1 + r) ^ j)]
    exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt (pow_pos h1r j) hpow) hjpos
  unfold npv
  exact Finset.sum_lt_sum hle ⟨j, hjrange, hltj⟩

/-- **A conventional project has a unique IRR.** If `c 0 < 0`, every later flow `c k`
(`1 ≤ k ≤ N`) is nonnegative and at least one is positive, there is exactly one internal rate of
return. -/
theorem existsUnique_isIRR {c : ℕ → ℝ} {N : ℕ} (h0 : c 0 < 0)
    (hnn : ∀ k ∈ Finset.Icc 1 N, 0 ≤ c k) (hpos : ∃ k ∈ Finset.Icc 1 N, 0 < c k) :
    ∃! r, IsIRR c N r := by
  have hanti : StrictAntiOn (npv c N) (Set.Ioi (-1)) := strictAntiOn_npv hnn hpos
  obtain ⟨j, hjmem, hjpos⟩ := hpos
  rw [Finset.mem_Icc] at hjmem
  obtain ⟨hj1, hjN⟩ := hjmem
  have hc0 : (0 : ℝ) < -c 0 := by linarith
  have hnpv : ∀ r : ℝ, npv c N r
      = c 0 + ∑ k ∈ Finset.range N, c (k + 1) / (1 + r) ^ (k + 1) := by
    intro r
    unfold npv
    simp only [Finset.sum_range_succ', pow_zero, div_one]
    exact add_comm _ _
  have htermnn : ∀ r : ℝ, -1 < r → ∀ i ∈ Finset.range N,
      0 ≤ c (i + 1) / (1 + r) ^ (i + 1) := by
    intro r hr i hi
    have h1r : (0 : ℝ) < 1 + r := by linarith
    rw [Finset.mem_range] at hi
    exact div_nonneg (hnn _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
      (le_of_lt (pow_pos h1r _))
  have hcont : ∀ a b : ℝ, -1 < a → ContinuousOn (npv c N) (Set.Icc a b) := by
    intro a b ha
    unfold npv
    apply continuousOn_finsetSum
    intro k hk
    show ContinuousOn (fun r : ℝ => c k / (1 + r) ^ k) (Set.Icc a b)
    have h1 : Continuous (fun r : ℝ => (1 : ℝ) + r) := continuous_const.add continuous_id
    have hden : Continuous (fun r : ℝ => (1 + r) ^ k) := h1.pow k
    have hnum : ContinuousOn (fun _ : ℝ => c k) (Set.Icc a b) := continuous_const.continuousOn
    have hne : ∀ x ∈ Set.Icc a b, (1 + x) ^ k ≠ 0 := by
      intro x hx
      rw [Set.mem_Icc] at hx
      obtain ⟨hax, -⟩ := hx
      exact pow_ne_zero k (ne_of_gt (by linarith : (0 : ℝ) < 1 + x))
    exact hnum.div hden.continuousOn hne
  have hub : ∀ r : ℝ, 0 ≤ r →
      npv c N r ≤ c 0 + (∑ k ∈ Finset.range N, c (k + 1)) / (1 + r) := by
    intro r hr
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have h1ge : (1 : ℝ) ≤ 1 + r := by linarith
    have hterm : ∀ k ∈ Finset.range N,
        c (k + 1) / (1 + r) ^ (k + 1) ≤ c (k + 1) / (1 + r) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hck : 0 ≤ c (k + 1) := hnn _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hpow : (1 + r) ^ 1 ≤ (1 + r) ^ (k + 1) :=
        pow_le_pow_right₀ h1ge (Nat.le_add_left 1 k)
      have hdiv : 1 / (1 + r) ^ (k + 1) ≤ 1 / (1 + r) ^ 1 :=
        one_div_le_one_div_of_le (pow_pos h1r 1) hpow
      rw [pow_one] at hdiv
      rw [div_eq_mul_one_div (c (k + 1)) ((1 + r) ^ (k + 1)),
        div_eq_mul_one_div (c (k + 1)) (1 + r)]
      exact mul_le_mul_of_nonneg_left hdiv hck
    have hS : (∑ k ∈ Finset.range N, c (k + 1) / (1 + r) ^ (k + 1))
        ≤ (∑ k ∈ Finset.range N, c (k + 1)) / (1 + r) := by
      have h1 : (∑ k ∈ Finset.range N, c (k + 1) / (1 + r) ^ (k + 1))
          ≤ ∑ k ∈ Finset.range N, c (k + 1) / (1 + r) := Finset.sum_le_sum hterm
      have h2 : (∑ k ∈ Finset.range N, c (k + 1) / (1 + r))
          = (∑ k ∈ Finset.range N, c (k + 1)) / (1 + r) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [h2] at h1
      exact h1
    rw [hnpv r]
    exact add_le_add_right hS (c 0)
  obtain ⟨b, hb0, hblt⟩ : ∃ b : ℝ, 0 ≤ b ∧ npv c N b < 0 := by
    have hM : 0 ≤ ∑ k ∈ Finset.range N, c (k + 1) := by
      apply Finset.sum_nonneg
      intro k hk
      rw [Finset.mem_range] at hk
      exact hnn _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hMdiv : 0 ≤ (∑ k ∈ Finset.range N, c (k + 1)) / (-c 0) := div_nonneg hM hc0.le
    refine ⟨(∑ k ∈ Finset.range N, c (k + 1)) / (-c 0) + 1, by linarith, ?_⟩
    have hb0' : (0 : ℝ) ≤ (∑ k ∈ Finset.range N, c (k + 1)) / (-c 0) + 1 := by linarith
    have hub' := hub _ hb0'
    have h1b : (0 : ℝ) < 1 + ((∑ k ∈ Finset.range N, c (k + 1)) / (-c 0) + 1) := by linarith
    have hfin : (∑ k ∈ Finset.range N, c (k + 1))
        / (1 + ((∑ k ∈ Finset.range N, c (k + 1)) / (-c 0) + 1)) < -c 0 := by
      rw [div_lt_iff₀ h1b]
      have hne : (-c 0 : ℝ) ≠ 0 := ne_of_gt hc0
      have hmul : (-c 0) * ((∑ k ∈ Finset.range N, c (k + 1)) / (-c 0))
          = ∑ k ∈ Finset.range N, c (k + 1) :=
        mul_div_cancel₀ _ hne
      linarith
    linarith [hub', hfin]
  obtain ⟨a, ham1, ha0, hapos⟩ : ∃ a : ℝ, -1 < a ∧ a < 0 ∧ 0 < npv c N a := by
    have ht : (0 : ℝ) < c j / (-c 0) := div_pos hjpos hc0
    have hδ : (0 : ℝ) < min (c j / (-c 0) / 2) (1 / 2) := by
      rw [lt_min_iff]
      constructor <;> linarith
    have hδ1 : min (c j / (-c 0) / 2) (1 / 2) ≤ 1 := by
      have h := min_le_right (c j / (-c 0) / 2) (1 / 2)
      linarith
    have hδt : min (c j / (-c 0) / 2) (1 / 2) ≤ c j / (-c 0) / 2 := min_le_left _ _
    have hδhalf : min (c j / (-c 0) / 2) (1 / 2) < 1 := by
      have h := min_le_right (c j / (-c 0) / 2) (1 / 2)
      linarith
    refine ⟨-1 + min (c j / (-c 0) / 2) (1 / 2), by linarith, by linarith, ?_⟩
    have h1a : (1 : ℝ) + (-1 + min (c j / (-c 0) / 2) (1 / 2))
        = min (c j / (-c 0) / 2) (1 / 2) := by ring
    have ha1 : -1 < -1 + min (c j / (-c 0) / 2) (1 / 2) := by linarith
    have hpow : (min (c j / (-c 0) / 2) (1 / 2)) ^ j ≤ min (c j / (-c 0) / 2) (1 / 2) := by
      have h := pow_le_pow_of_le_one hδ.le hδ1 hj1
      rwa [pow_one] at h
    have hδpow : (min (c j / (-c 0) / 2) (1 / 2)) ^ j < c j / (-c 0) := by
      linarith [hpow, hδt, ht]
    have hmul : (min (c j / (-c 0) / 2) (1 / 2)) ^ j * (-c 0) < c j :=
      (lt_div_iff₀ hc0).mp hδpow
    have hblow : -c 0 < c j / (min (c j / (-c 0) / 2) (1 / 2)) ^ j := by
      rw [lt_div_iff₀ (pow_pos hδ j)]
      linarith [hmul]
    have hjm : j - 1 ∈ Finset.range N := by
      rw [Finset.mem_range]
      omega
    have hsingle := Finset.single_le_sum
      (htermnn (-1 + min (c j / (-c 0) / 2) (1 / 2)) ha1) hjm
    rw [Nat.sub_add_cancel hj1, h1a] at hsingle
    rw [hnpv, h1a]
    linarith [hsingle, hblow]
  have hab : a ≤ b := by linarith
  have hmem : (0 : ℝ) ∈ Set.Icc (npv c N b) (npv c N a) := ⟨le_of_lt hblt, le_of_lt hapos⟩
  have hsub := intermediate_value_Icc' hab (hcont a b ham1)
  obtain ⟨r, hrIcc, hreq⟩ := hsub hmem
  rw [Set.mem_Icc] at hrIcc
  have hr : IsIRR c N r := ⟨by linarith, hreq⟩
  refine ⟨r, hr, fun s hs => ?_⟩
  have hinj := hanti.injOn
  have hrmem : r ∈ Set.Ioi (-1) := hr.1
  have hsmem : s ∈ Set.Ioi (-1) := hs.1
  have heq : npv c N r = npv c N s := by rw [hr.2, hs.2]
  exact (hinj hrmem hsmem heq).symm

end MathlibExt.Economics.Finance.InternalRateOfReturn
