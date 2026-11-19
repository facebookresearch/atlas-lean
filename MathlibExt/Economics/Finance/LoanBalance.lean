/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Prospective and retrospective loan balances

A loan `L` at per-period rate `r` is repaid by `n` level payments `P` at the ends of periods
`1, …, n` and priced at the same rate,
`L = presentValue (discountFactor r) (Finset.Icc 1 n) (fun _ => P)`. After `k` payments the
retrospective balance is the accumulated loan minus accumulated payments,
`L (1 + r)ᵏ - P ∑_{j<k} (1 + r)ʲ`, and the prospective balance is the present value at date
`k` of the remaining payments.

## Main results

* `MathlibExt.Economics.Finance.retrospectiveBalance_eq_prospectiveBalance`: the two balances
  agree for every `k ≤ n` when `1 + r ≠ 0`.

No division by `r` occurs, so the zero rate is covered. The proof is an induction on `k`
with `Finset.sum_range_succ`; both balances satisfy `B_{k+1} = (1 + r) B_k - P`.

## References

SOA Exam FM syllabus (loan balances, prospective and retrospective methods). Atlas roadmap
target FI01.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Retrospective loan balance after `k` level payments `P` made at the ends of
periods `1, …, k` on a loan `L` at per-period rate `r`: the loan accumulated to
date `k` minus the accumulated payments, `L (1 + r)ᵏ - P Σ_{j<k} (1 + r)ʲ`
(source clause: "retrospective balance"). -/
noncomputable def retrospectiveBalance (r L P : ℝ) (k : ℕ) : ℝ :=
  L * (1 + r) ^ k - P * ∑ j ∈ Finset.range k, (1 + r) ^ j

/-- Prospective loan balance at date `k` of an `n`-payment level loan: the present
value at date `k` of the remaining payments `P` at dates `k + 1, …, n`
(source clause: "prospective balance"). -/
noncomputable def prospectiveBalance (r P : ℝ) (n k : ℕ) : ℝ :=
  presentValue (discountFactor r) (Finset.Icc 1 (n - k)) (fun _ => P)

theorem presentValue_Icc_one_eq_sum_range (D : ℕ → ℝ) (P : ℝ) (m : ℕ) :
    presentValue D (Finset.Icc 1 m) (fun _ => P)
      = ∑ i ∈ Finset.range m, D (1 + i) * P := by
  induction m with
  | zero =>
    simp only [presentValue]
    rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by omega)]
    simp
  | succ m ih =>
    simp only [presentValue] at ih ⊢
    have hIcc : ∑ t ∈ Finset.Icc 1 (m + 1), D t * P
        = (∑ t ∈ Finset.Icc 1 m, D t * P) + D (m + 1) * P :=
      Finset.sum_Icc_succ_top (by omega) _
    have hrange : ∑ i ∈ Finset.range (m + 1), D (1 + i) * P
        = (∑ i ∈ Finset.range m, D (1 + i) * P) + D (1 + m) * P :=
      Finset.sum_range_succ _ _
    have hadd : (1 : ℕ) + m = m + 1 := Nat.add_comm 1 m
    rw [hIcc, hrange, ih, hadd]

theorem mul_discountFactor_succ (r : ℝ) (t : ℕ) (h1r : 1 + r ≠ 0) :
    (1 + r) * discountFactor r (t + 1) = discountFactor r t := by
  simp only [discountFactor]
  rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ h1r, one_mul]

theorem retrospectiveBalance_succ (r L P : ℝ) (k : ℕ) :
    retrospectiveBalance r L P (k + 1)
      = (1 + r) * retrospectiveBalance r L P k - P := by
  have hgeom : ∑ i ∈ Finset.range (k + 1), (1 + r) ^ i
      = (1 + r) * ∑ i ∈ Finset.range k, (1 + r) ^ i + 1 :=
    geom_sum_succ
  simp only [retrospectiveBalance]
  rw [hgeom, pow_succ]
  ring

theorem discounted_sum_succ (r P : ℝ) (m : ℕ) (h1r : 1 + r ≠ 0) :
    (1 + r) * (∑ i ∈ Finset.range (m + 1), discountFactor r (1 + i) * P)
      = (∑ i ∈ Finset.range m, discountFactor r (1 + i) * P) + P := by
  rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
  have h0 : (1 + r) * (discountFactor r (1 + 0) * P) = P := by
    rw [show (1 : ℕ) + 0 = 0 + 1 by omega, ← mul_assoc,
      mul_discountFactor_succ r 0 h1r]
    simp [discountFactor]
  have hstep : ∀ i : ℕ, (1 + r) * (discountFactor r (1 + (i + 1)) * P)
      = discountFactor r (1 + i) * P := by
    intro i
    rw [show (1 : ℕ) + (i + 1) = (1 + i) + 1 by ring, ← mul_assoc,
      mul_discountFactor_succ r (1 + i) h1r]
  have hsum : (∑ x ∈ Finset.range m, (1 + r) * (discountFactor r (1 + (x + 1)) * P))
      = ∑ x ∈ Finset.range m, discountFactor r (1 + x) * P :=
    Finset.sum_congr rfl (fun i _ => hstep i)
  rw [hsum, h0]

theorem prospectiveBalance_succ (r P : ℝ) (n k : ℕ) (h1r : 1 + r ≠ 0) (hkn : k < n) :
    prospectiveBalance r P n (k + 1)
      = (1 + r) * prospectiveBalance r P n k - P := by
  have hnm : n - k = (n - (k + 1)) + 1 := by omega
  rw [prospectiveBalance, prospectiveBalance,
    presentValue_Icc_one_eq_sum_range, presentValue_Icc_one_eq_sum_range, hnm,
    discounted_sum_succ r P (n - (k + 1)) h1r]
  ring

/-- Prospective and retrospective balances agree when the loan is the present value
of its `n` level payments at the same rate and payment timing, for every date
`k ≤ n` (Atlas roadmap FI01.T04). -/
theorem retrospectiveBalance_eq_prospectiveBalance (r L P : ℝ) (n k : ℕ)
    (h1r : 1 + r ≠ 0) (hk : k ≤ n)
    (hL : L = presentValue (discountFactor r) (Finset.Icc 1 n) (fun _ => P)) :
    retrospectiveBalance r L P k = prospectiveBalance r P n k := by
  have key : ∀ j : ℕ, j ≤ n → retrospectiveBalance r L P j = prospectiveBalance r P n j := by
    intro j
    induction j with
    | zero =>
      intro _
      have hR0 : retrospectiveBalance r L P 0 = L := by simp [retrospectiveBalance]
      have hS0 : prospectiveBalance r P n 0 = L := by
        simp only [prospectiveBalance, Nat.sub_zero]
        exact hL.symm
      rw [hR0, hS0]
    | succ j ih =>
      intro hj'
      have hjn : j < n := by omega
      have hj_le : j ≤ n := by omega
      rw [retrospectiveBalance_succ, prospectiveBalance_succ r P n j h1r hjn, ih hj_le]
  exact key k hk

end MathlibExt.Economics.Finance
