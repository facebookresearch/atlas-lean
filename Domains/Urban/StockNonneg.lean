/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
import MathlibExt.Combinatorics.Graph.NonnegTransferStep
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Urban nonnegative-stock certificate

## i. Overview

Zones are nodes `V` and distinct transfers (relocations,
reclassifications) are arcs `E` with `tail head : E → V`;
one stock unit is chosen per instantiation. Over one
interval the zone stocks update by
`m' = m + (incidenceMatrix tail head).mulVec F + s - r`,
where `F e` is the amount moved along arc `e` (out of
`tail e`, into `head e`), `s` the additions and `r` the
retirements. Urban accounts record amounts, not fractions.
Nonnegative stocks, transfer amounts, additions and
retirements whose outgoing total at each zone (transfers
out plus retirements) does not exceed the zone stock keep
every updated stock nonnegative. The amounts correspond to
the shared transfer fractions `F e / m (tail e)` and
`r v / m v` (totalized division at zero-stock zones), and
the nonnegativity itself is the shared transfer-step
certificate `nonneg_transfer_step`. Multi-period
nonnegativity is not stated.

## ii. Key results

- `Urban.urbanStock_nonneg_of_outgoing_le`: the
  nonnegative-stock certificate in recorded amounts.

## iii. Table of contents

- A. Amount-form certificate

## iv. References

- `MathlibExt.Combinatorics.Graph.ArcNetwork` for the
  signed incidence matrix.
- `MathlibExt.Combinatorics.Graph.NonnegTransferStep` for
  the shared transfer-step budget certificate.
- `MathlibExt.Urban.StockBalance` for the matching total
  balance (which defers nonnegativity to this certificate).
-/

@[expose] public section

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork

namespace Urban

/-! ## A. Amount-form certificate -/

/-- Conditional form of the urban certificate, given the
shared transfer-step statement. -/
private theorem urbanStock_nonneg_of_outgoing_le_of {V : Type*}
    [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (htransfer : ∀ (tail head : E → V) {α F : E → ℝ} {δ m m' s r : V → ℝ},
      (∀ v, 0 ≤ m v) → (∀ v, 0 ≤ s v) →
      (∀ e, 0 ≤ α e) →
      (∀ e, F e = α e * m (tail e)) →
      (∀ v, r v = δ v * m v) →
      (∀ v,
        (∑ e ∈ (Finset.univ : Finset E).filter
            (fun e => tail e = v), α e) + δ v ≤ 1) →
      m' = m + (incidenceMatrix tail head) *ᵥ F + s - r →
      ∀ v, 0 ≤ m' v)
    (tail head : E → V) {F : E → ℝ} {m m' s r : V → ℝ}
    (hm : ∀ v, 0 ≤ m v) (hs : ∀ v, 0 ≤ s v)
    (hF : ∀ e, 0 ≤ F e) (hr : ∀ v, 0 ≤ r v)
    (hout : ∀ v,
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), F e)
        + r v ≤ m v)
    (h : m' = m + (incidenceMatrix tail head).mulVec F + s - r) :
    ∀ v, 0 ≤ m' v := by
  refine htransfer tail head (α := fun e => F e / m (tail e))
    (δ := fun v => r v / m v) hm hs ?hα ?hF ?hr ?hsum h
  · intro e
    exact div_nonneg (hF e) (hm _)
  · intro e
    by_cases hmv : m (tail e) = 0
    · have hmem : e ∈ (Finset.univ : Finset E).filter
          (fun e' => tail e' = tail e) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ e, rfl⟩
      have hle : F e ≤ ∑ e' ∈ (Finset.univ : Finset E).filter
          (fun e' => tail e' = tail e), F e' :=
        Finset.single_le_sum (fun e _ => hF e) hmem
      have hS : 0 ≤ ∑ e' ∈ (Finset.univ : Finset E).filter
          (fun e' => tail e' = tail e), F e' :=
        Finset.sum_nonneg (fun e _ => hF e)
      have hout_v := hout (tail e)
      rw [hmv] at hout_v
      have hFe : F e = 0 := by
        have hsum_le : (∑ e' ∈ (Finset.univ : Finset E).filter
            (fun e' => tail e' = tail e), F e') ≤ 0 := by
          linarith [hout_v, hr (tail e), hS]
        linarith [hle, hsum_le, hF e]
      simp [hFe, hmv]
    · exact (div_mul_cancel₀ _ hmv).symm
  · intro v
    by_cases hmv : m v = 0
    · have hS : 0 ≤ ∑ e ∈ (Finset.univ : Finset E).filter
          (fun e => tail e = v), F e :=
        Finset.sum_nonneg (fun e _ => hF e)
      have hout_v := hout v
      rw [hmv] at hout_v
      have hrv : r v = 0 := by linarith [hout_v, hS, hr v]
      simp [hrv, hmv]
    · exact (div_mul_cancel₀ _ hmv).symm
  · intro v
    by_cases hmv : m v = 0
    · have hterm : ∀ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v),
          F e / m (tail e) = 0 := by
        intro e he
        have htail : tail e = v := (Finset.mem_filter.mp he).2
        rw [htail, hmv, div_zero]
      have hsum_zero : (∑ e ∈ (Finset.univ : Finset E).filter
          (fun e => tail e = v), F e / m (tail e)) = 0 :=
        Finset.sum_eq_zero hterm
      have hrdiv : r v / m v = 0 := by rw [hmv, div_zero]
      rw [hsum_zero, hrdiv, zero_add]
      exact zero_le_one
    · have hpos : 0 < m v := lt_of_le_of_ne (hm v) (Ne.symm hmv)
      have hcong : (∑ e ∈ (Finset.univ : Finset E).filter
            (fun e => tail e = v), F e / m (tail e)) =
          ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v),
            F e / m v := by
        apply Finset.sum_congr rfl
        intro e he
        have htail : tail e = v := (Finset.mem_filter.mp he).2
        rw [htail]
      rw [hcong, ← Finset.sum_div, ← add_div]
      exact (div_le_one hpos).mpr (hout v)

/-- Urban nonnegative-stock certificate. Nonnegative
transfer amounts `F`, additions `s` and retirements `r`
whose outgoing total at each zone (transfers out plus
retirements) does not exceed the zone stock keep every
updated stock nonnegative. The amounts map to the shared
fractions `F e / m (tail e)` and `r v / m v`; the
conclusion is `nonneg_transfer_step`. -/
theorem urbanStock_nonneg_of_outgoing_le {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) {F : E → ℝ} {m m' s r : V → ℝ}
    (hm : ∀ v, 0 ≤ m v) (hs : ∀ v, 0 ≤ s v)
    (hF : ∀ e, 0 ≤ F e) (hr : ∀ v, 0 ≤ r v)
    (hout : ∀ v,
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), F e)
        + r v ≤ m v)
    (h : m' = m + (incidenceMatrix tail head).mulVec F + s - r) :
    ∀ v, 0 ≤ m' v :=
  urbanStock_nonneg_of_outgoing_le_of nonneg_transfer_step
    tail head hm hs hF hr hout h

end Urban
