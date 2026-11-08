/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray
public import Cslib.Algorithms.Lean.MergeSort.MergeSort

/-!
# Maximum subarray by divide and conquer

`FIND-MAXIMUM-SUBARRAY` from CLRS, third edition, Section 4.1: split the array at its midpoint;
a maximum nonempty contiguous run lies entirely in the left half, entirely in the right half, or
crosses the midpoint, in which case it is a best nonempty suffix of the left half followed by a
best nonempty prefix of the right half (`FIND-MAX-CROSSING-SUBARRAY`). The answer is the largest
of the three.

The specification is the one used for Kadane's scan, `IsMaxSubarraySum`
(`CSLibExt.Algorithms.Lean.DynamicProgramming.MaximumSubarray`): the result is the largest sum of
a nonempty `List.IsInfix` run, so the two algorithms agree (`maxSubarraySumDC_eq_maxSubarraySum`).
As there, the result is the sum only, `none` on the empty list.

Combining a suffix and a prefix needs addition to be monotone on both sides, so values live in an
additive monoid with a linear order and `AddLeftMono` and `AddRightMono` (`ℤ`, `ℚ`, `ℝ`).

## Cost model

The crossing step scans both halves once, costing two units per element (one addition to the
running sum, one comparison with the best so far), `2 * n` for a run of `n`; combining the three
candidates costs `3` (the crossing addition and two comparisons). Splitting, recursion and
one-element runs are free. So the cost is `maxSubarrayDCCost n`, with
`maxSubarrayDCCost n = maxSubarrayDCCost ⌊n/2⌋ + maxSubarrayDCCost ⌈n/2⌉ + 2 * n + 3`, at most
`2 * n * ⌈log₂ n⌉ + 3 * (n - 1)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [AddMonoid α] [LinearOrder α]

/-- `p` is the maximum sum of a nonempty prefix of `xs`. -/
def IsMaxPrefixSum (xs : List α) (p : α) : Prop :=
  (∃ ys, ys <+: xs ∧ ys ≠ [] ∧ ys.sum = p) ∧ ∀ ys, ys <+: xs → ys ≠ [] → ys.sum ≤ p

/-- The sum of a nonempty list and its best nonempty suffix sum, scanning from the right. -/
def suffixScan : List α → TimeM ℕ (α × α)
  | [] => pure (0, 0)
  | [x] => do
      ✓[2]
      pure (x, x)
  | x :: y :: rest => do
      let r ← suffixScan (y :: rest)
      ✓[2]
      let total := x + r.1
      pure (total, max r.2 total)

/-- The best nonempty prefix sum of a nonempty list. -/
def prefixScan : List α → TimeM ℕ α
  | [] => pure 0
  | [x] => do
      ✓[2]
      pure x
  | x :: y :: rest => do
      let b ← prefixScan (y :: rest)
      ✓[2]
      pure (max x (x + b))

/-- The divide-and-conquer core on a nonempty list (the empty list gives `0`, unused). -/
def maxSubarrayDC : List α → TimeM ℕ α
  | [] => pure 0
  | [x] => pure x
  | x :: y :: rest => do
      let xs := x :: y :: rest
      let m := xs.length / 2
      let l ← maxSubarrayDC (xs.take m)
      let r ← maxSubarrayDC (xs.drop m)
      let s ← suffixScan (xs.take m)
      let p ← prefixScan (xs.drop m)
      ✓[3]
      pure (max (max l r) (s.2 + p))
termination_by xs => xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

/-- CLRS `FIND-MAXIMUM-SUBARRAY`: the maximum sum of a nonempty contiguous run, or `none` for the
empty list. -/
def maxSubarraySumDC (xs : List α) : TimeM ℕ (Option α) :=
  match xs with
  | [] => pure none
  | _ :: _ => some <$> maxSubarrayDC xs

/-! ## Cost -/

/-- The cost recurrence of the divide-and-conquer algorithm. -/
def maxSubarrayDCCost (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else maxSubarrayDCCost (n / 2) + maxSubarrayDCCost (n - n / 2) + 2 * n + 3
termination_by n
decreasing_by all_goals omega

theorem suffixScan_time : ∀ xs : List α, xs ≠ [] → (suffixScan xs).time = 2 * xs.length
  | [], h => absurd rfl h
  | [x], _ => by simp [suffixScan]
  | x :: y :: rest, _ => by
      rw [suffixScan]
      simp only [time_bind, time_tick, time_pure, Nat.add_zero,
        suffixScan_time (y :: rest) (List.cons_ne_nil _ _), List.length_cons]
      omega

theorem prefixScan_time : ∀ xs : List α, xs ≠ [] → (prefixScan xs).time = 2 * xs.length
  | [], h => absurd rfl h
  | [x], _ => by simp [prefixScan]
  | x :: y :: rest, _ => by
      rw [prefixScan]
      simp only [time_bind, time_tick, time_pure, Nat.add_zero,
        prefixScan_time (y :: rest) (List.cons_ne_nil _ _), List.length_cons]
      omega

theorem maxSubarrayDC_time (xs : List α) :
    (maxSubarrayDC xs).time = maxSubarrayDCCost xs.length := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    match xs, h with
    | [], h => simp [maxSubarrayDC, ← h, maxSubarrayDCCost]
    | [x], h => simp [maxSubarrayDC, ← h, maxSubarrayDCCost]
    | x :: y :: rest, h =>
        rw [maxSubarrayDC, maxSubarrayDCCost]
        simp only [show ¬ n ≤ 1 by simp at h; omega, ite_false]
        simp only [time_bind, time_tick, time_pure, Nat.add_zero]
        have hn : (x :: y :: rest).length = n := h
        set xs := x :: y :: rest
        have hm1 : 1 ≤ n / 2 := by simp [xs] at hn; omega
        have htake : (xs.take (xs.length / 2)).length = n / 2 := by
          simp only [List.length_take, hn]; omega
        have hdrop : (xs.drop (xs.length / 2)).length = n - n / 2 := by
          simp only [List.length_drop, hn]
        rw [ih _ (by omega) _ htake, ih _ (by omega) _ hdrop,
          suffixScan_time _ (List.ne_nil_of_length_pos (by omega)),
          prefixScan_time _ (List.ne_nil_of_length_pos (by omega)), htake, hdrop]
        omega

theorem maxSubarrayDCCost_le {n : ℕ} (hn : 1 ≤ n) :
    maxSubarrayDCCost n + 3 ≤ 2 * n * Nat.clog 2 n + 3 * n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [maxSubarrayDCCost]
    split_ifs with h1
    · have : n = 1 := by omega
      subst this
      simp
    · have ha := ih (n / 2) (by omega) (by omega)
      have hb := ih (n - n / 2) (by omega) (by omega)
      have hca : Nat.clog 2 (n / 2) ≤ Nat.clog 2 n - 1 := clog2_floor_half_le n (by omega)
      have hcb : Nat.clog 2 (n - n / 2) ≤ Nat.clog 2 n - 1 := by
        have := clog2_half_le n (by omega)
        rwa [show n - n / 2 = (n + 1) / 2 by omega]
      have hc1 : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
      set c := Nat.clog 2 n
      set a := n / 2
      set b := n - n / 2
      have h1 : a * Nat.clog 2 a ≤ a * (c - 1) := Nat.mul_le_mul_left _ hca
      have h2 : b * Nat.clog 2 b ≤ b * (c - 1) := Nat.mul_le_mul_left _ hcb
      have h3 : a * (c - 1) + b * (c - 1) = n * (c - 1) := by
        rw [← Nat.add_mul]; congr 1; omega
      have h4 : n * (c - 1) + n = n * c := by
        conv_rhs => rw [show c = (c - 1) + 1 by omega]
        rw [Nat.mul_add, Nat.mul_one]
      have e1 : 2 * a * Nat.clog 2 a = 2 * (a * Nat.clog 2 a) := Nat.mul_assoc _ _ _
      have e2 : 2 * b * Nat.clog 2 b = 2 * (b * Nat.clog 2 b) := Nat.mul_assoc _ _ _
      have e3 : 2 * n * c = 2 * (n * c) := Nat.mul_assoc _ _ _
      omega

/-- On a nonempty list of length `n` the divide-and-conquer algorithm uses at most
`2 * n * ⌈log₂ n⌉ + 3 * (n - 1)` operations (stated with the `3` moved left). -/
theorem maxSubarraySumDC_time_le (xs : List α) (hxs : xs ≠ []) :
    (maxSubarraySumDC xs).time + 3 ≤ 2 * xs.length * Nat.clog 2 xs.length + 3 * xs.length := by
  match xs, hxs with
  | x :: rest, _ =>
      simp only [maxSubarraySumDC, time_map, maxSubarrayDC_time]
      exact maxSubarrayDCCost_le (by simp)

@[simp]
theorem maxSubarraySumDC_nil_time : (maxSubarraySumDC ([] : List α)).time = 0 := by
  simp [maxSubarraySumDC]

/-! ## Correctness -/

/-- One scan from the right gives the total and the best nonempty suffix sum. -/
theorem suffixScan_spec : ∀ xs : List α, xs ≠ [] →
    (suffixScan xs).ret.1 = xs.sum ∧ IsMaxSuffixSum xs (suffixScan xs).ret.2
  | [], h => absurd rfl h
  | [x], _ => by simpa [suffixScan] using isMaxSuffixSum_singleton x
  | x :: y :: rest, _ => by
      have ih := suffixScan_spec (y :: rest) (List.cons_ne_nil _ _)
      rw [suffixScan]
      simp only [ret_bind, ret_pure]
      generalize (suffixScan (y :: rest)).ret = r at ih ⊢
      obtain ⟨hsum, ⟨⟨t, ht, htne, htsum⟩, hle⟩⟩ := ih
      refine ⟨by rw [hsum]; exact List.sum_cons.symm, ⟨?_, fun ys hys hne => ?_⟩⟩
      · rcases le_total (x + r.1) r.2 with hc | hc
        · exact ⟨t, ht.trans (List.suffix_cons _ _), htne, by rw [htsum, max_eq_left hc]⟩
        · exact ⟨x :: y :: rest, List.suffix_refl _, List.cons_ne_nil _ _,
            by rw [List.sum_cons, max_eq_right hc, hsum]⟩
      · rcases List.suffix_cons_iff.1 hys with rfl | hys
        · rw [List.sum_cons, ← hsum]; exact le_max_right _ _
        · exact (hle ys hys hne).trans (le_max_left _ _)

theorem prefixScan_spec [AddLeftMono α] : ∀ xs : List α, xs ≠ [] →
    IsMaxPrefixSum xs (prefixScan xs).ret
  | [], h => absurd rfl h
  | [x], _ => by
      rw [prefixScan]
      simp only [ret_bind, ret_pure]
      refine ⟨⟨[x], List.prefix_refl _, List.cons_ne_nil _ _, by simp⟩, fun ys hys hne => ?_⟩
      rcases List.prefix_cons_iff.1 hys with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · simp [List.eq_nil_of_prefix_nil ht]
  | x :: y :: rest, _ => by
      have ih := prefixScan_spec (y :: rest) (List.cons_ne_nil _ _)
      rw [prefixScan]
      simp only [ret_bind, ret_pure]
      generalize (prefixScan (y :: rest)).ret = b at ih ⊢
      obtain ⟨⟨t, ht, htne, htsum⟩, hle⟩ := ih
      refine ⟨?_, fun ys hys hne => ?_⟩
      · rcases le_total (x + b) x with hc | hc
        · exact ⟨[x], List.prefix_cons_iff.2 (Or.inr ⟨[], rfl, List.nil_prefix⟩),
            List.cons_ne_nil _ _, by simp [max_eq_left hc]⟩
        · exact ⟨x :: t, List.prefix_cons_iff.2 (Or.inr ⟨t, rfl, ht⟩), List.cons_ne_nil _ _,
            by rw [List.sum_cons, htsum, max_eq_right hc]⟩
      · rcases List.prefix_cons_iff.1 hys with rfl | ⟨u, rfl, hu⟩
        · exact absurd rfl hne
        · rw [List.sum_cons]
          by_cases hu0 : u = []
          · subst hu0
            simp
          · exact (add_le_add_right (hle u hu hu0) x).trans (le_max_right _ _)

/-- Combining the halves: a best run of `L ++ R` is a best run of `L`, a best run of `R`, or a
best suffix of `L` followed by a best prefix of `R`. -/
theorem IsMaxSubarraySum.append [AddLeftMono α] [AddRightMono α] {L R : List α} {l r s p : α}
    (hl : IsMaxSubarraySum L l) (hr : IsMaxSubarraySum R r) (hs : IsMaxSuffixSum L s)
    (hp : IsMaxPrefixSum R p) : IsMaxSubarraySum (L ++ R) (max (max l r) (s + p)) := by
  obtain ⟨⟨wl, hwl, hwlne, rfl⟩, hlle⟩ := hl
  obtain ⟨⟨wr, hwr, hwrne, rfl⟩, hrle⟩ := hr
  obtain ⟨⟨ws, hws, hwsne, rfl⟩, hsle⟩ := hs
  obtain ⟨⟨wp, hwp, hwpne, rfl⟩, hple⟩ := hp
  refine ⟨?_, fun ys hys hne => ?_⟩
  · have hcross : (ws ++ wp) <:+: L ++ R :=
      List.infix_append_iff.2 (Or.inr (Or.inr ⟨ws, wp, rfl, hws, hwp⟩))
    rcases le_total (max wl.sum wr.sum) (ws.sum + wp.sum) with hc | hc
    · exact ⟨ws ++ wp, hcross, by simp [hwsne], by rw [List.sum_append, max_eq_right hc]⟩
    · rw [max_eq_left hc]
      rcases le_total wl.sum wr.sum with hc' | hc'
      · exact ⟨wr, hwr.trans (List.suffix_append L R).isInfix, hwrne, by rw [max_eq_right hc']⟩
      · exact ⟨wl, hwl.trans (List.infix_append [] L R), hwlne, by rw [max_eq_left hc']⟩
  · rcases List.infix_append_iff_ne_nil.1 hys with h | h | ⟨l₁, l₂, h1, h2, rfl, h1s, h2p⟩
    · exact ((hlle ys h hne).trans (le_max_left _ _)).trans (le_max_left _ _)
    · exact ((hrle ys h hne).trans (le_max_right _ _)).trans (le_max_left _ _)
    · rw [List.sum_append]
      exact (add_le_add (hsle l₁ h1s h1) (hple l₂ h2p h2)).trans (le_max_right _ _)

theorem isMaxSubarraySum_maxSubarrayDC [AddLeftMono α] [AddRightMono α] (xs : List α)
    (hxs : xs ≠ []) : IsMaxSubarraySum xs (maxSubarrayDC xs).ret := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    match xs, h, hxs with
    | [x], _, _ => simpa [maxSubarrayDC] using isMaxSubarraySum_singleton x
    | x :: y :: rest, h, _ =>
        rw [maxSubarrayDC]
        simp only [ret_bind, ret_pure]
        set xs := x :: y :: rest
        have hn : xs.length = n := h
        have hm1 : 1 ≤ xs.length / 2 := by simp [xs]; omega
        have hL : xs.take (xs.length / 2) ≠ [] :=
          List.ne_nil_of_length_pos (by simp only [List.length_take]; omega)
        have hR : xs.drop (xs.length / 2) ≠ [] :=
          List.ne_nil_of_length_pos (by simp only [List.length_drop]; omega)
        have hl := ih _ (by simp only [List.length_take]; omega) _ hL rfl
        have hr := ih _ (by simp only [List.length_drop]; omega) _ hR rfl
        have := IsMaxSubarraySum.append hl hr (suffixScan_spec _ hL).2 (prefixScan_spec _ hR)
        rwa [List.take_append_drop] at this

/-- The divide-and-conquer algorithm returns a value exactly when the input is nonempty, and that
value is the maximum sum of a nonempty contiguous run. -/
theorem maxSubarraySumDC_ret_eq_some_iff [AddLeftMono α] [AddRightMono α] (xs : List α)
    (m : α) : (maxSubarraySumDC xs).ret = some m ↔ IsMaxSubarraySum xs m := by
  match xs with
  | [] =>
      simp only [maxSubarraySumDC, ret_pure, reduceCtorEq, false_iff]
      exact fun h => h.ne_nil rfl
  | x :: rest =>
      have h := isMaxSubarraySum_maxSubarrayDC (x :: rest) (List.cons_ne_nil _ _)
      simp only [maxSubarraySumDC, ret_map, Option.some.injEq]
      exact ⟨fun hm => hm ▸ h, fun hm => h.unique hm⟩

/-- Divide and conquer and Kadane's scan return the same answer. -/
theorem maxSubarraySumDC_eq_maxSubarraySum [AddLeftMono α] [AddRightMono α] (xs : List α) :
    (maxSubarraySumDC xs).ret = (maxSubarraySum xs).ret := by
  cases h : (maxSubarraySum xs).ret with
  | none =>
      rw [maxSubarraySum_ret_eq_none_iff] at h
      subst h
      simp [maxSubarraySumDC]
  | some m =>
      exact (maxSubarraySumDC_ret_eq_some_iff xs m).2
        ((maxSubarraySum_ret_eq_some_iff xs m).1 h)

end Cslib.Algorithms.Lean.TimeM
