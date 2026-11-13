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

/-- **Maximum prefix sum.** Let $\alpha$ be an additive monoid with a linear order. For a list $xs$
over $\alpha$ and $p \in \alpha$, $p$ is the maximum prefix sum of $xs$ when some nonempty prefix
of $xs$ has sum $p$ and every nonempty prefix of $xs$ has sum at most $p$. -/
def IsMaxPrefixSum (xs : List α) (p : α) : Prop :=
  (∃ ys, ys <+: xs ∧ ys ≠ [] ∧ ys.sum = p) ∧ ∀ ys, ys <+: xs → ys ≠ [] → ys.sum ≤ p

/-- **Right-to-left suffix scan.** Let $\alpha$ be an additive monoid carrying a linear order.
For a nonempty list $x_1, \dots, x_n$ in $\alpha$, this timed computation returns the pair
$(x_1 + \dots + x_n, s)$, where $s$ is the maximum of the suffix sums $x_i + \dots + x_n$ over
$1 \le i \le n$. It scans from the right: the step for $x_i$ forms $x_i + (x_{i+1} + \dots + x_n)$
and takes its maximum with the best suffix sum found so far, at a cost of $2$ time units per
element, $2n$ in total. On the empty list it returns $(0, 0)$ at no cost. -/
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

/-- **Prefix scan.** For lists over an additive monoid with a linear order, the prefix scan returns
$0$ on the empty list at no cost, and $x$ on a one-element list $[x]$ at cost $2$. On a list with
first element $x$ and nonempty tail $t$ it returns $\max(x, x + b)$, where $b$ is the prefix scan
of $t$, at the cost of the scan of $t$ plus $2$.

When $u \le v$ implies $a + u \le a + v$, the value on a nonempty list is the maximum sum of a
nonempty prefix of the list. -/
def prefixScan : List α → TimeM ℕ α
  | [] => pure 0
  | [x] => do
      ✓[2]
      pure x
  | x :: y :: rest => do
      let b ← prefixScan (y :: rest)
      ✓[2]
      pure (max x (x + b))

/-- **Divide-and-conquer core of maximum subarray.** For lists over an additive monoid with a
linear order: on the empty list it returns $0$ and on a one-element list $[x]$ it returns $x$,
both at no cost. On a list of length $n \ge 2$, let $m = \lfloor n/2 \rfloor$, let $l$ and $r$ be
its results on the first $m$ elements and on the remaining $n - m$ elements, let $s$ be the best
nonempty suffix sum of the first $m$ elements as computed by the suffix scan, and let $p$ be the
prefix scan of the remaining elements. It returns $\max(\max(l, r), s + p)$, at the cost of
these four computations plus $3$. -/
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

/-- **Divide-and-conquer maximum subarray.** The CLRS algorithm FIND-MAXIMUM-SUBARRAY over an
additive monoid with a linear order, returning only the sum. On the empty list it returns no
value, at no cost. On a nonempty list it returns the value of the divide-and-conquer core on that
list, at the same cost; the core splits a list of length $n \ge 2$ after its first
$\lfloor n/2 \rfloor$ elements and returns the largest of its results on the two parts and the
best nonempty suffix sum of the first part plus the prefix scan of the second part.

When $b \le c$ implies $a + b \le a + c$ and $b + a \le c + a$, the value returned on a nonempty
list is the maximum sum of a nonempty contiguous run of the list. -/
def maxSubarraySumDC (xs : List α) : TimeM ℕ (Option α) :=
  match xs with
  | [] => pure none
  | _ :: _ => some <$> maxSubarrayDC xs

/-! ## Cost -/

/-- **Cost recurrence of divide-and-conquer maximum subarray.** The function
$T : \mathbb{N} \to \mathbb{N}$ given by $T(n) = 0$ for $n \le 1$ and
$T(n) = T(\lfloor n/2 \rfloor) + T(n - \lfloor n/2 \rfloor) + 2n + 3$ for $n \ge 2$. -/
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

/-- **Running time of divide-and-conquer maximum subarray.** Let $\alpha$ be an additive monoid
with a linear order. On a nonempty list over $\alpha$ of length $n$, the cost $T$ of the
divide-and-conquer maximum subarray algorithm satisfies
$T + 3 \le 2n\lceil \log_2 n \rceil + 3n$, that is, $T \le 2n\lceil \log_2 n \rceil + 3(n - 1)$. -/
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

/-- **Correctness of the suffix scan.** Let $\alpha$ be an additive monoid with a linear order. For
every nonempty list $xs$ over $\alpha$, the suffix scan of $xs$ returns a pair whose first
component is the sum of $xs$ and whose second component is the maximum sum of a nonempty suffix
of $xs$. -/
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

/-- **Maximum subarray sum of a concatenation.** Let $\alpha$ be an additive monoid with a linear
order such that $b \le c$ implies $a + b \le a + c$ and $b + a \le c + a$, and let $L$ and $R$ be
lists over $\alpha$. Suppose that $l$ is the maximum sum of a nonempty contiguous run of $L$, $r$
is the maximum sum of a nonempty contiguous run of $R$, $s$ is the maximum sum of a nonempty
suffix of $L$, and $p$ is the maximum sum of a nonempty prefix of $R$. Then
$\max(\max(l, r), s + p)$ is the maximum sum of a nonempty contiguous run of the concatenation of
$L$ followed by $R$. -/
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

/-- **Correctness of divide-and-conquer maximum subarray.** Let $\alpha$ be an additive monoid
with a linear order such that $b \le c$ implies $a + b \le a + c$ and $b + a \le c + a$. For every
list $xs$ over $\alpha$ and every $m \in \alpha$, the divide-and-conquer algorithm returns $m$ on
$xs$ if and only if $m$ is the maximum sum of a nonempty contiguous run of $xs$. -/
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

/-- **Divide and conquer agrees with Kadane's algorithm.** Let $\alpha$ be an additive monoid with
a linear order such that $b \le c$ implies $a + b \le a + c$ and $b + a \le c + a$. For every list
$xs$ over $\alpha$, the divide-and-conquer maximum subarray algorithm and Kadane's algorithm
return the same result on $xs$. -/
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
