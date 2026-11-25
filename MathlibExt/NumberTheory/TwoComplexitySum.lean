/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import MathlibExt.NumberTheory.TwoComplexity

/-! # The 2-complexity of sums of distinct powers of two -/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.TwoComplexityWanted

private theorem canBuild_mul_two_pow {k n : ℕ} (h : CanBuild 2 k n) (d : ℕ) :
    CanBuild 2 (k + d) (n * 2 ^ d) := by
  induction d with
  | zero => simpa using h
  | succ d ih => simpa only [pow_succ, ← mul_assoc, Nat.add_succ] using ih.mul CanBuild.base

-- Shifting all exponents down to start at one lets us add the smallest term as a single two.
private theorem canBuild_shifted_sum (s : Finset ℕ) (hne : s.Nonempty)
    (d : ℕ) (hd : ∀ e ∈ s, d ≤ e) :
    CanBuild 2 (s.max' hne - d + s.card) (∑ e ∈ s, 2 ^ (e - d + 1)) := by
  induction s using Finset.induction_on_min generalizing d with
  | empty => simp at hne
  | insert a s ha ih =>
    have hda := hd a (Finset.mem_insert_self a s)
    have hnot : a ∉ s := fun h => (ha a h).false
    rcases s.eq_empty_or_nonempty with rfl | hne'
    · simpa [pow_succ', Nat.add_comm] using canBuild_mul_two_pow CanBuild.base (a - d)
    · have hamax := (ha _ (s.max'_mem hne')).le
      have htail := ih hne' a (fun e he => (ha e he).le)
      have hbuild := canBuild_mul_two_pow (CanBuild.base.add htail) (a - d)
      rw [Finset.max'_insert a s hne', max_eq_right hamax, Finset.card_insert_of_notMem hnot,
        Finset.sum_insert hnot]
      convert hbuild using 1
      · omega
      · rw [add_mul, Finset.sum_mul, pow_succ' 2 (a - d)]
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        rw [← pow_add]
        congr 1
        have := ha e he
        omega

/-- **An upper bound for the 2-complexity of a sum of distinct powers of two.** Write
$\|n\|_2$ for the $2$-complexity of $n$. Let $S$ be a nonempty finite set of positive integers
with $k$ elements and largest element $m_1$. Then $\|\sum_{e \in S} 2^e\|_2 \le m_1 + k - 1$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
public theorem complexityL_sum_two_pow_le (s : Finset ℕ)
    (hs : ∀ e ∈ s, 1 ≤ e) (hne : s.Nonempty) :
    complexityL 2 (∑ e ∈ s, 2 ^ e) ≤ s.max' hne + s.card - 1 := by
  have hbuild := canBuild_shifted_sum s hne 1 hs
  have hmax := hs _ (s.max'_mem hne)
  rw [show s.max' hne + s.card - 1 = s.max' hne - 1 + s.card by omega]
  apply complexityL_min_le
  simpa only [Finset.sum_congr rfl (fun e he => congrArg (2 ^ ·) (Nat.sub_add_cancel (hs e he)))]
    using hbuild

end MathlibExt.NumberTheory.TwoComplexityWanted
