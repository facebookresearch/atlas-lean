/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TwoComplexity

/-!
# The largest value built from a fixed number of copies

For a natural number `l > 1`, `canBuild_max` shows that the largest value obtainable
from exactly `m ≥ 1` copies of `l` by addition and multiplication is `l ^ m`.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.TwoComplexityWanted

/-- **The largest number built from $m$ copies of $l$.** Let $l > 1$ and $m \ge 1$ be natural
numbers. Then $l^m$ can be built from exactly $m$ copies of $l$ using addition and
multiplication, and every natural number that can be built from $m$ copies of $l$ in this way
is at most $l^m$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 1. -/
public theorem canBuild_max (l m : ℕ) (hl : 1 < l)
    (hm : 1 ≤ m) :
    CanBuild l m (l ^ m) ∧
      ∀ n : ℕ, CanBuild l m n → n ≤ l ^ m := by
  constructor
  · induction m, hm using Nat.le_induction with
    | base => simpa only [pow_one] using (CanBuild.base (l := l))
    | succ k _ ih => simpa only [pow_succ] using ih.mul CanBuild.base
  · clear hm
    intro n h
    induction h with
    | base => simp
    | add hx hy ihx ihy =>
      rw [pow_add]
      exact (Nat.add_le_add ihx ihy).trans (Nat.add_le_mul
        (Nat.one_lt_pow (Nat.ne_of_gt hx.one_le) hl)
        (Nat.one_lt_pow (Nat.ne_of_gt hy.one_le) hl))
    | mul _ _ ihx ihy =>
      rw [pow_add]
      exact Nat.mul_le_mul ihx ihy

end MathlibExt.NumberTheory.TwoComplexityWanted
