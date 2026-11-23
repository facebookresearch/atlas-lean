/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Maximum Nim and the Josephus problem

This file proves a floor identity from the paper of Takahashi, Manabe and Miyadera on Maximum Nim
with the rule function $f(x) = \lfloor x/k \rfloor$ and the Josephus problem.

## Main statements

* `MetaMathlibExt.maximumNim_sub_div_sub_one_eq`: for $k \ge 2$ and $x$ not a multiple of $k$,
  $x - \lfloor x/k \rfloor - 1 = \lfloor (k-1)x/k \rfloor$. For the rule function
  $f(x) = \lfloor x/k \rfloor$, which is flat at every such $x$, this identifies the position
  $x - f(x) - 1$ with $\lfloor (k-1)x/k \rfloor$.

## Proof outline

Write $(k-1)x = kx - x$. As $x \ge 1$, the core lemma `Nat.mul_sub_div` gives
$\lfloor (kx - x)/k \rfloor = x - (\lfloor (x-1)/k \rfloor + 1)$, and
$\lfloor (x-1)/k \rfloor = \lfloor x/k \rfloor$ because $k$ does not divide $x$
(`Nat.succ_div_of_not_dvd`).

## Implementation notes

`maximumNim_sub_div_sub_one_eq` keeps the full name, the statement and the docstring it had as a
wanted theorem in `WantedExt.Combinatorics.MaximumNimJosephusWanted`. Natural-number division is
the floor, and `¬k ∣ x` says that $x$ is not a multiple of $k$. Then $x \ge 1$,
$\lfloor x/k \rfloor + 1 \le x$ and $k - 1 \ge 1$, so every truncated subtraction in the statement
is an ordinary difference.

## References

* Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and Josephus Problem*,
  arXiv:2403.19308v1 (2024), Section 3, equation (1) in the proof of Lemma 3.1
  (<https://arxiv.org/abs/2403.19308>). There the identity is displayed without proof and without
  the hypothesis that $k$ does not divide $x$, which it needs: at a positive multiple $x$ of $k$
  the right side exceeds the left side by one. The docstring of `maximumNim_sub_div_sub_one_eq`
  cites the published version, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024),
  Article G5.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Floor identity for non-multiples in Maximum Nim.** Let $k \ge 2$ and $x$ be natural numbers
such that $x$ is not a multiple of $k$. Then
$x - \lfloor x/k \rfloor - 1 = \lfloor (k-1)x/k \rfloor$.

Source: Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*,
        INTEGERS 24 (2024), Article G5, Lemma 2 (`integers-2024-G5-lem-2`). -/
theorem maximumNim_sub_div_sub_one_eq (k x : ℕ) (hk : 2 ≤ k)
    (hxk : ¬k ∣ x) :
    x - x / k - 1 = (k - 1) * x / k := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact hxk (Nat.dvd_zero k)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hx
  have ha : a < k * (a + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_mul_of_pos_left (a + 1) (by omega))
  rw [Nat.succ_div_of_not_dvd hxk, Nat.sub_one_mul, Nat.mul_sub_div a k (a + 1) ha, Nat.sub_sub]

end

end MetaMathlibExt
