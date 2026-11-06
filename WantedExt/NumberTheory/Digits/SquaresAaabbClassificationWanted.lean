/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.Group.Even

@[expose] public section

namespace MetaMathlibExt

/--
**Squares with two blocks of repeated digits.** Let $n$ be a perfect square whose decimal
representation, read from the most significant digit, consists of $r \ge 1$ copies of a digit
$a$ with $1 \le a \le 9$ followed by $s \ge 1$ copies of a digit $b$ with $0 \le b \le 9$. Then
$n$ is one of $16$, $25$, $36$, $49$, $64$, $81$, $144$, $225$, $441$, $1444$ and $7744$, or
there is a natural number $i$ such that $n = 10^{2i}$, $n = 4 \cdot 10^{2i}$ or
$n = 9 \cdot 10^{2i}$.

Source: Omar Kihel and Florian Luca, "Perfect Powers With All Equal Digits
But One," Journal of Integer Sequences 8 (2005), Article 05.5.7, Theorem
(label thm:3), lines 273–279,
https://cs.uwaterloo.ca/journals/JIS/VOL8/Kihel/kihel7.tex
-/
public theorem_wanted squares_aaabb_classification
    (n : ℕ) (hn : IsSquare n)
    (h : ∃ a b r s : ℕ, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 1 ≤ r ∧ 1 ≤ s ∧
      Nat.digits 10 n = List.replicate s b ++ List.replicate r a) :
    n = 16 ∨ n = 25 ∨ n = 36 ∨ n = 49 ∨ n = 64 ∨ n = 81 ∨ n = 144 ∨
    n = 225 ∨ n = 441 ∨ n = 1444 ∨ n = 7744 ∨
    (∃ i, n = 10 ^ (2 * i)) ∨ (∃ i, n = 4 * 10 ^ (2 * i)) ∨
    (∃ i, n = 9 * 10 ^ (2 * i))

end MetaMathlibExt
