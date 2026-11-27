/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CommaSequence

/-!
# Recovering the parent of a comma-child

`MetaMathlibExt.commaChild_parent_eq` recovers a parent from the digits of its child and
rules out a positive parent when the formula gives a negative integer.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Recovering the parent of a comma-child.** Fix a base $b \ge 2$ and a natural number $n$.
Call $n$ a comma-child of $k$ if $n = k + b\,(k \bmod b) + y$ for some comma candidate digit $y$
of $k$ in base $b$. Let $f$ be the most significant base-$b$ digit of $n$ and let
$x = (n - f) \bmod b$. If $n$ is a comma-child of a positive integer $k$, then
$k = n - x b - f$; and if the integer $n - x b - f$ is negative, then $n$ is not a comma-child
of any positive integer.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Lemma 5.3 (`fq-2024-sloane05302024-lem-5.3`). -/
public theorem commaChild_parent_eq (b n : ℕ) (hb : 2 ≤ b) :
    (∀ k : ℕ, 0 < k → (∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val) →
      (k : ℤ) = n - ((n - commaMsd b n) % b : ℕ) * b - commaMsd b n) ∧
    ((n : ℤ) - ((n - commaMsd b n) % b : ℕ) * b - commaMsd b n < 0 →
      ¬ ∃ k : ℕ, 0 < k ∧ ∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val) := by
  refine (and_iff_left_of_imp ?_).2 ?_
  · rintro recover hneg ⟨k, hk, y, hy, hn⟩
    rw [← recover k hk ⟨y, hy, hn⟩] at hneg
    omega
  · rintro k _ ⟨y, hy, rfl⟩
    rw [hy.2, Nat.add_sub_cancel, Nat.add_mul_mod_self_left]
    simp only [Int.natCast_add, Int.natCast_mul, Int.mul_comm (b : ℤ)]
    omega

end MetaMathlibExt
