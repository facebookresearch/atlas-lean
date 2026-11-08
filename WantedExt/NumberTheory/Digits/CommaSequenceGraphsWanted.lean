/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.NumberTheory.CommaSequence

namespace MetaMathlibExt

@[expose] public section

/-- Landmines: in base `b ≥ 2`, a positive integer `n` has no comma-successor (equivalently no
comma-child) iff its base-`b` representation is `(b-1)…(b-1) x y` with `i ≥ 0` leading digits
`b - 1`, `1 ≤ x ≤ b - 2` and `y = b - 1 - x`. `Nat.digits` lists digits least significant
first. "No comma-child" is `IsCommaTerminal b n` (no digit `y` with
`n + b·(n mod b) + y` having leading digit `y`).

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.1 (`fq-2024-sloane05302024-thm-5.1`). -/
public theorem_wanted isCommaTerminal_iff_digits (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) :
    IsCommaTerminal b n ↔ ∃ i x : ℕ, 1 ≤ x ∧ x ≤ b - 2 ∧
      Nat.digits b n = [b - 1 - x, x] ++ List.replicate i (b - 1)

/-- Numbers with two comma-children, in base `b ≥ 2`: (a) a positive `n < b²` has two children
iff `n = w·b + x` with `1 ≤ x`, `2x ≤ b - 1` and `w = b - 1 - 2x` (so `0 ≤ w ≤ b - 3`);
(b) an `n ≥ b²` has two children iff its base-`b` representation is
`d (b-1)…(b-1) d (b-1-d)` with `1 ≤ d ≤ b - 2` and `i ≥ 0` digits `b - 1` (digits listed least
significant first below). A child of `k` is `k + b·(k mod b) + y` for a digit `y` that is its
leading digit (`IsCommaCandidate`); distinct digits give distinct children.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.2 (`fq-2024-sloane05302024-thm-5.2`). -/
public theorem_wanted two_commaChildren_iff (b : ℕ) (hb : 2 ≤ b) :
    (∀ n : ℕ, 0 < n → n < b ^ 2 →
      ((∃ y₁ y₂ : Fin b, y₁ ≠ y₂ ∧ IsCommaCandidate b n y₁ ∧ IsCommaCandidate b n y₂) ↔
        ∃ x : ℕ, 1 ≤ x ∧ 2 * x ≤ b - 1 ∧ n = (b - 1 - 2 * x) * b + x)) ∧
    ∀ n : ℕ, b ^ 2 ≤ n →
      ((∃ y₁ y₂ : Fin b, y₁ ≠ y₂ ∧ IsCommaCandidate b n y₁ ∧ IsCommaCandidate b n y₂) ↔
        ∃ d i : ℕ, 1 ≤ d ∧ d ≤ b - 2 ∧
          Nat.digits b n = [b - 1 - d, d] ++ List.replicate i (b - 1) ++ [d])

/-- Recovering the parent: in base `b ≥ 2`, if `n` is a comma-child of a positive `k` then
`k = n - x·b - f`, where `f = δ(n)` is the leading digit of `n` and `x = (n - f) mod b`; in
particular, if `n - x·b - f < 0` then `n` is not a comma-child of any positive integer.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Lemma 5.3 (`fq-2024-sloane05302024-lem-5.3`). -/
public theorem_wanted commaChild_parent_eq (b n : ℕ) (hb : 2 ≤ b) :
    (∀ k : ℕ, 0 < k → (∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val) →
      (k : ℤ) = n - ((n - commaMsd b n) % b : ℕ) * b - commaMsd b n) ∧
    ((n : ℤ) - ((n - commaMsd b n) % b : ℕ) * b - commaMsd b n < 0 →
      ¬ ∃ k : ℕ, 0 < k ∧ ∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val)

/-- In base `b ≥ 3`, the numbers `n ≥ b² - 1` that are not the comma-successor of any positive
integer are exactly `c·bⁱ` with `i ≥ 2` and `2 ≤ c ≤ b - 1`.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.4 (`fq-2024-sloane05302024-thm-5.4`). -/
public theorem_wanted not_commaSucc_iff (b n : ℕ) (hb : 3 ≤ b) (hn : b ^ 2 - 1 ≤ n) :
    (¬ ∃ k : ℕ, 0 < k ∧ IsCommaSucc b k n) ↔
      ∃ c i : ℕ, 2 ≤ i ∧ 2 ≤ c ∧ c ≤ b - 1 ∧ n = c * b ^ i

/-- In base `b ≥ 2`, every `n ≥ b²` is a comma-child of some positive integer (the numbers that
are not comma-children all lie in `1 ≤ n ≤ b² - 1`).

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.5 (`fq-2024-sloane05302024-thm-5.5`). -/
public theorem_wanted exists_commaParent_of_sq_le (b n : ℕ) (hb : 2 ≤ b) (hn : b ^ 2 ≤ n) :
    ∃ k : ℕ, 0 < k ∧ ∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val

/-- For every base `b ≥ 2` the comma-child graph `G_c` (positive integers, an edge from `k` to
each comma-child of `k`) contains an infinite path.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.6 (`fq-2024-sloane05302024-thm-5.6`). -/
public theorem_wanted exists_infinite_commaChild_path (b : ℕ) (hb : 2 ≤ b) :
    ∃ a : ℕ → ℕ, (∀ i, 0 < a i) ∧
      ∀ i, ∃ y : Fin b, IsCommaCandidate b (a i) y ∧ a (i + 1) = a i + b * (a i % b) + y.val

/-- There is a unique infinite path in the base-3 comma-child graph starting at `1`. The
paper's construction rule (alternate the lower and the higher child at branch points) is
omitted.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 10.1 (`fq-2024-sloane05302024-thm-10.1`). -/
public theorem_wanted existsUnique_commaChild_path_base_three :
    ∃! a : ℕ → ℕ, a 0 = 1 ∧
      ∀ i, ∃ y : Fin 3, IsCommaCandidate 3 (a i) y ∧ a (i + 1) = a i + 3 * (a i % 3) + y.val

end

end MetaMathlibExt
