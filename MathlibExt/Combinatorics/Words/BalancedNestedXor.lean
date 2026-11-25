/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Nested indices in balanced binary sequences
-/

namespace MetaMathlibExt

/-- **Nested indices in balanced binary sequences.** Let $a : \mathbb{N} \to \{0, 1\}$ satisfy
$a(2n) + a(2n+1) = 1$ for every $n \in \mathbb{N}$, and write $\oplus$ for addition modulo $2$.
Then for every $n \in \mathbb{N}$, $a(2n + a(n)) = a(2n) \oplus a(n)$ and
$a(2n + 1 - a(n)) = a(2n+1) \oplus a(n)$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 5 (`jis-2026-26.4.1-lem-5`). -/
public theorem balanced_nested_xor (a : ℕ → Bool)
    (ha : ∀ n, (a (2 * n)).toNat + (a (2 * n + 1)).toNat = 1) (n : ℕ) :
    a (2 * n + (a n).toNat) = xor (a (2 * n)) (a n) ∧
      a (2 * n + 1 - (a n).toNat) = xor (a (2 * n + 1)) (a n) := by
  have hpair : a (2 * n + 1) = !a (2 * n) := by
    cases h : a (2 * n) <;> simpa [h] using ha n
  cases a n <;> simp [hpair]

end MetaMathlibExt
