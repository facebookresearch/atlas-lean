/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.Order

namespace MetaMathlibExt

@[expose] public section

/-- **Van der Laan windows.** Four natural numbers $a, b, c, d$ form a Van der Laan window when
the largest of them equals the sum of the two smallest, that is, when
$\max(a, b, c, d) = \min(a + b, a + c, a + d, b + c, b + d, c + d)$.

The minimum of the six pair sums is the sum of the two smallest of the four values counted with
multiplicity, so repeated values are handled correctly.

Source: concept `jis_term_73e55616c68e02e09fa349b5`, raw phrase rank 204 `laan sequence`,
`/data/users/akiezun/jis_corpus/artifacts/a6b5613ec29d7f2bcc9e-nacin5.tex`
(SHA-256 `52008805cb731f6d0e329d46c8da38ea6055d8ced9031f7a81cf630ddd7b69a1`),
lines 92-96. The source calls a non-negative sequence Van der Laan when, for every four
consecutive terms, the largest term equals the sum of the two smallest (conjecture from the
OEIS entry; only the predicate is formalized here). -/
public def IsVanDerLaanWindow (a b c d : ℕ) : Prop :=
  max (max a b) (max c d)
    = min (min (a + b) (a + c)) (min (min (a + d) (b + c)) (min (b + d) (c + d)))

/-- **Van der Laan sequences.** A sequence $s \colon \mathbb{N} \to \mathbb{N}$ is a Van der Laan
sequence when, for every $n \in \mathbb{N}$, the four consecutive terms
$s(n), s(n + 1), s(n + 2), s(n + 3)$ form a Van der Laan window, that is, the largest of them
equals the sum of the two smallest.

Source: concept `jis_term_73e55616c68e02e09fa349b5`, source lines 92-96. -/
public def IsVanDerLaan (s : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, IsVanDerLaanWindow (s n) (s (n + 1)) (s (n + 2)) (s (n + 3))

/-- **Van der Laan windows in increasing order.** Let $a \le b \le c \le d$ be natural numbers.
Then $a, b, c, d$ form a Van der Laan window if and only if $d = a + b$.

Source: concept `jis_term_73e55616c68e02e09fa349b5`; local reduction used by source
lines 120-124 for increasing sequences. -/
public theorem isVanDerLaanWindow_ordered_iff {a b c d : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hcd : c ≤ d) : IsVanDerLaanWindow a b c d ↔ d = a + b := by
  have hmax : max (max a b) (max c d) = d := by omega
  have hmin : min (min (a + b) (a + c)) (min (min (a + d) (b + c)) (min (b + d) (c + d)))
      = a + b := by omega
  unfold IsVanDerLaanWindow
  rw [hmax, hmin]

/-- **Constant Van der Laan windows.** For a natural number $k$, the window $k, k, k, k$ is a
Van der Laan window if and only if $k = 0$.

Its largest value is $k$ and the sum of its two smallest values is $k + k$.

Source: concept `jis_term_73e55616c68e02e09fa349b5`. -/
public theorem isVanDerLaanWindow_const_iff {k : ℕ} :
    IsVanDerLaanWindow k k k k ↔ k = 0 := by
  have hmax : max (max k k) (max k k) = k := by omega
  have hmin : min (min (k + k) (k + k)) (min (min (k + k) (k + k)) (min (k + k) (k + k)))
      = k + k := by omega
  unfold IsVanDerLaanWindow
  rw [hmax, hmin]
  constructor <;> intro h <;> omega

/-- **Constant Van der Laan sequences.** For a natural number $k$, the constant sequence
$s \colon \mathbb{N} \to \mathbb{N}$ with $s(n) = k$ for all $n$ is a Van der Laan sequence if and
only if $k = 0$.

In particular the identically zero sequence, one of the alternatives in the source conjecture,
is a Van der Laan sequence.

Source: concept `jis_term_73e55616c68e02e09fa349b5`, source lines 92-96. -/
public theorem isVanDerLaan_const_iff {k : ℕ} :
    IsVanDerLaan (fun _ => k) ↔ k = 0 := by
  constructor
  · intro h
    have h0 : IsVanDerLaanWindow k k k k := h 0
    exact isVanDerLaanWindow_const_iff.mp h0
  · intro hk n
    subst hk
    change IsVanDerLaanWindow 0 0 0 0
    unfold IsVanDerLaanWindow
    decide

end

end MetaMathlibExt
