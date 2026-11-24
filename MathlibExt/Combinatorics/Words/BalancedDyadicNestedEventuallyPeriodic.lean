/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Balanced sequences with a nested doubling recurrence

A binary sequence $a : \mathbb{N} \to \{0, 1\}$ is *balanced* if $a(2n) + a(2n+1) = 1$ for every
$n \in \mathbb{N}$. This file shows that a balanced sequence satisfying the nested recurrence
$a(2n) = a(n + a(n))$, or the nested recurrence $a(2n) = a(n + 1 - a(n))$, has a forced value
at $0$ and alternates from index $4$ on.

## Main statements

* `MetaMathlibExt.balanced_dyadic_nested_eventually_periodic`: both parts of the lemma.

## Implementation notes

Part (a) is proved by strong induction on $n \ge 2$. The recurrence gives $a(2n) = a(n) = 0$
when $a(n) = 0$, and $a(2n) = a(n + 1)$ when $a(n) = 1$; in the latter case $a(n + 1) = 0$ by
balance when $n$ is even, and by the induction hypothesis at $(n + 1) / 2$ when $n$ is odd.
Part (b) follows by applying part (a) to the complementary sequence, as in the source.

## References

* John M. Campbell and Benoît Cloitre, *Meta-automatic sequences*, arXiv:2602.23395 (v2),
  Lemma 6.
-/

namespace MetaMathlibExt

namespace balanced_dyadic_nested_eventually_periodic

/-- Part (a): a balanced binary sequence with $a(2n) = a(n + a(n))$ for every $n$ satisfies
$a(0) = 0$, and $a(2n) = 0$ and $a(2n+1) = 1$ for every $n \ge 2$. -/
private theorem part_a (a : ℕ → Bool)
    (ha : ∀ n, (a (2 * n)).toNat + (a (2 * n + 1)).toNat = 1)
    (h : ∀ n, a (2 * n) = a (n + (a n).toNat)) :
    a 0 = false ∧ ∀ n, 2 ≤ n → a (2 * n) = false ∧ a (2 * n + 1) = true := by
  have hpair (n : ℕ) : a (2 * n + 1) = !a (2 * n) := by
    cases h2n : a (2 * n) <;> simpa [h2n] using ha n
  have heven (n : ℕ) : 2 ≤ n → a (2 * n) = false := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      cases han : a n
      · simpa [han] using h n
      · -- Here `a (2 * n) = a (n + 1)`; split on the parity of `n`.
        rw [h n, han, Bool.toNat_true]
        obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
        · rw [hpair, han, Bool.not_true]
        · rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
          exact ih (k + 1) (by omega) (by omega)
  refine ⟨?_, fun n hn => ⟨heven n hn, by rw [hpair, heven n hn, Bool.not_false]⟩⟩
  -- At `n = 0` the recurrence reads `a 0 = a (a 0)`, which excludes `a 0 = true`.
  have h0 := h 0
  have p0 := hpair 0
  cases h' : a 0 <;> simp_all

end balanced_dyadic_nested_eventually_periodic

/-- **Balanced sequences with a nested doubling recurrence are eventually alternating.** Let
$a : \mathbb{N} \to \{0, 1\}$ satisfy $a(2n) + a(2n+1) = 1$ for every $n \in \mathbb{N}$.
(a) If $a(2n) = a(n + a(n))$ for every $n$, then $a(0) = 0$, and $a(2n) = 0$ and
$a(2n+1) = 1$ for every $n \ge 2$. (b) If $a(2n) = a(n + 1 - a(n))$ for every $n$, then
$a(0) = 1$, and $a(2n) = 1$ and $a(2n+1) = 0$ for every $n \ge 2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 6 (`jis-2026-26.4.1-lem-6`). -/
public theorem balanced_dyadic_nested_eventually_periodic (a : ℕ → Bool)
    (ha : ∀ n, (a (2 * n)).toNat + (a (2 * n + 1)).toNat = 1) :
    ((∀ n, a (2 * n) = a (n + (a n).toNat)) →
        a 0 = false ∧ ∀ n, 2 ≤ n → a (2 * n) = false ∧ a (2 * n + 1) = true) ∧
      ((∀ n, a (2 * n) = a (n + 1 - (a n).toNat)) →
        a 0 = true ∧ ∀ n, 2 ≤ n → a (2 * n) = true ∧ a (2 * n + 1) = false) := by
  refine ⟨balanced_dyadic_nested_eventually_periodic.part_a a ha, fun h => ?_⟩
  -- The complementary sequence is balanced and satisfies the recurrence of part (a).
  have hb := balanced_dyadic_nested_eventually_periodic.part_a (fun n => !a n)
    (fun n => by
      have hn := ha n
      change (!a (2 * n)).toNat + (!a (2 * n + 1)).toNat = 1
      revert hn
      cases a (2 * n) <;> cases a (2 * n + 1) <;> decide)
    (fun n => by cases han : a n <;> simpa [han] using h n)
  simpa only [Bool.not_eq_false', Bool.not_eq_true'] using hb

end MetaMathlibExt
