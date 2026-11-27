/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.Order

@[expose] public section

namespace MetaMathlibExt

/-- **C-finite integer sequences.** An integer sequence $s \colon \mathbb{N} \to \mathbb{Z}$ is
C-finite if there are $p, q \in \mathbb{N}$ and integers $c_0, \dots, c_{p-1}$ such that
$s(n + p) = \sum_{i=0}^{p-1} c_i \, s(n + i)$ for every $n \ge q$.

Source: JIS VOL26/Fischer–Kotek–Makowsky,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>, lines 249–259;
concept `jis_term_8dfeefcfa70ce96efa8b4fb3`. -/
def IsIntegerCFiniteSequence (s : ℕ → ℤ) : Prop :=
  ∃ p q, ∃ c : Fin p → ℤ, ∀ n, q ≤ n → s (n + p) = ∑ i, c i * s (n + (i : ℕ))

/-- **Solutions of linear recurrences are C-finite.** Let $p \in \mathbb{N}$ and let
$c_0, \dots, c_{p-1}$ be integers. If an integer sequence $s$ satisfies
$s(n + p) = \sum_{i=0}^{p-1} c_i \, s(n + i)$ for every $n \in \mathbb{N}$, then $s$ is C-finite. -/
theorem isIntegerCFiniteSequence_of_isSolution (E : LinearRecurrence ℤ) (s : ℕ → ℤ)
    (h : E.IsSolution s) : IsIntegerCFiniteSequence s :=
  ⟨E.order, 0, E.coeffs, fun n _ => h n⟩

/-- **Discarding the exceptional prefix of a C-finite recurrence.** Let $s$ be an integer
sequence, let $p, q \in \mathbb{N}$ and let $c_0, \dots, c_{p-1}$ be integers. If
$s(n + p) = \sum_{i=0}^{p-1} c_i \, s(n + i)$ for every $n \ge q$, then the shifted sequence
$t(n) = s(n + q)$ satisfies $t(n + p) = \sum_{i=0}^{p-1} c_i \, t(n + i)$ for every
$n \in \mathbb{N}$. -/
theorem isSolution_tail_of_cFiniteWitness (s : ℕ → ℤ) (p q : ℕ) (c : Fin p → ℤ)
    (h : ∀ n, q ≤ n → s (n + p) = ∑ i, c i * s (n + (i : ℕ))) :
    (LinearRecurrence.mk p c).IsSolution (fun n => s (n + q)) := by
  intro n
  have hn : q ≤ n + q := by omega
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (n + q) hn

/-- **A tail of a C-finite sequence satisfies a linear recurrence.** If an integer sequence $s$
is C-finite, then there are a shift $q \in \mathbb{N}$, an order $p \in \mathbb{N}$ and integers
$c_0, \dots, c_{p-1}$ such that the shifted sequence $t(n) = s(n + q)$ satisfies
$t(n + p) = \sum_{i=0}^{p-1} c_i \, t(n + i)$ for every $n \in \mathbb{N}$. -/
theorem IsIntegerCFiniteSequence.exists_isSolution_tail {s : ℕ → ℤ}
    (h : IsIntegerCFiniteSequence s) :
    ∃ (E : LinearRecurrence ℤ) (q : ℕ), E.IsSolution (fun n => s (n + q)) := by
  obtain ⟨p, q, c, hc⟩ := h
  exact ⟨LinearRecurrence.mk p c, q, isSolution_tail_of_cFiniteWitness s p q c hc⟩

end MetaMathlibExt
