/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion

/-!
# Agreement of shifted Padovan–Perrin solutions

A window of one recurrence order determines the shifted solutions on the rest of the tail.
-/

namespace MetaMathlibExt

variable {R : Type*}

/-- **Solutions agreeing on a window agree afterwards.** Let $R$ be a commutative ring, let
$k_1, k_2 \in R$, let $p, s$ be natural numbers and let $v, w \colon \mathbb{N} \to R$ be solutions
of the Padovan–Perrin recurrence with parameters $k_1, k_2, p, s$. Let $n_0, m_0, N$ be natural
numbers such that $v(j + n_0) = w(j + m_0)$ for every $j$ with $N \le j < N + s + p$. Then
$v(n + n_0) = w(n + m_0)$ for every $n \ge N$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 1 (`integers-2024-A49-lem-1`). -/
public theorem padovanPerrin_shift_eq_of_window [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    {v w : ℕ → R}
    (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v)
    (hw : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution w) (n₀ m₀ N : ℕ)
    (h : ∀ j, N ≤ j → j < N + (s + p) → v (j + n₀) = w (j + m₀)) :
    ∀ n, N ≤ n → v (n + n₀) = w (n + m₀) := by
  let E := padovanPerrinRecurrence k₁ k₂ p s
  have horder : E.order = s + p := rfl
  change E.IsSolution v at hv
  change E.IsSolution w at hw
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    by_cases hwin : n < N + (s + p)
    · exact h n hn hwin
    let t := n - E.order
    have ht (a : ℕ) : t + a + E.order = n + a := by
      dsimp only [t]
      omega
    rw [← ht n₀, ← ht m₀, hv (t + n₀), hw (t + m₀)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [Nat.add_right_comm t n₀ (i : ℕ), Nat.add_right_comm t m₀ (i : ℕ),
      ih (t + (i : ℕ)) (by dsimp only [t]; omega) (by dsimp only [t]; omega)]

end MetaMathlibExt
