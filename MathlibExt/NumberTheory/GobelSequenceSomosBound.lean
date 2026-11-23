/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelSequence
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Somos-type sequences lie below Göbel sequences

Let $k, l \ge 2$ and let $t$ be a real sequence with $t(n + 1) = t(n)^k / (n + 1)$ and
$t(0)^k \le l$. Then $t$ lies below the $(k, l)$-Göbel sequence $g_{k,l}$ from index $1$ on. At
index $1$ this is $t(1) = t(0)^k \le l = g_{k,l}(1)$. For the induction step, the Göbel recurrence
reads $(n + 1) g_{k,l}(n + 1) = n g_{k,l}(n) + g_{k,l}(n)^k$ with $g_{k,l}(n) > 0$, while
$t(n)^k \le g_{k,l}(n)^k$ follows from $t(n) \le g_{k,l}(n)$: for even $k$ the term $t(n)$ is a
$k$-th power divided by $n$, hence nonnegative, and for odd $k$ the map $x \mapsto x^k$ is
monotone.

In the arXiv version of the source (Gima, Matsusaka, Miyazaki and Yara, arXiv:2402.09064v1)
this is Lemma 3.3, where Somos-like sequences are defined only for $t(0) > 1$.
-/

namespace MetaMathlibExt

/-- **Somos-type sequences lie below Göbel sequences.** Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $t : \mathbb{N} \to \mathbb{R}$ satisfy
$t(n + 1) = t(n)^k / (n + 1)$ for all $n \ge 0$. If $t(0)^k \le l$, then $t(n) \le g_{k,l}(n)$
for every $n \ge 1$.

The paper also assumes $t(0) > 1$; the statement holds without it (for even $k$, $t(n) \ge 0$
for $n \ge 1$; for odd $k$, $x \mapsto x^k$ is monotone), so that hypothesis is dropped.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 9 (`jis-2024-24.8.1-lem-9`). -/
public theorem somosLike_le_gobelSequence (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (t : ℕ → ℝ) (ht : ∀ n : ℕ, t (n + 1) = t n ^ k / (n + 1)) (h0 : t 0 ^ k ≤ l)
    (n : ℕ) (hn : 1 ≤ n) :
    t n ≤ gobelSequence k l n := by
  -- The Göbel sequence is positive from index 1 on.
  have hpos : ∀ m : ℕ, 1 ≤ m → 0 < gobelSequence k l m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rw [gobelSequence_one]
      exact Nat.cast_pos.mpr (by omega)
    | succ m hm ih =>
      have h : 0 < (m + 1 : ℚ) * gobelSequence k l (m + 1) := by
        rw [gobelSequence_succ k l m hm]
        exact mul_pos ih (add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) (pow_pos ih _))
      exact pos_of_mul_pos_right h (by positivity)
  induction n, hn using Nat.le_induction with
  | base =>
    have h1 : t 1 = t 0 ^ k := by simpa using ht 0
    rw [h1, gobelSequence_one]
    exact_mod_cast h0
  | succ n hn ih =>
    have hg : (0 : ℝ) < gobelSequence k l n := by
      exact_mod_cast hpos n hn
    -- Raising `t n ≤ g n` to the `k`-th power: `t n ≥ 0` for even `k`, and odd powers are monotone.
    have hpow : t n ^ k ≤ (gobelSequence k l n : ℝ) ^ k := by
      rcases Nat.even_or_odd k with hke | hko
      · have htn : 0 ≤ t n := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [ht m]
          exact div_nonneg (hke.pow_nonneg _) (by positivity)
        exact pow_le_pow_left₀ htn ih k
      · exact hko.pow_le_pow.mpr ih
    -- The Göbel recurrence: `(n + 1) g (n + 1) = n g n + g n ^ k`.
    have hrec : ((n : ℝ) + 1) * gobelSequence k l (n + 1) =
        gobelSequence k l n * ((n : ℝ) + (gobelSequence k l n : ℝ) ^ (k - 1)) := by
      have h := congrArg (Rat.cast : ℚ → ℝ) (gobelSequence_succ k l n hn)
      push_cast at h
      exact h
    rw [ht n, div_le_iff₀' (by positivity), hrec, mul_add, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ k)]
    linarith [mul_nonneg hg.le (Nat.cast_nonneg (α := ℝ) n)]

end MetaMathlibExt
