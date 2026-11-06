/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SmoothNumbers

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/-- **Sum-product sets cover the integers modulo a prime.** Let $p$ be a prime and let
$A_1, A_2, A_3, D$ be subsets of $\mathbb{Z}/p\mathbb{Z}$ with $|A_1| |A_2| |A_3| |D| > p^3$.
Then every residue class modulo $p$ can be written as $a_1 d + a_2 + a_3$ with $a_1 \in A_1$,
$d \in D$, $a_2 \in A_2$ and $a_3 \in A_3$; that is, $A_1 D + A_2 + A_3 = \mathbb{Z}/p\mathbb{Z}$.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 3
(`integers-2026-A14-lem-3`), quoting Lemma 8.3 of their reference [5] (a consequence of
Sárközy's Corollary A). -/
public theorem_wanted product_add_add_eq_univ_of_card_mul_gt (p : ℕ) [Fact p.Prime]
    (A₁ A₂ A₃ D : Finset (ZMod p))
    (h : p ^ 3 < A₁.card * A₂.card * A₃.card * D.card) :
    A₁ * D + A₂ + A₃ = Finset.univ

/-! Notation for the statements below. The paper's set of `B^η`-smooth numbers
`A(B, B^η) = {x ∈ [1, B] ∩ ℤ : every prime q ∣ x has q ≤ B^η}` is
`Nat.smoothNumbersUpTo B (⌊(B : ℝ) ^ η⌋₊ + 1)` (Mathlib's smooth numbers use a strict
bound, and a prime `q` satisfies `q ≤ B^η` iff `q < ⌊B^η⌋₊ + 1`). The threshold
`s_0(k)` of Theorem 2 is `5` for `k = 2`, `8` for `k = 3`, and
`k (log k + log log k + 2 + g k)` for `k ≥ 4`, where `g k = O(log log k / log k)`; the
function `g` is existentially quantified in each statement. -/

/-- **Diagonal congruences in $k$ variables are solvable.** Let $p$ be a prime and $k \ge 1$. For
all integers $a_1, \dots, a_k$ not divisible by $p$ and every integer $c$, there are integers
$x_1, \dots, x_k$ with $a_1 x_1^k + \dots + a_k x_k^k \equiv c \pmod p$.

Equivalently, $\Gamma(k, p) \le k$, where $\Gamma(k, p)$ is the least $n$ such that every such
congruence in $n$ variables is solvable; extra variables can be set to $0$.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 2 (`integers-2026-A14-lem-2`). -/
public theorem_wanted diagonal_congruence_solvable_of_card_eq_exponent (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hk : 1 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (c : ℤ) :
    ∃ x : Fin k → ℤ, ∑ i, a i * x i ^ k ≡ c [ZMOD p]

/-- **Smooth solutions of diagonal equations (Chow–Lindqvist–Prendiville).** For a natural number
$N$ and real $\eta > 0$, let $A(N, N^\eta)$ be the set of integers $1 \le x \le N$ all of whose
prime factors are at most $N^\eta$. There is a real-valued function $g$ on the natural numbers
with $g(k) = O(\log \log k / \log k)$ as $k \to \infty$ such that for every $k \ge 2$ there is
$\eta_0 > 0$ with the following property. Let $c_1, \dots, c_s$ be nonzero integers such that
$\sum_{i \in I} c_i = 0$ for some nonempty $I \subseteq \{1, \dots, s\}$, and suppose $s \ge 5$
if $k = 2$, $s \ge 8$ if $k = 3$, and $s \ge k (\log k + \log \log k + 2 + g(k))$ if $k \ge 4$.
Then for every $0 < \eta \le \eta_0$ there are a natural number $N_0$ and constants
$C_1, C_2 > 0$ such that for all $N \ge N_0$ the number of $x \in A(N, N^\eta)^s$ with
$c_1 x_1^k + \dots + c_s x_s^k = 0$ is at least $C_1 N^{s-k}$ and at most $C_2 N^{s-k}$.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Theorem 2 (`integers-2026-A14-thm-2`), quoting Chow, Lindqvist and Prendiville,
*Rado's criterion over squares and higher powers*, J. Eur. Math. Soc. 23 (2021),
Theorem B.1. -/
public theorem_wanted smooth_diagonal_solution_count_asymp :
    ∃ g : ℕ → ℝ, (g =O[Filter.atTop] fun k : ℕ => Real.log (Real.log k) / Real.log k) ∧
      ∀ k : ℕ, 2 ≤ k → ∃ η₀ : ℝ, 0 < η₀ ∧
        ∀ (s : ℕ) (c : Fin s → ℤ), (∀ i, c i ≠ 0) →
          (∃ I : Finset (Fin s), I.Nonempty ∧ ∑ i ∈ I, c i = 0) →
          (k = 2 → 5 ≤ s) → (k = 3 → 8 ≤ s) →
          (4 ≤ k → (k : ℝ) * (Real.log k + Real.log (Real.log k) + 2 + g k) ≤ s) →
          ∀ η : ℝ, 0 < η → η ≤ η₀ →
            ∃ (N₀ : ℕ) (C₁ C₂ : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, N₀ ≤ N →
              C₁ * (N : ℝ) ^ ((s : ℝ) - k) ≤
                (((Fintype.piFinset fun _ : Fin s =>
                    Nat.smoothNumbersUpTo N (⌊(N : ℝ) ^ η⌋₊ + 1)).filter
                  fun x => ∑ i, c i * (x i : ℤ) ^ k = 0).card : ℝ) ∧
              (((Fintype.piFinset fun _ : Fin s =>
                    Nat.smoothNumbersUpTo N (⌊(N : ℝ) ^ η⌋₊ + 1)).filter
                  fun x => ∑ i, c i * (x i : ℤ) ^ k = 0).card : ℝ) ≤
                C₂ * (N : ℝ) ^ ((s : ℝ) - k)

/-- **Many values of a smooth diagonal form modulo a prime.** For a natural number $B$ and real
$\eta > 0$, let $A(B, B^\eta)$ be the set of integers $1 \le x \le B$ all of whose prime factors
are at most $B^\eta$. There is a real-valued function $g$ on the natural numbers with
$g(k) = O(\log \log k / \log k)$ as $k \to \infty$ such that for every $k \ge 2$ there is
$\eta_0 > 0$ with the following property. Let $0 < \eta \le \eta_0$ and let $n \ge 1$ satisfy
$2n \ge 5$ if $k = 2$, $2n \ge 8$ if $k = 3$, and $2n \ge k (\log k + \log \log k + 2 + g(k))$
if $k \ge 4$. Then there is $C > 0$ such that for every prime $p$, every natural number $B \ge 1$
with $n B^k \le p$ and all integers $a_1, \dots, a_n$ not divisible by $p$, the set of residues
modulo $p$ of $a_1 x_1^k + \dots + a_n x_n^k$ with $x \in A(B, B^\eta)^n$ has at least $C B^k$
elements.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 1 (`integers-2026-A14-lem-1`). -/
public theorem_wanted card_smooth_diagonal_values_ge :
    ∃ g : ℕ → ℝ, (g =O[Filter.atTop] fun k : ℕ => Real.log (Real.log k) / Real.log k) ∧
      ∀ k : ℕ, 2 ≤ k → ∃ η₀ : ℝ, 0 < η₀ ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ n : ℕ, 1 ≤ n →
          (k = 2 → 5 ≤ 2 * n) → (k = 3 → 8 ≤ 2 * n) →
          (4 ≤ k → (k : ℝ) * (Real.log k + Real.log (Real.log k) + 2 + g k) ≤ 2 * n) →
          ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (B : ℕ), 1 ≤ B → n * B ^ k ≤ p →
            ∀ a : Fin n → ℤ, (∀ i, ¬ (p : ℤ) ∣ a i) →
              C * (B : ℝ) ^ k ≤
                (((Fintype.piFinset fun _ : Fin n =>
                    Nat.smoothNumbersUpTo B (⌊(B : ℝ) ^ η⌋₊ + 1)).image
                  fun x => ∑ i, (a i : ZMod p) * (x i : ZMod p) ^ k).card : ℝ)

/-- **Small solutions of diagonal congruences.** There is a real-valued function $g$ on the natural
numbers with $g(k) = O(\log \log k / \log k)$ as $k \to \infty$ such that for every $k \ge 2$
there is a constant $C > 0$ with the following property. Let $n$ satisfy $n \ge 9$ if $k = 2$,
$n \ge 12$ if $k = 3$, and $n \ge \frac{3}{2} k (\log k + \log \log k + 2 + g(k))$ if $k \ge 4$.
Then for every prime $p$, every integer $c$ and all integers $a_1, \dots, a_n$ not divisible by
$p$, the congruence $a_1 x_1^k + \dots + a_n x_n^k \equiv c \pmod p$ has a solution in natural
numbers $x_1, \dots, x_n$ with $1 \le x_i \le C p^{1/k}$ for every $i$.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Theorem 1 (`integers-2026-A14-thm-1`). -/
public theorem_wanted exists_small_solution_diagonal_congruence :
    ∃ g : ℕ → ℝ, (g =O[Filter.atTop] fun k : ℕ => Real.log (Real.log k) / Real.log k) ∧
      ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, (k = 2 → 9 ≤ n) → (k = 3 → 12 ≤ n) →
          (4 ≤ k → 3 / 2 * (k : ℝ) * (Real.log k + Real.log (Real.log k) + 2 + g k) ≤ n) →
          ∀ (p : ℕ) [Fact p.Prime] (c : ℤ) (a : Fin n → ℤ), (∀ i, ¬ (p : ℤ) ∣ a i) →
            ∃ x : Fin n → ℕ, (∀ i, 1 ≤ x i ∧ (x i : ℝ) ≤ C * (p : ℝ) ^ ((1 : ℝ) / k)) ∧
              ∑ i, a i * (x i : ℤ) ^ k ≡ c [ZMOD p]

end

end MetaMathlibExt
