/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Analytical study and efficient evaluation of the Josephus function

Statements from Yunier Bello-Cruz and Roy
Quintero-Contreras, "Analytical Study and Efficient
Evaluation of the Josephus Function", *Journal of Integer
Sequences* 27 (2024), Article 24.3.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Cruz/cruz4.html>).

The statements use the existing Josephus survivor
function `MetaMathlibExt.josephus` (`J_k(1) = 1`,
`J_k(n+1) = (J_k(n) + k - 1) % (n+1) + 1`). Following the
paper's usage (Lemma 8: "`j ∈ [[1, k-1]]`, i.e., `n+1` is
a low extremal point"; Corollary 7: "`n_e` is a high
extremal point and `n_e + 1` is a low extremal point"), a
point `m` is *low extremal* if `J_k(m) ∈ [1, k - 1]` and
*high extremal* if `m + 1` is low extremal. The
bounded-instance statements were verified by
simulation for `2 ≤ k ≤ 9`, `n ≤ 400`; for Theorem 13
the simulation only exhibits initial fixed points
(for `n ≤ 3000`) and does not verify infinitude.

Lemma 6(b) is stated with the additional single-wrap
hypothesis `J_k(n) + k * m ≤ 2 * (n + m)`: as extracted it
fails at `k = 4`, `n = 1`, `m = 1`, where the printed
formula gives `3 > n + m` but `J_4(2) = 1` (two wraps);
with the hypothesis it holds on the whole simulation
grid. Proposition 4 carries the domain hypothesis
`1 ≤ n_p`: at `n_p = 0` the recursion anchor
`J_k(0) = 0` is a spurious fixed point for which the
fourth case fails (`J_k(1) = 1 ≠ 0`). Not stated (see the
source audit table): Lemma 8(b), 8(c), Theorem 9(b),
9(c), 9(d), and Corollaries 10, 11, which use the paper's
auxiliary functions `δ_k`, `M_k`, `a_k` and the "next
extremal point" notation, none of which are defined in
the extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.JosephusWanted

/-- **Low extremal point of the Josephus function.** For natural numbers $k$ and $m$, the point
$m$ is a low extremal point of the Josephus function $J_k$ if $1 \le J_k(m) \le k - 1$, where
$k - 1$ is truncated at $0$. -/
def IsLowExtremal (k m : ℕ) : Prop :=
  1 ≤ MetaMathlibExt.josephus k m ∧
    MetaMathlibExt.josephus k m ≤ k - 1

/-- **High extremal point of the Josephus function.** For natural numbers $k$ and $m$, the point
$m$ is a high extremal point of the Josephus function $J_k$ if $m + 1$ is a low extremal point
of $J_k$, that is, if $1 \le J_k(m + 1) \le k - 1$. -/
def IsHighExtremal (k m : ℕ) : Prop := IsLowExtremal k (m + 1)

/-- **Josephus recurrence by number of wrap-arounds.** Let $k \ge 2$ and $n \ge 1$ be natural
numbers, let $J_k$ be the Josephus function and write $p = J_k(n)$. If $\ell$ is a natural
number with $\ell(n+1) + 1 \le p + k \le (\ell+1)(n+1)$, then $J_k(n+1) = p + k - \ell(n+1)$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 2. -/
theorem_wanted josephus_succ_eq_sub (k n ℓ : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n)
    (h : ℓ * (n + 1) + 1 ≤ MetaMathlibExt.josephus k n + k ∧
      MetaMathlibExt.josephus k n + k ≤ (ℓ + 1) * (n + 1)) :
    MetaMathlibExt.josephus k (n + 1) =
      MetaMathlibExt.josephus k n + k - ℓ * (n + 1)

/-- **The Josephus function just after a fixed point.** Let $k \ge 2$ and $n_p \ge 1$ be natural
numbers with $J_k(n_p) = n_p$, where $J_k$ is the Josephus function. Then $J_k(n_p + 1)$ is
determined as follows: (i) if $k \le n_p + 1$, then $J_k(n_p + 1) = k - 1$; (ii) if
$k = \ell(n_p + 1) + 1$ for some natural number $\ell \ge 1$, then $J_k(n_p + 1) = n_p + 1$;
(iii) if $k = \ell(n_p + 1) + k_1$ for some natural numbers $\ell \ge 1$ and $k_1$ with
$2 \le k_1 \le n_p$, then $J_k(n_p + 1) = k_1 - 1$; (iv) if $k = (\ell + 1)(n_p + 1)$ for some
natural number $\ell \ge 1$, then $J_k(n_p + 1) = n_p$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Proposition 4. -/
theorem_wanted josephus_fixed_succ_cases (k np : ℕ)
    (hk : 2 ≤ k) (hnp : 1 ≤ np)
    (hfix : MetaMathlibExt.josephus k np = np) :
    (k ≤ np + 1 → MetaMathlibExt.josephus k (np + 1) = k - 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → k = ℓ * (np + 1) + 1 →
      MetaMathlibExt.josephus k (np + 1) = np + 1) ∧
    (∀ ℓ k1 : ℕ, 1 ≤ ℓ → 2 ≤ k1 → k1 ≤ np →
      k = ℓ * (np + 1) + k1 →
        MetaMathlibExt.josephus k (np + 1) = k1 - 1) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → k = (ℓ + 1) * (np + 1) →
      MetaMathlibExt.josephus k (np + 1) = np)

/-- **Josephus fixed points detected by the next value.** Let $k \ge 2$ and $n_p$ be natural
numbers with $n_p \ge k - 1$, and let $J_k$ be the Josephus function. Then $J_k(n_p) = n_p$ if
and only if $J_k(n_p + 1) = k - 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Proposition 4. -/
theorem_wanted josephus_eq_self_iff (k np : ℕ) (hk : 2 ≤ k)
    (hnp : k - 1 ≤ np) :
    MetaMathlibExt.josephus k np = np ↔
      MetaMathlibExt.josephus k (np + 1) = k - 1

/-- **Linear growth of the Josephus function before a wrap-around.** Let $k \ge 2$, $n \ge 1$
and $m$ be natural numbers, let $J_k$ be the Josephus function and write $p = J_k(n)$. If
$p + km \le n + m$, then $J_k(n + m) = p + km$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 6. -/
theorem_wanted josephus_add_eq_of_le (k n m : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n)
    (h : MetaMathlibExt.josephus k n + k * m ≤ n + m) :
    MetaMathlibExt.josephus k (n + m) =
      MetaMathlibExt.josephus k n + k * m

/-- **The Josephus function at the first wrap-around.** Let $k \ge 2$, $n \ge 1$ and $m$ be
natural numbers and let $J_k$ be the Josephus function. Suppose that $m$ is the least natural
number with $J_k(n) + km > n + m$, and that moreover $J_k(n) + km \le 2(n + m)$. Then
$J_k(n + m) = J_k(n) + km - (n + m)$.

The second hypothesis, which allows only one wrap-around, is not in the printed lemma; without it
the statement fails at $k = 4$, $n = 1$, $m = 1$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 6. -/
theorem_wanted josephus_add_eq_sub_of_minimal (k n m : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n)
    (hmin : (∀ m' : ℕ, m' < m →
        MetaMathlibExt.josephus k n + k * m' ≤ n + m') ∧
      n + m < MetaMathlibExt.josephus k n + k * m)
    (hwrap : MetaMathlibExt.josephus k n + k * m ≤ 2 * (n + m)) :
    MetaMathlibExt.josephus k (n + m) =
      MetaMathlibExt.josephus k n + k * m - (n + m)

/-- **Extremal points of the Josephus function near $2k - 2$.** Let $k \ge 2$ be a natural
number and let $J_k$ be the Josephus function; call $m$ low extremal if $1 \le J_k(m) \le k - 1$,
and high extremal if $m + 1$ is low extremal. If $J_k(2k - 2) \le k - 1$, then $2k - 3$ is high
extremal and $2k - 2$ is low extremal. If $J_k(2k - 2) > k - 1$, then $2k - 2$ is high extremal
and $2k - 1$ is low extremal. In particular, $2k - 2$ is always a low or a high extremal point.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Corollary 7. -/
theorem_wanted extremal_two_mul_sub (k : ℕ) (hk : 2 ≤ k) :
    (MetaMathlibExt.josephus k (2 * k - 2) ≤ k - 1 →
      IsHighExtremal k (2 * k - 3) ∧
        IsLowExtremal k (2 * k - 2)) ∧
    (k - 1 < MetaMathlibExt.josephus k (2 * k - 2) →
      IsHighExtremal k (2 * k - 2) ∧
        IsLowExtremal k (2 * k - 1))

/-- **Linear-step bound at a low extremal point.** Let $k \ge 2$ and $n$ be natural numbers, let
$J_k$ be the Josephus function, write $j = J_k(n+1)$, and suppose $j \le k - 1$. Then for every
natural number $m$, $j + km \le n + 1 + m$ holds if and only if
$m \le \lfloor (n - (j - 1)) / (k - 1) \rfloor$. Moreover, if $k - 2 + j \le n$, then
$\lfloor (n - (j - 1)) / (k - 1) \rfloor \ge 1$.

Since $1 \le J_k(n+1) \le n + 1$, the hypothesis says $j \in [1, k - 1]$, that is, $n + 1$ is a
low extremal point in the paper's sense, and none of the subtractions above is truncated.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Lemma 8. -/
theorem_wanted shift_le_iff_le_div (k n : ℕ) (hk : 2 ≤ k)
    (hj : MetaMathlibExt.josephus k (n + 1) ≤ k - 1) :
    (∀ m : ℕ, MetaMathlibExt.josephus k (n + 1) + k * m ≤ n + 1 + m ↔
      m ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1)) ∧
    (k - 2 + MetaMathlibExt.josephus k (n + 1) ≤ n →
      1 ≤ (n - (MetaMathlibExt.josephus k (n + 1) - 1)) / (k - 1))

/-- **Linear growth of the Josephus function after a high extremal point.** Let $k \ge 2$ and
$n_e \ge 2k - 3$ be natural numbers such that $n_e$ is a high extremal point of the Josephus
function $J_k$, that is, $1 \le J_k(n_e + 1) \le k - 1$, and write $j = J_k(n_e + 1)$. Then
$J_k(n_e + 1 + m) = j + km$ for every natural number
$m \le \lfloor (n_e - (j - 1)) / (k - 1) \rfloor$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 9. -/
theorem_wanted josephus_add_eq_of_high (k ne m : ℕ)
    (hk : 2 ≤ k) (hne : 2 * k - 3 ≤ ne)
    (hhigh : IsHighExtremal k ne)
    (hm : m ≤ (ne - (MetaMathlibExt.josephus k (ne + 1) - 1)) / (k - 1)) :
    MetaMathlibExt.josephus k (ne + 1 + m) =
      MetaMathlibExt.josephus k (ne + 1) + k * m

/-- **The Josephus function has infinitely many fixed points.** For every natural number
$k \ge 2$, the set of natural numbers $n$ with $J_k(n) = n$ is infinite, where $J_k$ is the
Josephus function.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras,
"Analytical Study and Efficient Evaluation of the
Josephus Function", Theorem 13. -/
theorem_wanted infinite_fixedPoints (k : ℕ) (hk : 2 ≤ k) :
    {n : ℕ | MetaMathlibExt.josephus k n = n}.Infinite

end MathlibExt.NumberTheory.JosephusWanted
