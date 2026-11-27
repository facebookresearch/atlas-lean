/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.GameTheory.ExactSlowNimRemoteness
public import MathlibExt.GameTheory.ExactSlowNimA0Moves
public import WantedExt.Combinatorics.SlowANimWanted

/-!
# Remoteness of Exact Slow `k`-NIM with `k + 1` piles

Statements from Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
*On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1
(arXiv:2304.06498).

`NIM(k + 1, k)` is played on `k + 1` piles (a position is `x : Fin (k + 1) → ℕ`); a move removes
exactly one stone from each of `k` nonempty piles. This is the existing Slow`A`-Nim game
`slowANimGame (k + 1) {k}`, whose options are `slowANimMoves {k} x`. Smith's remoteness function
is `SpragueGrundy.smithRemoteness` (`MathlibExt/GameTheory/SmithRemoteness.lean`). The paper
compares positions after sorting their entries; since the game, the remoteness, and the
conditions below are invariant under permuting piles, "`R(y) ≠ m` for
every `y < x`" is equivalent to the same condition for the componentwise (`Pi`) order used here.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$m$-critical positions of exact slow $k$-NIM with $k + 1$ piles (Theorem 1).** Let $k \ge 1$
and $m$ be natural numbers, and let $x = (x_0, \dots, x_k)$ be a position of
$\mathrm{NIM}(k + 1, k)$, the game on $k + 1$ piles in which a move removes one stone from each
of exactly $k$ nonempty piles. Call $x$ $m$-critical when its Smith remoteness is $m$ and no
position $y < x$ (that is, $y_i \le x_i$ for every $i$ and $y \ne x$) has remoteness $m$. Then
$x$ is $m$-critical if and only if either
(A) $x_0 + \dots + x_k = km$, $x_i \le m$ for every $i$, every $x_i$ is even if $m$ is even,
and exactly one $x_i$ is even if $m$ is odd; or
(B) $x_0 + \dots + x_k = km + k - 1$, $x_i < m$ for every $i$, $m$ is even, and every $x_i$ is
odd.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public theorem_wanted isExactSlowNimCritical_iff {k : ℕ} (hk : 0 < k) (m : ℕ)
    (x : Fin (k + 1) → ℕ) :
    IsExactSlowNimCritical k m x ↔
      (∑ i, x i = k * m ∧ (∀ i, x i ≤ m) ∧ (Even m → ∀ i, Even (x i)) ∧
          (Odd m → ∃! i, Even (x i))) ∨
        (∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m ∧ ∀ i, Odd (x i))

/-- **Unique critical-lowering move for odd parameter (Corollary 1 (ii)).** Let $k \ge 2$, let
$m$ be odd, and let $x \in \mathbb{N}^{k+1}$ be an $m$-critical position of Slow$\{k\}$-Nim on
$k + 1$ stacks. Then $x$ has exactly one even entry $x_i$. The position $x'$ obtained from $x$ by
removing one token from every pile other than $i$ is an option of $x$, it is the only option of
$x$ that is $(m - 1)$-critical, and it is the position reached from $x$ by the M-move.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Corollary 1 (ii). -/
public theorem_wanted exactSlowNim_critical_of_odd {k m : ℕ} (hk : 2 ≤ k) (hm : Odd m)
    (x : Fin (k + 1) → ℕ) (hx : IsExactSlowNimCritical k m x) :
    ∃ i, Even (x i) ∧ (∀ j, Even (x j) → j = i) ∧
      slowANimAfter x (Finset.univ.erase i) ∈ slowANimMoves {k} x ∧
      (∀ y ∈ slowANimMoves {k} x,
        IsExactSlowNimCritical k (m - 1) y ↔ y = slowANimAfter x (Finset.univ.erase i)) ∧
      exactSlowNimMRuleMove x = slowANimAfter x (Finset.univ.erase i)

/-- **Proposition 1 (odd P-positions of exact slow k-NIM).** Let $0 < k$ and let
$\mathrm{NIM}(k + 1, k)$ be Slow$A$-Nim on $k + 1$ stacks with $A = \{k\}$. A position
$x = (x_0, \dots, x_k)$ of $\mathrm{NIM}(k + 1, k)$ all of whose entries are odd is a P-position if
and only if there is a natural number $m$ such that $x_0 + \dots + x_k = km + k - 1$, $x_i < m$
for every $i$, and $m$ is even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Proposition 1. -/
public theorem_wanted exactSlowNim_odd_isP_iff {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ)
    (hx : ∀ i, Odd (x i)) :
    SpragueGrundy.IsP (slowANimGame (k + 1) {k}) x ↔
      ∃ m, ∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m

/-- **Theorem 2 (the M-rule realizes Smith's remoteness).** Let $0 < k$ and let
$\mathrm{NIM}(k + 1, k)$ be exact slow $k$-NIM on $k + 1$ piles, that is, Slow$A$-Nim on $k + 1$
stacks with $A = \{k\}$, where a move removes one stone from each of exactly $k$ nonempty piles.
For every position $x$ of $\mathrm{NIM}(k + 1, k)$, the M-rule length $M(x)$ equals Smith's
remoteness $R(x)$ of $x$ in $\mathrm{NIM}(k + 1, k)$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 2. -/
public theorem_wanted exactSlowNimMRuleLength_eq_smithRemoteness {k : ℕ} (hk : 0 < k)
    (x : Fin (k + 1) → ℕ) :
    exactSlowNimMRuleLength k x = SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x

/-- **Theorem 3 (Smith's remoteness of exact slow k-NIM is polynomial-time computable).** The map
sending a list $(x_0, \dots, x_{n-1})$ of natural numbers of length $n$ to Smith's remoteness of
the position $(x_0, \dots, x_{n-1})$ of Slow$A$-Nim on $n$ stacks with $A = \{n - 1\}$ (where
$0 - 1 = 0$) is polynomial-time computable. Here natural numbers, in the input and the output,
are encoded in binary, and a list is encoded as the concatenation of the self-delimiting forms
of the encodings of its entries. For $n = k + 1$ this is the game $\mathrm{NIM}(k + 1, k)$, so $k$
is part of the input.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 3. -/
public theorem_wanted exactSlowNimRemoteness_isPolyTime :
    letI : BitstringEncoding ℕ := exactSlowNimBinaryNatEncoding
    ComplexityTheory.IsPolyTime exactSlowNimRemotenessOfList

end

end MetaMathlibExt
