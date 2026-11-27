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
public import MathlibExt.GameTheory.ExactSlowNimCritical
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
