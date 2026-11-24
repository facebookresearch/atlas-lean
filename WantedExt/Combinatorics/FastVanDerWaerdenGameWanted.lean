/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fast winning strategies in a generalized van der Waerden game

Statements from Hannah Alpert, Liam Barham, Brian Freidin, Ian Tan, and
Alexandra Weiner, "Fast Winning Strategies in a Generalized van der Waerden
Game", *INTEGERS* 26 (2026), Article A40 (arXiv:2309.11367).

Fix a finite `S ⊆ ℕ`. Maker and Breaker alternately claim unclaimed natural
numbers, Maker first; Maker wins once his numbers contain a homothetic copy
`aS + b` with `a ∈ ℕ \ {0}` and `b ∈ ℤ` (`ContainsCopy`). Maker has a
`p`-move strategy when he can force a win with at most `p` selections
(`MakerWinsWithin S p ∅ ∅`; the recursion checks the win condition before
each Maker move, and Breaker answers each Maker move with any unclaimed
number).

From Section 5 on, the paper also compares finite sets of rationals: `B` is a
copy (resp. reflection) of `A` if `B = aA + b` with `a > 0` (resp. `a < 0`).
A set `S = {s₁ < ⋯ < sₙ}` is symmetric of type `(i, j)` (`i < j`) if
`S \ {sᵢ}` is a copy of `S \ {sⱼ}`. Indices here are zero-based through
`Finset.orderEmbOfFin`, so the paper's types `(1, n)`, `(2, n)`, `(1, n - 1)`
are `(0, n - 1)`, `(1, n - 1)`, `(0, n - 2)`.

Theorems 1 (van der Waerden) and 2 (Hales–Jewett) of the paper are quoted
classical results already available as `MetaMathlibExt.vanDerWaerden` and
Mathlib's `Combinatorics.Line.exists_mono_in_high_dimension`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.HalesJewett
public import MathlibExt.Combinatorics.FastVanDerWaerdenGame

set_option autoImplicit false

namespace MetaMathlibExt

namespace FastVanDerWaerdenGame

@[expose] public section

open Finset

/-- **Maker wins the $S$-game in $|S|$ moves when $|S| \le 3$.** If $S$ is a finite set of
natural numbers with $|S| \le 3$, then, starting from the position where no number has been
claimed, Maker wins the $S$-game within $|S|$ moves.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Corollary 1 (`integers-2026-A40-cor-1`). -/
public theorem_wanted makerWinsWithin_card_of_card_le_three (S : Finset ℕ)
    (hS : S.card ≤ 3) :
    MakerWinsWithin S S.card ∅ ∅

/-- **A fast Maker win forces symmetry.** Let $S$ be a finite set of natural numbers with at
least two elements. If Maker, moving first with no numbers claimed, can force a win in the
game on $S$ within $|S|$ selections, then $S$, viewed as a set of rational numbers, is
symmetric.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 1
(`integers-2026-A40-lem-1`). -/
public theorem_wanted isSymmetric_of_makerWinsWithin_card (S : Finset ℕ)
    (hS : 2 ≤ S.card) (h : MakerWinsWithin S S.card ∅ ∅) :
    IsSymmetric (S.image fun s : ℕ => (s : ℚ))

/-- **Zero-geometric copies of symmetric sets.** Let $S = \{s_0 < s_1 < \dots < s_{n-1}\}$ be a
finite set of $n$ rational numbers, and let $i, j < n$ be such that $S$ is symmetric of type
$(i, j)$, with positions counted from $0$. If $i = 1$ and $j = n - 1$, then there is a rational
number $k > 1$ such that the zero-geometric set $S_2(n, k)$ is a copy of $S$. If $i = 0$ and
$j = n - 2$, then there is a rational number $k > 1$ such that $S_2(n, k)$ is a reflection of $S$.

In the paper's one-based numbering these are the types $(2, n)$ and $(1, n - 1)$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 4
(`integers-2026-A40-lem-4`). -/
public theorem_wanted zeroGeometricSet_of_isSymmetricOfType (S : Finset ℚ)
    (i j : Fin S.card) (h : IsSymmetricOfType S i j) :
    (i.val = 1 → j.val = S.card - 1 →
        ∃ k : ℚ, 1 < k ∧ IsRatCopy S (zeroGeometricSet S.card k)) ∧
      (i.val = 0 → j.val = S.card - 2 →
        ∃ k : ℚ, 1 < k ∧ IsRatReflection S (zeroGeometricSet S.card k))

/-- **Uniqueness of the symmetry type.** A finite set $S$ of rational numbers with at least
four elements is symmetric of at most one type: if $S$ is symmetric of types $(i, j)$ and
$(i', j')$, then $i = i'$ and $j = j'$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 5
(`integers-2026-A40-lem-5`). -/
public theorem_wanted isSymmetricOfType_unique (S : Finset ℚ) (hS : 4 ≤ S.card)
    (i j i' j' : Fin S.card) (h : IsSymmetricOfType S i j)
    (h' : IsSymmetricOfType S i' j') :
    i = i' ∧ j = j'

/-- **Hales–Jewett bound for the $S$-game.** Let $S$ be a finite set of natural numbers with
$|S| = n$, and let $N$ be a natural number such that every 2-coloring of $S^N$ has a
monochromatic combinatorial line. Then, starting from the position where no number has been
claimed, Maker wins the $S$-game within $\lceil n^N / 2 \rceil$ moves.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 4
(`integers-2026-A40-thm-4`). -/
public theorem_wanted makerWinsWithin_of_halesJewett (S : Finset ℕ) (N : ℕ)
    (hN : ∀ C : (Fin N → S) → Bool, ∃ l : Combinatorics.Line S (Fin N), l.IsMono C) :
    MakerWinsWithin S ((S.card ^ N + 1) / 2) ∅ ∅

/-- **Maker cannot win the $S$-game in $|S|$ moves when $|S| \ge 5$.** If $S$ is a finite
set of natural numbers with $|S| \ge 5$, then, starting from the position where no number has
been claimed, Maker does not win the $S$-game within $|S|$ moves.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 5
(`integers-2026-A40-thm-5`). -/
public theorem_wanted not_makerWinsWithin_card_of_five_le (S : Finset ℕ)
    (hS : 5 ≤ S.card) :
    ¬ MakerWinsWithin S S.card ∅ ∅

/-- **Four-element sets with a four-move win are the symmetric ones.** If $S$ is a set of four
natural numbers, then, starting from the position where no number has been claimed, Maker wins
the $S$-game within $4$ moves if and only if $S$, viewed as a set of rationals, is symmetric.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 6
(`integers-2026-A40-thm-6`). -/
public theorem_wanted makerWinsWithin_four_iff_isSymmetric (S : Finset ℕ)
    (hS : S.card = 4) :
    MakerWinsWithin S 4 ∅ ∅ ↔ IsSymmetric (S.image fun s : ℕ => (s : ℚ))

/-- **Maker wins the $S$-game in five moves when $|S| = 4$.** If $S$ is a set of four natural
numbers, then, starting from the position where no number has been claimed, Maker wins the
$S$-game within $5$ moves.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 7
(`integers-2026-A40-thm-7`). -/
public theorem_wanted makerWinsWithin_five_of_card_eq_four (S : Finset ℕ)
    (hS : S.card = 4) :
    MakerWinsWithin S 5 ∅ ∅

/-- **Tree criterion for fast wins.** Let $S$ be a finite set of natural numbers and $p$ a
natural number. Let $T$ be a finite rooted tree with root $r$ whose vertices are pairwise
distinct rationals, such that every path from $r$ down to a vertex has at most $p$ vertices and
some such path has exactly $p$ vertices (so $T$ has height $p - 1$). Suppose that for every leaf
$v$ the set of vertices on the path from $r$ to $v$ contains a copy $aS + b$ of $S$ with
rationals $a > 0$ and $b$, and that every vertex other than the root that is not a leaf has at
least two children. Then, starting from the position where no number has been claimed, Maker
wins the $S$-game within $p$ moves.

The tree is given by the finite set of its root-to-vertex paths, each recorded as the list of
rationals along it.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Proposition 1
(`integers-2026-A40-prop-1`). -/
public theorem_wanted makerWinsWithin_of_tree (S : Finset ℕ) (p : ℕ) (r : ℚ)
    (N : Finset (List ℚ)) (hroot : [r] ∈ N) (hstart : ∀ l ∈ N, [r] <+: l)
    (hprefix : ∀ l ∈ N, ∀ l', l' <+: l → l' ≠ [] → l' ∈ N)
    (hdistinct : ∀ l₁ ∈ N, ∀ l₂ ∈ N, l₁.getLast? = l₂.getLast? → l₁ = l₂)
    (hheight : (∀ l ∈ N, l.length ≤ p) ∧ ∃ l ∈ N, l.length = p)
    (hcopy : ∀ l ∈ N, (∀ x, l ++ [x] ∉ N) →
      ∃ C ⊆ l.toFinset, IsRatCopy (S.image fun s : ℕ => (s : ℚ)) C)
    (hdeg : ∀ l ∈ N, l ≠ [r] → (∃ x, l ++ [x] ∈ N) →
      2 ≤ (N.filter fun l' => l <+: l' ∧ l'.length = l.length + 1).card) :
    MakerWinsWithin S p ∅ ∅

end

end FastVanDerWaerdenGame

end MetaMathlibExt
