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
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.Ring.Rat

set_option autoImplicit false

namespace MetaMathlibExt

namespace FastVanDerWaerdenGame

@[expose] public section

open Finset

/-- **Containing a homothetic copy.** Let $S$ and $M$ be finite sets of natural numbers. $M$
contains a homothetic copy of $S$ if there are a natural number $a > 0$ and an integer $b$ such
that $as + b \in M$ for every $s \in S$, that is, $aS + b \subseteq M$. This is Maker's winning
condition.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
def ContainsCopy (S M : Finset ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ ∃ b : ℤ, ∀ s ∈ S, ∃ m ∈ M, (m : ℤ) = a * s + b

/-- **Maker wins within $p$ moves.** Let $S$ be a finite set of natural numbers. In the
$S$-game, Maker and Breaker alternately claim unclaimed natural numbers, and Maker wins once the
numbers Maker has claimed contain a copy $aS + b = \{as + b : s \in S\}$ of $S$, where $a$ is a
positive integer and $b$ is an integer. Let $M$ and $B$ be finite sets of natural numbers
(claimed by Maker and by Breaker) and $p$ a natural number, with Maker to move. Maker wins
within $p$ moves if $M$ already contains such a copy of $S$, or if $p \ge 1$ and there is a
number $x \notin M \cup B$ such that for every number $y \ne x$ with $y \notin M \cup B$, Maker
wins within $p - 1$ moves from the position where Maker has claimed $M \cup \{x\}$ and Breaker
has claimed $B \cup \{y\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Sections 1
and 5 (`p`-move strategy). -/
def MakerWinsWithin (S : Finset ℕ) : ℕ → Finset ℕ → Finset ℕ → Prop
  | 0, M, _ => ContainsCopy S M
  | p + 1, M, B => ContainsCopy S M ∨
      ∃ x : ℕ, x ∉ M ∧ x ∉ B ∧
        ∀ y : ℕ, y ≠ x → y ∉ M → y ∉ B → MakerWinsWithin S p (insert x M) (insert y B)

/-- **Copies of finite sets of rationals.** Let $A$ and $B$ be finite sets of rational numbers.
$B$ is a copy of $A$ if there are rationals $a > 0$ and $b$ such that
$B = aA + b = \{ax + b : x \in A\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
def IsRatCopy (A B : Finset ℚ) : Prop :=
  ∃ a b : ℚ, 0 < a ∧ B = A.image fun x => a * x + b

/-- **Reflections of finite sets of rationals.** Let $A$ and $B$ be finite sets of rational
numbers. $B$ is a reflection of $A$ if there are rationals $a < 0$ and $b$ such that
$B = aA + b = \{ax + b : x \in A\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 6. -/
def IsRatReflection (A B : Finset ℚ) : Prop :=
  ∃ a b : ℚ, a < 0 ∧ B = A.image fun x => a * x + b

/-- **Symmetric sets of a given type.** Let $S = \{s_0 < s_1 < \dots < s_{n-1}\}$ be a finite
set of $n$ rational numbers and let $i, j < n$. Then $S$ is called symmetric of type $(i, j)$ if
$i < j$ and $S \setminus \{s_i\}$ is a copy of $S \setminus \{s_j\}$.

Positions are counted from $0$, so the paper's type $(i + 1, j + 1)$ is the type $(i, j)$ here.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetricOfType (S : Finset ℚ) (i j : Fin S.card) : Prop :=
  i < j ∧ IsRatCopy (S.erase (S.orderEmbOfFin rfl j)) (S.erase (S.orderEmbOfFin rfl i))

/-- **Symmetric sets of rationals.** A finite set $S$ of rational numbers is symmetric if it is
symmetric of some type $(i, j)$ with $i, j < |S|$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetric (S : Finset ℚ) : Prop :=
  ∃ i j : Fin S.card, IsSymmetricOfType S i j

/-- **The zero-geometric set $S_2(n, k)$.** For a natural number $n$ and a rational number $k$,
$S_2(n, k)$ is the finite set of rationals $\{0\} \cup \{k^i : 0 \le i < n - 1\}$, that is,
$\{0, 1, k, \dots, k^{n-2}\}$ when $n \ge 2$ and $\{0\}$ when $n \le 1$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
def zeroGeometricSet (n : ℕ) (k : ℚ) : Finset ℚ :=
  insert 0 ((range (n - 1)).image fun i => k ^ i)

/-- **Every finite set contains a copy of the empty set.** Every finite set $M$ of natural
numbers contains a homothetic copy of the empty set.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
theorem containsCopy_empty (M : Finset ℕ) : ContainsCopy ∅ M :=
  ⟨1, Nat.one_pos, 0, by simp⟩

/-- **Winning within zero moves.** Let $S$ be a finite set of natural numbers, and let $M$ and
$B$ be finite sets of natural numbers. Maker wins the $S$-game within $0$ moves from the position
where Maker has claimed $M$ and Breaker has claimed $B$ if and only if $M$ contains a copy
$aS + b = \{as + b : s \in S\}$ of $S$, where $a$ is a positive integer and $b$ is an integer.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
theorem makerWinsWithin_zero (S M B : Finset ℕ) :
    MakerWinsWithin S 0 M B ↔ ContainsCopy S M := Iff.rfl

/-- **Every finite set of rationals is a copy of itself.** For every finite set $A$ of rational
numbers, $A$ is a copy of $A$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
theorem isRatCopy_refl (A : Finset ℚ) : IsRatCopy A A :=
  ⟨1, 0, one_pos, by simp⟩

/-- **The zero-geometric set $S_2(1, k)$ is $\{0\}$.** For every rational number $k$, the
zero-geometric set $S_2(1, k)$ equals $\{0\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
theorem zeroGeometricSet_one (k : ℚ) : zeroGeometricSet 1 k = {0} := by
  simp [zeroGeometricSet]

/-- **The zero-geometric set $S_2(n + 2, k)$.** For every natural number $n$ and every rational
$k$, $S_2(n + 2, k) = \{0\} \cup \{k^i : 0 \le i \le n\} = \{0, 1, k, \dots, k^n\}$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
theorem zeroGeometricSet_add_two (n : ℕ) (k : ℚ) :
    zeroGeometricSet (n + 2) k = insert 0 ((range (n + 1)).image fun i => k ^ i) := rfl

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

/-- **Possible types of a symmetric set.** Let $S$ be a finite set of rational numbers with
$n \ge 4$ elements. If $S$ is symmetric of type $(i, j)$, with positions counted from $0$, then
$(i, j)$ is $(0, n - 1)$, $(1, n - 1)$ or $(0, n - 2)$. In the paper's one-based numbering these
are the types $(1, n)$, $(2, n)$ and $(1, n - 1)$.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 2
(`integers-2026-A40-lem-2`). -/
public theorem_wanted isSymmetricOfType_cases (S : Finset ℚ) (hS : 4 ≤ S.card)
    (i j : Fin S.card) (h : IsSymmetricOfType S i j) :
    (i.val = 0 ∧ j.val = S.card - 1) ∨ (i.val = 1 ∧ j.val = S.card - 1) ∨
      (i.val = 0 ∧ j.val = S.card - 2)

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
