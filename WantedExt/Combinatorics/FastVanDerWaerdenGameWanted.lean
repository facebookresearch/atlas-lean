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

/-- The finite set `M` of naturals contains a homothetic copy `aS + b` of `S`
with `a ∈ ℕ \ {0}` and `b ∈ ℤ` (Maker's winning condition).

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
def ContainsCopy (S M : Finset ℕ) : Prop :=
  ∃ a : ℕ, 0 < a ∧ ∃ b : ℤ, ∀ s ∈ S, ∃ m ∈ M, (m : ℤ) = a * s + b

/-- Maker, to move with claimed set `M` against Breaker's claimed set `B`, can
force a win with at most `p` further selections.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Sections 1
and 5 (`p`-move strategy). -/
def MakerWinsWithin (S : Finset ℕ) : ℕ → Finset ℕ → Finset ℕ → Prop
  | 0, M, _ => ContainsCopy S M
  | p + 1, M, B => ContainsCopy S M ∨
      ∃ x : ℕ, x ∉ M ∧ x ∉ B ∧
        ∀ y : ℕ, y ≠ x → y ∉ M → y ∉ B → MakerWinsWithin S p (insert x M) (insert y B)

/-- `B` is a copy of `A`: `B = aA + b` for rationals `a > 0` and `b`.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
def IsRatCopy (A B : Finset ℚ) : Prop :=
  ∃ a b : ℚ, 0 < a ∧ B = A.image fun x => a * x + b

/-- `B` is a reflection of `A`: `B = aA + b` for rationals `a < 0` and `b`.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 6. -/
def IsRatReflection (A B : Finset ℚ) : Prop :=
  ∃ a b : ℚ, a < 0 ∧ B = A.image fun x => a * x + b

/-- `S` is symmetric of (zero-based) type `(i, j)`: `i < j` and removing the
`i`-th smallest element gives a copy of removing the `j`-th smallest.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetricOfType (S : Finset ℚ) (i j : Fin S.card) : Prop :=
  i < j ∧ IsRatCopy (S.erase (S.orderEmbOfFin rfl j)) (S.erase (S.orderEmbOfFin rfl i))

/-- `S` is symmetric: it is symmetric of some type.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 2. -/
def IsSymmetric (S : Finset ℚ) : Prop :=
  ∃ i j : Fin S.card, IsSymmetricOfType S i j

/-- The paper's `S₂(n, k) = {0, 1, k, …, k^{n-2}}` (`{0}` for `n = 1`).

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
def zeroGeometricSet (n : ℕ) (k : ℚ) : Finset ℚ :=
  insert 0 ((range (n - 1)).image fun i => k ^ i)

/-- The empty set is contained in every claimed set.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 1. -/
theorem containsCopy_empty (M : Finset ℕ) : ContainsCopy ∅ M :=
  ⟨1, Nat.one_pos, 0, by simp⟩

/-- With no moves left Maker has won exactly when he already holds a copy.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
theorem makerWinsWithin_zero (S M B : Finset ℕ) :
    MakerWinsWithin S 0 M B ↔ ContainsCopy S M := Iff.rfl

/-- Every finite set of rationals is a copy of itself.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Section 5. -/
theorem isRatCopy_refl (A : Finset ℚ) : IsRatCopy A A :=
  ⟨1, 0, one_pos, by simp⟩

/-- `S₂(1, k) = {0}`.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
theorem zeroGeometricSet_one (k : ℚ) : zeroGeometricSet 1 k = {0} := by
  simp [zeroGeometricSet]

/-- `S₂(n + 2, k) = {0, 1, k, …, k^n}`.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Definition 3. -/
theorem zeroGeometricSet_add_two (n : ℕ) (k : ℚ) :
    zeroGeometricSet (n + 2) k = insert 0 ((range (n + 1)).image fun i => k ^ i) := rfl

/-- If `|S| ≤ 3`, Maker has an `|S|`-move strategy.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40,
Corollary 1 (`integers-2026-A40-cor-1`). -/
public theorem_wanted makerWinsWithin_card_of_card_le_three (S : Finset ℕ)
    (hS : S.card ≤ 3) :
    MakerWinsWithin S S.card ∅ ∅

/-- For `|S| ≥ 2`, if Maker has an `|S|`-move strategy then `S` is symmetric.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 1
(`integers-2026-A40-lem-1`). -/
public theorem_wanted isSymmetric_of_makerWinsWithin_card (S : Finset ℕ)
    (hS : 2 ≤ S.card) (h : MakerWinsWithin S S.card ∅ ∅) :
    IsSymmetric (S.image fun s : ℕ => (s : ℚ))

/-- A symmetric set of size `n ≥ 4` has (one-based) type `(1, n)`, `(2, n)` or
`(1, n - 1)`.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 2
(`integers-2026-A40-lem-2`). -/
public theorem_wanted isSymmetricOfType_cases (S : Finset ℚ) (hS : 4 ≤ S.card)
    (i j : Fin S.card) (h : IsSymmetricOfType S i j) :
    (i.val = 0 ∧ j.val = S.card - 1) ∨ (i.val = 1 ∧ j.val = S.card - 1) ∨
      (i.val = 0 ∧ j.val = S.card - 2)

/-- If `S` is symmetric of (one-based) type `(2, n)` (resp. `(1, n - 1)`), then
`S₂(n, k)` is a copy (resp. reflection) of `S` for some rational `k > 1`.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 4
(`integers-2026-A40-lem-4`). -/
public theorem_wanted zeroGeometricSet_of_isSymmetricOfType (S : Finset ℚ)
    (i j : Fin S.card) (h : IsSymmetricOfType S i j) :
    (i.val = 1 → j.val = S.card - 1 →
        ∃ k : ℚ, 1 < k ∧ IsRatCopy S (zeroGeometricSet S.card k)) ∧
      (i.val = 0 → j.val = S.card - 2 →
        ∃ k : ℚ, 1 < k ∧ IsRatReflection S (zeroGeometricSet S.card k))

/-- A set of size `n ≥ 4` is symmetric of at most one type.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Lemma 5
(`integers-2026-A40-lem-5`). -/
public theorem_wanted isSymmetricOfType_unique (S : Finset ℚ) (hS : 4 ≤ S.card)
    (i j i' j' : Fin S.card) (h : IsSymmetricOfType S i j)
    (h' : IsSymmetricOfType S i' j') :
    i = i' ∧ j = j'

/-- For `|S| = n`, if `N` is a Hales–Jewett dimension for two colors and
alphabet `S` (every 2-coloring of `S^N` has a monochromatic line), Maker wins
within `⌈n^N / 2⌉` moves.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 4
(`integers-2026-A40-thm-4`). -/
public theorem_wanted makerWinsWithin_of_halesJewett (S : Finset ℕ) (N : ℕ)
    (hN : ∀ C : (Fin N → S) → Bool, ∃ l : Combinatorics.Line S (Fin N), l.IsMono C) :
    MakerWinsWithin S ((S.card ^ N + 1) / 2) ∅ ∅

/-- If `|S| ≥ 5`, Maker does not have an `|S|`-move strategy.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 5
(`integers-2026-A40-thm-5`). -/
public theorem_wanted not_makerWinsWithin_card_of_five_le (S : Finset ℕ)
    (hS : 5 ≤ S.card) :
    ¬ MakerWinsWithin S S.card ∅ ∅

/-- For `|S| = 4`, Maker has a 4-move strategy if and only if `S` is
symmetric.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 6
(`integers-2026-A40-thm-6`). -/
public theorem_wanted makerWinsWithin_four_iff_isSymmetric (S : Finset ℕ)
    (hS : S.card = 4) :
    MakerWinsWithin S 4 ∅ ∅ ↔ IsSymmetric (S.image fun s : ℕ => (s : ℚ))

/-- For `|S| = 4`, Maker always has a 5-move strategy.

Source: Alpert, Barham, Freidin, Tan, and Weiner, *Fast Winning Strategies in a
Generalized van der Waerden Game*, INTEGERS 26 (2026), Article A40, Theorem 7
(`integers-2026-A40-thm-7`). -/
public theorem_wanted makerWinsWithin_five_of_card_eq_four (S : Finset ℕ)
    (hS : S.card = 4) :
    MakerWinsWithin S 5 ∅ ∅

/-- Tree criterion for fast wins: suppose a directed tree `T` of height `p - 1` has distinct
rational vertices, every maximal directed path's set of rationals contains a copy of `S`, and
every vertex that is neither a leaf nor the root has outdegree at least `2`. Then Maker has a
`p`-move strategy. The tree is given by its nodes `N`, each node recorded as the list of
rationals on the directed path from the root `r` to it: `N` contains `[r]`, every node starts
with `[r]`, nonempty prefixes of nodes are nodes, and nodes with the same last vertex are equal
(distinct vertices); the children of `l` are the nodes `l ++ [x]` (counted as the nodes
with prefix `l` and one more entry), leaves are nodes without
children, height `p - 1` means every node has length `≤ p` and some has length `p`, and the
maximal directed paths are the leaf nodes. A copy is `IsRatCopy` of `S` (cast to `ℚ`).

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
