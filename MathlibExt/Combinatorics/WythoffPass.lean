/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Lattice.Nat

/-!
# Grundy numbers and moves in Wythoff's game with a pass

In Wythoff's game a position is a pair `(x, y)` of natural numbers, and a move from `(x, y)` goes
to `(u, y)` with `u < x` (a horizontal move), to `(x, v)` with `v < y` (a vertical move), or to
`(x - t, y - t)` with `1 ≤ t ≤ min(x, y)` (a diagonal move). Miyadera, Manabe and Fukui compare
Wythoff's game with a one-time pass and the sum of Wythoff's game and a pile of one stone. In the
source, the sets `B` (`MetaMathlibExt.wythoffPassSetB`) and `C` (`MetaMathlibExt.wythoffPassSetC`),
of nine positions each, are the P-positions `(x, y, 1)` with `x, y ≤ 8` of the game with a pass
and of the game plus one stone, respectively (its Lemma 1); here they are finite sets of pairs,
with the third coordinate dropped. The source uses the theorem below in the induction showing
that the two games have the same P-positions `(x, y, 1)` with `x ≥ 9` or `y ≥ 9` (its Theorem 4).

## Main statements

* `MetaMathlibExt.wythoffExtraMoveGrundy_eq` gives the mex recursion for the two variants.
  At the origin with the extra move unused, their Grundy numbers are respectively zero and one.
* `MetaMathlibExt.wythoffPassSetB_card_wythoffPassSetC_card`: `B` and `C` have nine elements each.
* `MetaMathlibExt.wythoffPass_moves_meet_setB_setC` characterizes the rows, columns and diagonals
  from which a move reaches each set outside the nine-by-nine corner.
* `MetaMathlibExt.wythoffPass_moves_meet_setB_iff_setC`: from a position `(x, y)` with `x ≥ 9` or
  `y ≥ 9`, some horizontal move lies in `B` if and only if some horizontal move lies in `C`, and
  likewise for the vertical moves and for the diagonal moves.

## Proof

Every pair in `B` or in `C` has both coordinates at most `8`, and its coordinates differ by at
most `4`. Each of the two sets has a pair in every row `y ≤ 8`, in every column `x ≤ 8` and on
every diagonal `y - x = d` with `-4 ≤ d ≤ 4`. So from a position `(x, y)` with `x ≥ 9` or `y ≥ 9`,
some horizontal move lies in the set exactly when `y ≤ 8`, some vertical move exactly when
`x ≤ 8`, and some diagonal move exactly when `x ≤ y + 4` and `y ≤ x + 4`; the conditions are the
same for `B` and for `C`. The source derives the theorem directly from its Lemma 2, which states
these conditions.

## References

* Ryohei Miyadera, Hikaru Manabe and Masanori Fukui, *Wythoff's Game with a Pass*,
  arXiv:1711.04960v2, Definition 7 (the moves), Definition 9 (the sets `B` and `C`), Lemmas 1-3
  and Theorem 4 (<https://arxiv.org/abs/1711.04960>). The declaration docstrings cite the journal
  version, INTEGERS 25 (2025), Article G4.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Grundy numbers of Wythoff's game with an extra move.** Positions are triples $(x, y, p)$
with $x, y \in \mathbb{N}$ and $p \in \{0, 1\}$. A move from $(x, y, p)$ goes to $(u, y, p)$ with
$u < x$, to $(x, v, p)$ with $v < y$, or to $(x - t, y - t, p)$ with $1 \le t \le \min(x, y)$
(the moves of a Queen in Wythoff's game), or, when $p = 1$, it is an extra move to $(x, y, 0)$.
There are two variants. In the strict variant the extra move is the one-time pass of Wythoff's
game with a pass and is not allowed at the terminal position, that is, it requires $x + y > 0$;
in the non-strict variant it is the move in an added pile of one stone and is always allowed
when $p = 1$. In each variant, the Grundy number of $(x, y, p)$ is the mex (least natural number
not attained) of the Grundy numbers of the positions reachable in one move. With $p = 0$ both
variants are classical Wythoff's game.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (the move sets `M₁, M₂, M₃, M₄, M₄'` and the
Grundy numbers `𝒢₁`, `𝒢₂`). -/
noncomputable def wythoffExtraMoveGrundy (strict : Bool) : ℕ → ℕ → Bool → ℕ
  | x, y, p =>
    sInf {m | (∀ u, u < x → wythoffExtraMoveGrundy strict u y p ≠ m) ∧
      (∀ v, v < y → wythoffExtraMoveGrundy strict x v p ≠ m) ∧
      (∀ t, 1 ≤ t → t ≤ x → t ≤ y → wythoffExtraMoveGrundy strict (x - t) (y - t) p ≠ m) ∧
      (p = true → (strict = false ∨ 0 < x + y) →
        wythoffExtraMoveGrundy strict x y false ≠ m)}
termination_by x y p => 2 * (x + y) + p.toNat
decreasing_by
  all_goals first
    | omega
    | (subst_vars; simp only [Bool.toNat_true, Bool.toNat_false]; omega)

/-- **Grundy numbers of Wythoff's game with a pass.** Wythoff's game with a pass has positions
$(x, y, p)$ with $x, y \in \mathbb{N}$ and $p \in \{0, 1\}$, where $p = 1$ means the one-time pass
is still available. A move goes from $(x, y, p)$ to $(u, y, p)$ with $u < x$, to $(x, v, p)$
with $v < y$, or to $(x - t, y - t, p)$ with $1 \le t \le \min(x, y)$, or, when $p = 1$ and
$x + y > 0$, it is the pass to $(x, y, 0)$. $\mathcal{G}_1(x, y, p)$ is the Grundy number of
$(x, y, p)$ in this game, that is, the strict variant of the Grundy numbers of Wythoff's game
with an extra move.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (Grundy numbers `𝒢₁`). -/
noncomputable abbrev wythoffPassGrundy (x y : ℕ) (p : Bool) : ℕ :=
  wythoffExtraMoveGrundy true x y p

/-- **Grundy numbers of Wythoff's game plus one stone.** For natural numbers $x, y$ and
$p \in \{0, 1\}$, $\mathcal{G}_2(x, y, p)$ is the Grundy number of the position $(x, y, p)$ in the
sum of Wythoff's game on $(x, y)$ and a pile of $p$ stones. That is, it is the Grundy function of
Wythoff's game with the extra move from $(x, y, 1)$ to $(x, y, 0)$ always available, including at
$(0, 0, 1)$.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (Grundy numbers `𝒢₂`). -/
noncomputable abbrev wythoffPlusStoneGrundy (x y : ℕ) (p : Bool) : ℕ :=
  wythoffExtraMoveGrundy false x y p

/-- **The set $A$.** $A$ is the finite set of pairs of natural numbers
$A = \{(0, 0), (1, 2), (2, 1), (3, 5), (4, 7), (5, 3), (7, 4)\}$. These are the positions
$(x, y, 0)$ of the set $A$ in the source, with the third coordinate dropped.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4 (the set `A`, Definition 12). -/
def wythoffPassSetA : Finset (ℕ × ℕ) :=
  {(0, 0), (1, 2), (2, 1), (3, 5), (4, 7), (5, 3), (7, 4)}

/-- **Mex recursion for the Grundy numbers of Wythoff's game with an extra move.** In both
variants (strict: the pass of Wythoff's game with a pass; non-strict: a pile of one stone), the
Grundy number of a position $(x, y, p)$ with $x, y \in \mathbb{N}$ and $p \in \{0, 1\}$ is the
least natural number $m$ that differs from the Grundy number of $(u, y, p)$ for every $u < x$,
from that of $(x, v, p)$ for every $v < y$, and from that of $(x - t, y - t, p)$ for every $t$
with $1 \le t \le x$ and $t \le y$, and that, when $p = 1$ and either the variant is non-strict
or $x + y > 0$, also differs from the Grundy number of $(x, y, 0)$.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 1 (Grundy numbers as mex over moves). -/
theorem wythoffExtraMoveGrundy_eq (strict : Bool) (x y : ℕ) (p : Bool) :
    wythoffExtraMoveGrundy strict x y p =
      sInf {m | (∀ u, u < x → wythoffExtraMoveGrundy strict u y p ≠ m) ∧
        (∀ v, v < y → wythoffExtraMoveGrundy strict x v p ≠ m) ∧
        (∀ t, 1 ≤ t → t ≤ x → t ≤ y →
          wythoffExtraMoveGrundy strict (x - t) (y - t) p ≠ m) ∧
        (p = true → (strict = false ∨ 0 < x + y) →
          wythoffExtraMoveGrundy strict x y false ≠ m)} := by
  rw [wythoffExtraMoveGrundy]

/-- **The terminal position of Wythoff's game with a pass.** Let $\mathcal{G}_1(x, y, p)$ be the
Grundy numbers of Wythoff's game with a pass, where $p = 1$ means the pass is still available.
Then $\mathcal{G}_1(0, 0, p) = 0$ for both $p = 0$ and $p = 1$: the terminal position $(0, 0)$
has Grundy number $0$ with or without the pass available, since the pass is not allowed from a
terminal position.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (`M₄(x, y, p) = ∅` if `x + y = 0`). -/
theorem wythoffPassGrundy_zero_zero (p : Bool) : wythoffPassGrundy 0 0 p = 0 := by
  rw [wythoffPassGrundy, wythoffExtraMoveGrundy_eq]
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  refine ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun v hv => absurd hv (Nat.not_lt_zero v),
    fun t h1 h2 _ => by omega, fun _ h => by simp at h⟩

/-- **Wythoff's game plus one stone at $(0, 0, 1)$.** In the sum of Wythoff's game and a pile of
one stone, the position $(0, 0, 1)$ (no Wythoff moves left, the stone present) has Grundy number
$\mathcal{G}_2(0, 0, 1) = 1$: its only move is to the terminal position $(0, 0, 0)$.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 3 (`M₄'(x, y, 1) = {(x, y, 0)}`). -/
theorem wythoffPlusStoneGrundy_zero_zero_true : wythoffPlusStoneGrundy 0 0 true = 1 := by
  have h0 : wythoffPlusStoneGrundy 0 0 false = 0 := by
    rw [wythoffPlusStoneGrundy, wythoffExtraMoveGrundy_eq]
    refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
    refine ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun v hv => absurd hv (Nat.not_lt_zero v),
      fun t h1 h2 _ => by omega, fun h => by simp at h⟩
  rw [wythoffPlusStoneGrundy] at h0 ⊢
  rw [wythoffExtraMoveGrundy_eq]
  have h1 : (1 : ℕ) ∈ {m | (∀ u, u < 0 → wythoffExtraMoveGrundy false u 0 true ≠ m) ∧
      (∀ v, v < 0 → wythoffExtraMoveGrundy false 0 v true ≠ m) ∧
      (∀ t, 1 ≤ t → t ≤ 0 → t ≤ 0 →
        wythoffExtraMoveGrundy false (0 - t) (0 - t) true ≠ m) ∧
      (true = true → (false = false ∨ 0 < 0 + 0) →
        wythoffExtraMoveGrundy false 0 0 false ≠ m)} :=
    ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun v hv => absurd hv (Nat.not_lt_zero v),
      fun t h1 h2 _ => by omega, fun _ _ => by rw [h0]; omega⟩
  apply le_antisymm (Nat.sInf_le h1)
  refine le_csInf ⟨1, h1⟩ fun m hm => ?_
  have := hm.2.2.2 rfl (Or.inl rfl)
  rw [h0] at this
  omega

/-- **The set $A$ has seven elements.** The set
$A = \{(0, 0), (1, 2), (2, 1), (3, 5), (4, 7), (5, 3), (7, 4)\}$ of pairs of natural numbers has
exactly $7$ elements.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4. -/
theorem wythoffPassSetA_card : wythoffPassSetA.card = 7 := by
  decide

/-- **The set $B$.** $B$ is the finite set of pairs of natural numbers
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$. These are the
positions $(x, y, 1)$ of the set $B$ in the source, with the third coordinate dropped.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4 (the set `B`). -/
def wythoffPassSetB : Finset (ℕ × ℕ) :=
  {(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)}

/-- **The set $C$.** $C$ is the finite set of pairs of natural numbers
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$. These are the
positions $(x, y, 1)$ of the set $C$ in the source, with the third coordinate dropped.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4 (the set `C`). -/
def wythoffPassSetC : Finset (ℕ × ℕ) :=
  {(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)}

/-- **The sets $B$ and $C$ have nine elements each.** The sets
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$ and
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$ of pairs of
natural numbers each have exactly $9$ elements.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4. -/
theorem wythoffPassSetB_card_wythoffPassSetC_card :
    wythoffPassSetB.card = 9 ∧ wythoffPassSetC.card = 9 := by
  decide

/-- Let `S` be a finite set of pairs of natural numbers whose coordinates are at most `8` and
differ by at most `4`, with a pair in every row `b ≤ 8`, in every column `a ≤ 8` and on every
diagonal `b + 4 = a + d` with `d ≤ 8`. Then, from a position `(x, y)` with `x ≥ 9` or `y ≥ 9`, some
horizontal move lies in `S` if and only if `y ≤ 8`, some vertical move if and only if `x ≤ 8`, and
some diagonal move if and only if `x ≤ y + 4` and `y ≤ x + 4`. -/
private theorem WythoffPass.moves_meet_iff (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 ≤ 8 ∧ p.2 ≤ 8 ∧ p.1 ≤ p.2 + 4 ∧ p.2 ≤ p.1 + 4)
    (hrow : ∀ b < 9, ∃ a < 9, (a, b) ∈ S) (hcol : ∀ a < 9, ∃ b < 9, (a, b) ∈ S)
    (hdiag : ∀ d < 9, ∃ p ∈ S, p.2 + 4 = p.1 + d) {x y : ℕ} (hxy : 9 ≤ x ∨ 9 ≤ y) :
    ((∃ u < x, (u, y) ∈ S) ↔ y ≤ 8) ∧ ((∃ v < y, (x, v) ∈ S) ↔ x ≤ 8) ∧
      ((∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ S) ↔ x ≤ y + 4 ∧ y ≤ x + 4) := by
  refine ⟨⟨fun ⟨_, _, h⟩ => (hS _ h).2.1, fun hy => ?_⟩,
    ⟨fun ⟨_, _, h⟩ => (hS _ h).1, fun hx => ?_⟩, ⟨fun ⟨t, _, _, _, h⟩ => ?_, fun h => ?_⟩⟩
  · -- A horizontal move: the pair of `S` in row `y` has first coordinate `a < 9 ≤ x`.
    obtain ⟨a, ha, h⟩ := hrow y (by omega)
    exact ⟨a, by omega, h⟩
  · -- A vertical move: the pair of `S` in column `x` has second coordinate `b < 9 ≤ y`.
    obtain ⟨b, hb, h⟩ := hcol x (by omega)
    exact ⟨b, by omega, h⟩
  · -- A diagonal move keeps the difference of the coordinates, which is at most `4` on `S`.
    have := hS _ h
    dsimp only at this
    omega
  · -- A diagonal move: take the pair `(a, b)` of `S` with `b - a = y - x`, and `t = x - a`.
    obtain ⟨⟨a, b⟩, hp, hab⟩ := hdiag (y + 4 - x) (by omega)
    have := hS _ hp
    dsimp only at this hab
    refine ⟨x - a, by omega, by omega, by omega, ?_⟩
    rwa [show x - (x - a) = a by omega, show y - (x - a) = b by omega]

/-- **Moves into the sets $B$ and $C$ away from the corner.** Let
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$ and
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$. For natural
numbers $x, y$, call the pairs $(u, y)$ with $u < x$ the horizontal moves from $(x, y)$, the
pairs $(x, v)$ with $v < y$ its vertical moves, and the pairs $(x - t, y - t)$ with
$1 \le t \le \min(x, y)$ its diagonal moves. Suppose that $x \ge 9$ or $y \ge 9$. Then (i) if
$y \le 8$, some horizontal move lies in $B$ and some horizontal move lies in $C$, while no
vertical move lies in $B$ or in $C$; (ii) if $x \le 8$, some vertical move lies in $B$ and some
vertical move lies in $C$, while no horizontal move lies in $B$ or in $C$; (iii) if
$x \le y + 4$ and $y \le x + 4$, some diagonal move lies in $B$ and some diagonal move lies in
$C$; (iv) if $x \ge y + 5$ or $y \ge x + 5$, no diagonal move lies in $B$ or in $C$.

In the source these are the moves from the position $(x, y, 1)$ of Wythoff's game with a pass,
with the third coordinate dropped.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Lemma 2 (`integers-2025-G4-lem-2`). -/
theorem wythoffPass_moves_meet_setB_setC (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    (y ≤ 8 →
      (∃ u < x, (u, y) ∈ wythoffPassSetB) ∧ (∃ u < x, (u, y) ∈ wythoffPassSetC) ∧
        (∀ v < y, (x, v) ∉ wythoffPassSetC) ∧ (∀ v < y, (x, v) ∉ wythoffPassSetB)) ∧
    (x ≤ 8 →
      (∃ v < y, (x, v) ∈ wythoffPassSetB) ∧ (∃ v < y, (x, v) ∈ wythoffPassSetC) ∧
        (∀ u < x, (u, y) ∉ wythoffPassSetC) ∧ (∀ u < x, (u, y) ∉ wythoffPassSetB)) ∧
    (x ≤ y + 4 → y ≤ x + 4 →
      (∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetB) ∧
        (∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetC)) ∧
    (y + 5 ≤ x ∨ x + 5 ≤ y →
      (∀ t, 1 ≤ t → t ≤ x → t ≤ y → (x - t, y - t) ∉ wythoffPassSetB) ∧
        (∀ t, 1 ≤ t → t ≤ x → t ≤ y → (x - t, y - t) ∉ wythoffPassSetC)) := by
  obtain ⟨rowB, colB, diagB⟩ :=
    WythoffPass.moves_meet_iff wythoffPassSetB (by decide) (by decide) (by decide) (by decide) hxy
  obtain ⟨rowC, colC, diagC⟩ :=
    WythoffPass.moves_meet_iff wythoffPassSetC (by decide) (by decide) (by decide) (by decide) hxy
  simp only [← not_and, ← not_exists, rowB, rowC, colB, colC, diagB, diagC]
  grind only

/-- **Moves from a large position meet $B$ exactly when they meet $C$.** Let
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$ and
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$. Let $x, y$ be
natural numbers with $x \ge 9$ or $y \ge 9$. Then some pair $(u, y)$ with $u < x$ lies in $B$ if
and only if some such pair lies in $C$; some pair $(x, v)$ with $v < y$ lies in $B$ if and only
if some such pair lies in $C$; and some pair $(x - t, y - t)$ with $1 \le t \le \min(x, y)$ lies
in $B$ if and only if some such pair lies in $C$.

In the source these pairs are the horizontal, vertical and diagonal moves from the position
$(x, y, 1)$ of Wythoff's game with a pass, with the third coordinate dropped.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Lemma 3 (`integers-2025-G4-lem-3`). -/
theorem wythoffPass_moves_meet_setB_iff_setC (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    ((∃ u < x, (u, y) ∈ wythoffPassSetB) ↔ ∃ u < x, (u, y) ∈ wythoffPassSetC) ∧
    ((∃ v < y, (x, v) ∈ wythoffPassSetB) ↔ ∃ v < y, (x, v) ∈ wythoffPassSetC) ∧
    ((∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetB) ↔
      ∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetC) := by
  obtain ⟨hB₁, hB₂, hB₃⟩ :=
    WythoffPass.moves_meet_iff wythoffPassSetB (by decide) (by decide) (by decide) (by decide) hxy
  obtain ⟨hC₁, hC₂, hC₃⟩ :=
    WythoffPass.moves_meet_iff wythoffPassSetC (by decide) (by decide) (by decide) (by decide) hxy
  exact ⟨hB₁.trans hC₁.symm, hB₂.trans hC₂.symm, hB₃.trans hC₃.symm⟩

end

end MetaMathlibExt
