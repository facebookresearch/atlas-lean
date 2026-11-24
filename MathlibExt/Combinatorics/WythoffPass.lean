/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card

/-!
# Moves into the sets `B` and `C` of Wythoff's game with a pass

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

* `MetaMathlibExt.wythoffPassSetB_card_wythoffPassSetC_card`: `B` and `C` have nine elements each.
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
