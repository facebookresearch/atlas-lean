/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.GoldenRatio

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

/-- **The sets $B$ and $C$ have nine elements each.** The sets
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$ and
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$ of pairs of
natural numbers each have exactly $9$ elements.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4. -/
theorem wythoffPassSetB_card_wythoffPassSetC_card :
    wythoffPassSetB.card = 9 ∧ wythoffPassSetC.card = 9 := by
  decide

/-- **The set $A$ has seven elements.** The set
$A = \{(0, 0), (1, 2), (2, 1), (3, 5), (4, 7), (5, 3), (7, 4)\}$ of pairs of natural numbers has
exactly $7$ elements.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Section 4. -/
theorem wythoffPassSetA_card : wythoffPassSetA.card = 7 := by
  decide

/-- **Wythoff's theorem.** Let $\mathcal{G}_1(x, y, 0)$ be the Grundy number of the position
$(x, y, 0)$ of Wythoff's game with a pass, in which the pass has been used; this is the Grundy
number of $(x, y)$ in classical Wythoff's game. Then $\mathcal{G}_1(x, y, 0) = 0$ (that is,
$(x, y)$ is a P-position) if and only if there is $n \in \mathbb{N}$ with
$(x, y) = (\lfloor n\varphi \rfloor, \lfloor n\varphi \rfloor + n)$ or
$(x, y) = (\lfloor n\varphi \rfloor + n, \lfloor n\varphi \rfloor)$, where
$\varphi = (1 + \sqrt{5})/2$ is the golden ratio.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Theorem 2 (`integers-2025-G4-thm-2`), quoting Wythoff. -/
public theorem_wanted wythoffGrundy_eq_zero_iff (x y : ℕ) :
    wythoffPassGrundy x y false = 0 ↔
      ∃ n : ℕ, (x = ⌊(n : ℝ) * Real.goldenRatio⌋₊ ∧ y = ⌊(n : ℝ) * Real.goldenRatio⌋₊ + n) ∨
        (x = ⌊(n : ℝ) * Real.goldenRatio⌋₊ + n ∧ y = ⌊(n : ℝ) * Real.goldenRatio⌋₊)

/-- **Grundy-one positions of Wythoff's game lie near P-positions.** Let
$\mathcal{G}_1(x, y, 0)$ be the Grundy number of the position $(x, y, 0)$ of Wythoff's game with
a pass, in which the pass has been used; this is the Grundy number of $(x, y)$ in classical
Wythoff's game. If $\mathcal{G}_1(x, y, 0) = 1$, then there are $v, w \in \mathbb{N}$ with
$\mathcal{G}_1(v, w, 0) = 0$ and $(x - v)^2 + (y - w)^2 \le 20$: every position with Grundy
number $1$ lies within Euclidean distance $\sqrt{20}$ of a P-position.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Corollary 1 (`integers-2025-G4-cor-1`). -/
public theorem_wanted wythoffGrundy_one_near_zero (x y : ℕ)
    (h : wythoffPassGrundy x y false = 1) :
    ∃ v w : ℕ, wythoffPassGrundy v w false = 0 ∧
      ((x : ℤ) - v) ^ 2 + ((y : ℤ) - w) ^ 2 ≤ 20

/-- **P-positions of Wythoff's game with a pass for $x, y \le 8$.** Let $\mathcal{G}_1(x, y, p)$ be
the Grundy number of Wythoff's game with a one-time pass ($p = 1$: the pass is still available;
$p = 0$: classical Wythoff's game), and $\mathcal{G}_2(x, y, p)$ the Grundy number of the sum of
Wythoff's game and a pile of $p$ stones. Let
$A = \{(0, 0), (1, 2), (2, 1), (3, 5), (5, 3), (4, 7), (7, 4)\}$,
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$ and
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$. Then for all
natural numbers $x \le 8$ and $y \le 8$: $\mathcal{G}_1(x, y, 0) = 0$ if and only if
$(x, y) \in A$; $\mathcal{G}_1(x, y, 1) = 0$ if and only if $(x, y) \in B$; and
$\mathcal{G}_2(x, y, 1) = 0$ if and only if $(x, y) \in C$.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Lemma 1 (`integers-2025-G4-lem-1`). -/
public theorem_wanted wythoffPass_pPositions_le_eight (x y : ℕ) (hx : x ≤ 8) (hy : y ≤ 8) :
    (wythoffPassGrundy x y false = 0 ↔ (x, y) ∈ wythoffPassSetA) ∧
      (wythoffPassGrundy x y true = 0 ↔ (x, y) ∈ wythoffPassSetB) ∧
      (wythoffPlusStoneGrundy x y true = 0 ↔ (x, y) ∈ wythoffPassSetC)

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
public theorem_wanted wythoffPass_moves_meet_setB_setC (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
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
        (∀ t, 1 ≤ t → t ≤ x → t ≤ y → (x - t, y - t) ∉ wythoffPassSetC))

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
public theorem_wanted wythoffPass_moves_meet_setB_iff_setC (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    ((∃ u < x, (u, y) ∈ wythoffPassSetB) ↔ ∃ u < x, (u, y) ∈ wythoffPassSetC) ∧
    ((∃ v < y, (x, v) ∈ wythoffPassSetB) ↔ ∃ v < y, (x, v) ∈ wythoffPassSetC) ∧
    ((∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetB) ↔
      ∃ t, 1 ≤ t ∧ t ≤ x ∧ t ≤ y ∧ (x - t, y - t) ∈ wythoffPassSetC)

/-- **Pass versus a pile of one stone in Wythoff's game.** Let $\mathcal{G}_1(x, y, p)$ be the
Grundy numbers of Wythoff's game with a pass, where $p = 1$ means the pass is still available,
and let $\mathcal{G}_2(x, y, p)$ be the Grundy numbers of the sum of Wythoff's game and a pile of
$p \in \{0, 1\}$ stones. If $x \ge 9$ or $y \ge 9$, then $\mathcal{G}_1(x, y, 1) = 0$ if and only
if $\mathcal{G}_2(x, y, 1) = 0$: away from the $9 \times 9$ corner, Wythoff's game with an
available pass has the same P-positions as Wythoff's game plus a pile of one stone.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Theorem 4 (`integers-2025-G4-thm-4`). -/
public theorem_wanted wythoffPassGrundy_eq_zero_iff_plusStone (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    wythoffPassGrundy x y true = 0 ↔ wythoffPlusStoneGrundy x y true = 0

/-- **Away from the corner, P-positions with a pass are Wythoff's Grundy-one positions.** Let
$\mathcal{G}_1(x, y, p)$ be the Grundy numbers of Wythoff's game with a pass, where $p = 1$ means
the pass is still available and $p = 0$ means it has been used, so that $\mathcal{G}_1(x, y, 0)$
is the Grundy number of $(x, y)$ in classical Wythoff's game. If $x \ge 9$ or $y \ge 9$, then
$\mathcal{G}_1(x, y, 1) = 0$ if and only if $\mathcal{G}_1(x, y, 0) = 1$.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Corollary 2 (`integers-2025-G4-cor-2`). -/
public theorem_wanted wythoffPassGrundy_true_eq_zero_iff (x y : ℕ) (hxy : 9 ≤ x ∨ 9 ≤ y) :
    wythoffPassGrundy x y true = 0 ↔ wythoffPassGrundy x y false = 1

/-- **P-positions with the pass available lie near Wythoff P-positions.** Let
$\mathcal{G}_1(x, y, p)$ be the Grundy number of Wythoff's game with a one-time pass, where $p = 1$
means the pass is still available and $p = 0$ gives classical Wythoff's game. For all natural
numbers $x, y$ with $\mathcal{G}_1(x, y, 1) = 0$ there exist natural numbers $v, w$ with
$\mathcal{G}_1(v, w, 0) = 0$ and $(x - v)^2 + (y - w)^2 \le 20$, that is, $(v, w)$ lies within
Euclidean distance $\sqrt{20}$ of $(x, y)$.

Source: Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*,
INTEGERS 25 (2025), Article G4, Theorem 5 (`integers-2025-G4-thm-5`). -/
public theorem_wanted wythoffPass_pPosition_near_wythoff_pPosition (x y : ℕ)
    (h : wythoffPassGrundy x y true = 0) :
    ∃ v w : ℕ, wythoffPassGrundy v w false = 0 ∧
      ((x : ℤ) - v) ^ 2 + ((y : ℤ) - w) ^ 2 ≤ 20

end

end MetaMathlibExt
