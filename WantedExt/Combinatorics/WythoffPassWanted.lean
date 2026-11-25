/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.WythoffPass

namespace MetaMathlibExt

@[expose] public section

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
