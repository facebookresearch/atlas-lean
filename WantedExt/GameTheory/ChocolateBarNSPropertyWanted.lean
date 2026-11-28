/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Lattice.Nat
public import MathlibExt.Data.Nat.DyadicBlock
public import MathlibExt.GameTheory.ChocolateBarNSProperty
public import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtXor
public import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtFoldlXor
public import MathlibExt.GameTheory.ChocolateBarNSPropertyImageXorEq
public import MathlibExt.GameTheory.ChocolateBarNSPropertyExistsOfLtXorXor
public import MathlibExt.GameTheory.ChocolateBarNSPropertyImageXorXorEq
public import MathlibExt.GameTheory.ChocolateBarNSPropertyGrundy
public import MathlibExt.GameTheory.NimPassIndicator

/-! # The NS property of chocolate-bar games (Miyadera, Manabe, Singh)

Arithmetic lemmas on the `NS` property and nim-sums from R. Miyadera, H. Manabe and
A. Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*,
INTEGERS 25 (2025), Article G3. The definition of the `NS` property is taken from the
arXiv version (arXiv:2207.09134v1, Section 2); nim-sum `⊕` is `Nat.xor` (`^^^`) and
`Z≥0` is `ℕ`.

The game theorems use the published move sets: `chocolateBarGrundy` is the Grundy number of the
bar `CB(f₁, …, f_s, x₁, …, x_s, z)` of Definitions 2, 9, 10 and Section 4 (the column at width
`w` has extent `min (f t w) (x t) + 1` along axis `t`), and `heightChocolateBarGrundy` is the
Grundy number of the bar `CB(F, x₁, …, x_s, y)` of Definitions 13, 15 and 17 (the column at
`(u₁, …, u_s)` has height `min (F u) y + 1`). Both are defined on all coordinate tuples by the
mex recursion over the paper's move sets; the theorems quantify over the actual bars, i.e. the
positions with `x t ≤ f t z`, respectively `y ≤ F x`, a set closed under moves. A P-position is
a position of Grundy number `0` (Theorem 1 (i), the classical Sprague-Grundy theorem).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The single bitter square has Grundy number zero.** For all functions
$f_1, \dots, f_s : \mathbb{N} \to \mathbb{N}$, the chocolate bar
$\mathrm{CB}(f_1, \dots, f_s, 0, \dots, 0, 0)$, whose coordinates and width are all $0$, has
Grundy number $0$: it is a single bitter square and has no move.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 9 and 10. -/
public theorem chocolateBarGrundy_zero {s : ℕ} (f : Fin s → ℕ → ℕ) :
    chocolateBarGrundy f (fun _ ↦ 0) 0 = 0 := by
  rw [chocolateBarGrundy_eq]
  exact Nat.sInf_eq_zero.mpr (Or.inl ⟨fun _ u hu ↦ absurd hu (Nat.not_lt_zero u),
    fun w hw ↦ absurd hw (Nat.not_lt_zero w)⟩)

/-- **Grundy number of a chocolate bar with a height function.** Let $s \in \mathbb{N}$ and
$F : \mathbb{N}^s \to \mathbb{N}$. The $(s + 1)$-dimensional chocolate bar
$\mathrm{CB}(F, x_1, \dots, x_s, y)$ has, at each $u = (u_1, \dots, u_s)$ with $u_t \le x_t$ for
all $t$, a column of height $\min(F(u), y) + 1$. A move either lowers one coordinate $x_i$ to some
$a < x_i$, which clamps the height to $\min(F(x'), y)$ for the new position $x'$, or lowers the
height $y$ to some $v < y$. The Grundy number of $\mathrm{CB}(F, x_1, \dots, x_s, y)$ is the mex
(least natural number not attained) of the Grundy numbers of the positions reachable in one
move. It is defined for all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$; the bars themselves are
the positions with $y \le F(x)$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 15, 16 and 17 (and Definition 13 with second function `0`). -/
public noncomputable def heightChocolateBarGrundy {s : ℕ} (F : (Fin s → ℕ) → ℕ)
    (x : Fin s → ℕ) (y : ℕ) : ℕ :=
  sInf {m | (∀ i u, u < x i → heightChocolateBarGrundy F (Function.update x i u)
      (min (F (Function.update x i u)) y) ≠ m) ∧
    ∀ v, v < y → heightChocolateBarGrundy F x v ≠ m}
termination_by (∑ t, x t) + y
decreasing_by
  · have hlt : ∑ t, Function.update x i u t < ∑ t, x t := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, by simpa⟩
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hj]
    have := min_le_right (F (Function.update x i u)) y
    omega
  · omega

/-- **Mex recursion for chocolate bars with a height function.** Let $s \in \mathbb{N}$ and
$F : \mathbb{N}^s \to \mathbb{N}$, and write $G(x, y)$ for the Grundy number of the chocolate bar
$\mathrm{CB}(F, x_1, \dots, x_s, y)$. For all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$,
$G(x, y)$ is the least natural number $m$ such that $m \ne G(x', \min(F(x'), y))$ for every $x'$
obtained from $x$ by lowering one coordinate $x_i$ to some $u < x_i$, and $m \ne G(x, v)$ for
every $v < y$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 17. -/
public theorem heightChocolateBarGrundy_eq {s : ℕ} (F : (Fin s → ℕ) → ℕ) (x : Fin s → ℕ)
    (y : ℕ) :
    heightChocolateBarGrundy F x y =
      sInf {m | (∀ i u, u < x i → heightChocolateBarGrundy F (Function.update x i u)
          (min (F (Function.update x i u)) y) ≠ m) ∧
        ∀ v, v < y → heightChocolateBarGrundy F x v ≠ m} := by
  rw [heightChocolateBarGrundy]

/-- **The single bitter cube has Grundy number zero.** For every $s \in \mathbb{N}$ and every
$F : \mathbb{N}^s \to \mathbb{N}$, the chocolate bar $\mathrm{CB}(F, 0, \dots, 0, 0)$ has no move,
so its Grundy number is $0$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 17. -/
public theorem heightChocolateBarGrundy_zero {s : ℕ} (F : (Fin s → ℕ) → ℕ) :
    heightChocolateBarGrundy F (fun _ ↦ 0) 0 = 0 := by
  rw [heightChocolateBarGrundy_eq]
  exact Nat.sInf_eq_zero.mpr (Or.inl ⟨fun _ u hu ↦ absurd hu (Nat.not_lt_zero u),
    fun v hv ↦ absurd hv (Nat.not_lt_zero v)⟩)

/-- **The Nim pass indicator is at most one.** For every $s \in \mathbb{N}$ and all
$m, x \in \mathbb{N}^s$, the pass indicator of $m$ at $x$ is at most $1$; that is, it takes values
in $\{0, 1\}$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 (the function `F`). -/
public theorem nimPassIndicator_le_one {s : ℕ} (m x : Fin s → ℕ) : nimPassIndicator m x ≤ 1 := by
  unfold nimPassIndicator; split_ifs <;> omega

/-- **The pass is unavailable from the empty position.** Let $s \in \mathbb{N}$ and
$m \in \mathbb{N}^s$ with $m_i > 0$ for every $i < s$. Then the pass indicator of $m$ takes the
value $0$ at the zero tuple $(0, \dots, 0)$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 (the function `F`). -/
public theorem nimPassIndicator_zero {s : ℕ} {m : Fin s → ℕ} (hm : ∀ i, 0 < m i) :
    nimPassIndicator m (fun _ ↦ 0) = 0 := by
  rw [nimPassIndicator, ite_eq_right_iff]
  rintro ⟨j, hj⟩
  exact absurd hj (Nat.not_le.mpr (hm j))

/-- **NS property of sections and the three-dimensional chocolate bar.** Let
$F : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ be monotone for the componentwise order. Then
the sections $x \mapsto F(n, x)$ and $w \mapsto F(w, n)$ have the NS property for every
$n \in \mathbb{N}$ if and only if, for all natural numbers $w$, $x$, $y$ with $y \le F(w, x)$,
the Grundy number of the chocolate bar $\mathrm{CB}(F, w, x, y)$, whose column at $(u, v)$
(with $u \le w$, $v \le x$) has height $\min(F(u, v), y) + 1$, equals the nim-sum
$w \oplus x \oplus y$ (bitwise exclusive or).

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 3 (`integers-2025-G3-thm-3`). -/
public theorem_wanted sections_hasNSProperty_iff_heightChocolateBarGrundy_eq_xor
    {F : ℕ → ℕ → ℕ} (hF : Monotone fun p : ℕ × ℕ ↦ F p.1 p.2) :
    ((∀ n, HasNSProperty (F n)) ∧ ∀ n, HasNSProperty fun w ↦ F w n) ↔
      ∀ w x y, y ≤ F w x →
        heightChocolateBarGrundy (fun v ↦ F (v 0) (v 1)) ![w, x] y = w ^^^ x ^^^ y

/-- **Nim-sum Grundy numbers of chocolate bars with four functions.** Let
$f_1, f_2, f_3, f_4 : \mathbb{N} \to \mathbb{N}$ be monotone. Then all four have the NS property if
and only if, for all natural numbers $x_1, x_2, x_3, x_4, z$ with $x_t \le f_t(z)$ for every $t$,
the Grundy number of the chocolate bar $\mathrm{CB}(f_1, f_2, f_3, f_4, x_1, x_2, x_3, x_4, z)$
equals $x_1 \oplus x_2 \oplus x_3 \oplus x_4 \oplus z$, where $\oplus$ is nim-sum (bitwise
exclusive or).

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 5 (`integers-2025-G3-thm-5`). -/
public theorem_wanted forall_hasNSProperty_iff_chocolateBarGrundy_eq_xor_four
    {f : Fin 4 → ℕ → ℕ} (hf : ∀ t, Monotone (f t)) :
    (∀ t, HasNSProperty (f t)) ↔
      ∀ (x : Fin 4 → ℕ) z, (∀ t, x t ≤ f t z) →
        chocolateBarGrundy f x z = x 0 ^^^ x 1 ^^^ x 2 ^^^ x 3 ^^^ z

/-- **P-positions of a three-dimensional chocolate bar with floor-quotient height.** Let $k$ be a
natural number with $k \equiv 3 \pmod 4$, and let $F(w, x) = \lfloor (w + x) / k \rfloor$. For
all $w, x, y \in \mathbb{N}$ with $y \le F(w, x)$, the three-dimensional chocolate bar
$\mathrm{CB}(F, w, x, y)$ has Grundy number $0$ (is a P-position) if and only if
$w \oplus x \oplus y = 0$, where $\oplus$ denotes nim-sum (bitwise exclusive or).

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 8 (`integers-2025-G3-thm-8`). -/
public theorem_wanted heightChocolateBarGrundy_add_div_eq_zero_iff {k : ℕ} (hk : k % 4 = 3)
    {w x y : ℕ} (hy : y ≤ (w + x) / k) :
    heightChocolateBarGrundy (fun v ↦ (v 0 + v 1) / k) ![w, x] y = 0 ↔ w ^^^ x ^^^ y = 0

/-- **Height-one chocolate bars with nim-sum Grundy numbers.** Let $s \in \mathbb{N}$ and let
$F : \mathbb{N}^s \to \mathbb{N}$ be monotone for the coordinatewise order, with $F(x) \le 1$ for
all $x$. For $x \in \mathbb{N}^s$, $i < s$ and $t \in \mathbb{N}$ write $x[i \mapsto t]$ for $x$
with its $i$-th coordinate replaced by $t$, and suppose that for all $x$ and $i$ there is a $t$
with $F(x[i \mapsto t]) = 1$. Write $\oplus$ for nim-sum. Then the following are equivalent:
(a) for all $x \in \mathbb{N}^s$ and $i < s$ there is an even $m \in \mathbb{N}$ (depending on $x$
and $i$) such that $F(x[i \mapsto t]) = 1$ for $t \ge m$ and $F(x[i \mapsto t]) = 0$ for $t < m$;
(b) for all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$ with $y \le F(x)$, the Grundy number of the
chocolate bar $\mathrm{CB}(F, x_0, \dots, x_{s-1}, y)$ is
$x_0 \oplus \cdots \oplus x_{s-1} \oplus y$.

The hypothesis that every section takes the value $1$ is that of Lemma 9, from which the
corollary is derived.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Corollary 1 (`integers-2025-G3-cor-1`). -/
public theorem_wanted indicator_sections_iff_heightChocolateBarGrundy_eq_xor {s : ℕ}
    {F : (Fin s → ℕ) → ℕ} (hF : Monotone F) (hle : ∀ x, F x ≤ 1)
    (hone : ∀ (x : Fin s → ℕ) i, ∃ t, F (Function.update x i t) = 1) :
    (∀ (x : Fin s → ℕ) i, ∃ m, Even m ∧
        (fun t ↦ F (Function.update x i t)) = (Set.Ici m).indicator 1) ↔
      ∀ x y, y ≤ F x → heightChocolateBarGrundy F x y = (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ y

/-- **Nim with a restricted pass.** Let $s \in \mathbb{N}$ and $m \in \mathbb{N}^s$ with $m_i > 0$
for every $i < s$, and let $F : \mathbb{N}^s \to \mathbb{N}$ be the pass indicator of $m$:
$F(x) = 1$ if $m_j \le x_j$ for some $j$, and $F(x) = 0$ otherwise. Write $\oplus$ for nim-sum.
Then the following are equivalent: (a) for all $x \in \mathbb{N}^s$ and $p \in \mathbb{N}$ with
$p \le F(x)$, the Grundy number of the chocolate bar $\mathrm{CB}(F, x_0, \dots, x_{s-1}, p)$ is
$x_0 \oplus \cdots \oplus x_{s-1} \oplus p$; (b) $m_i$ is even for every $i < s$.

The bar is Nim on $s$ piles with a one-time pass usable only while $F(x) = 1$: removing stones
from a pile, reaching $x'$, replaces $p$ by $\min(F(x'), p)$, and the pass lowers $p$ from $1$
to $0$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Corollary 2 (`integers-2025-G3-cor-2`). -/
public theorem_wanted nimPassGrundy_eq_xor_iff {s : ℕ} {m : Fin s → ℕ} (hm : ∀ i, 0 < m i) :
    (∀ (x : Fin s → ℕ) p, p ≤ nimPassIndicator m x →
        heightChocolateBarGrundy (nimPassIndicator m) x p =
          (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ p) ↔
      ∀ i, Even (m i)

end

end MetaMathlibExt
