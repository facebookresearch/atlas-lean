/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Lattice.Nat

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

/-- **NS property.** A function $h : \mathbb{N} \to \mathbb{N}$ has the *NS property* if it is
monotone (weakly increasing) and, for all $z, z' \in \mathbb{N}$ and every natural number
$i \ge 1$, $\lfloor z / 2^i \rfloor = \lfloor z' / 2^i \rfloor$ implies
$\lfloor h(z) / 2^{i-1} \rfloor = \lfloor h(z') / 2^{i-1} \rfloor$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definition 11 (text of arXiv:2207.09134v1, NS property in Section 2). -/
public def HasNSProperty (h : ℕ → ℕ) : Prop :=
  Monotone h ∧ ∀ z z' i : ℕ, 0 < i → z / 2 ^ i = z' / 2 ^ i →
    h z / 2 ^ (i - 1) = h z' / 2 ^ (i - 1)

/-- **Constant functions have the NS property.** For every natural number $c$, the constant
function $\mathbb{N} \to \mathbb{N}$ with value $c$ has the NS property.

Source: characteristic lemma for the NS property of Miyadera, Manabe and Singh,
INTEGERS 25 (2025), Article G3, Definition 11. -/
public theorem hasNSProperty_const (c : ℕ) : HasNSProperty fun _ ↦ c :=
  ⟨monotone_const, fun _ _ _ _ _ ↦ rfl⟩

/-- **The identity function lacks the NS property.** The identity function on the natural
numbers does not have the NS property: $\lfloor 0/2 \rfloor = \lfloor 1/2 \rfloor$, but
$0 \ne 1$.

Source: characteristic lemma for the NS property of Miyadera, Manabe and Singh,
INTEGERS 25 (2025), Article G3, Definition 11. -/
public theorem not_hasNSProperty_id : ¬ HasNSProperty id := fun h ↦ by
  have := h.2 0 1 1 Nat.one_pos rfl
  simp at this

/-- **Constant extension preserves the NS property.** Let $z \in \mathbb{N}$ and let
$h : \mathbb{N} \to \mathbb{N}$ satisfy $h(a) \le h(b)$ whenever $a \le b \le z$, and
$\lfloor h(a) / 2^{i-1} \rfloor = \lfloor h(b) / 2^{i-1} \rfloor$ whenever $a, b \le z$,
$i \ge 1$ and $\lfloor a / 2^i \rfloor = \lfloor b / 2^i \rfloor$. Then the function sending
$x$ to $h(x)$ for $x \le z$ and to $h(z)$ for $x > z$ has the NS property.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 1 (`integers-2025-G3-lem-1`). -/
public theorem_wanted hasNSProperty_extend_const (z : ℕ) (h : ℕ → ℕ)
    (hmono : ∀ a b, a ≤ b → b ≤ z → h a ≤ h b)
    (hns : ∀ a b i : ℕ, a ≤ z → b ≤ z → 0 < i → a / 2 ^ i = b / 2 ^ i →
      h a / 2 ^ (i - 1) = h b / 2 ^ (i - 1)) :
    HasNSProperty fun x ↦ if x ≤ z then h x else h z

/-- **Taking a minimum preserves quotients by powers of two.** Let $a, b, c, k \in \mathbb{N}$. If
$\lfloor a / 2^k \rfloor = \lfloor b / 2^k \rfloor$, then
$\lfloor \min(a, c) / 2^k \rfloor = \lfloor \min(b, c) / 2^k \rfloor$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 2 (i) (`integers-2025-G3-lem-2`). -/
public theorem_wanted min_div_two_pow_eq_of_div_two_pow_eq {a b k : ℕ}
    (hab : a / 2 ^ k = b / 2 ^ k) (c : ℕ) :
    min a c / 2 ^ k = min b c / 2 ^ k

/-- **Quotients of a truncated NS function by powers of two.** Let $h : \mathbb{N} \to \mathbb{N}$
have the NS property and let $z, z', k \in \mathbb{N}$ with $k \ge 1$ and
$\lfloor z' / 2^k \rfloor = \lfloor z / 2^k \rfloor$. Then for every $y \in \mathbb{N}$,
$\lfloor \min(h(z'), y) / 2^{k-1} \rfloor = \lfloor \min(h(z), y) / 2^{k-1} \rfloor$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 2 (ii) (`integers-2025-G3-lem-2`). -/
public theorem_wanted HasNSProperty.min_div_two_pow_eq {h : ℕ → ℕ} (hh : HasNSProperty h)
    {z z' k : ℕ} (hk : 0 < k) (hz : z' / 2 ^ k = z / 2 ^ k) (y : ℕ) :
    min (h z') y / 2 ^ (k - 1) = min (h z) y / 2 ^ (k - 1)

/-- **Mex step for chocolate bars with one function.** Let $g : \mathbb{N} \to \mathbb{N}$ have
the NS property, and let $x, z, c$ be natural numbers with $x \le g(z)$ and $c < x \oplus z$,
where $\oplus$ is nim-sum (bitwise exclusive or). Then $c = u \oplus z$ for some $u < x$, or
$c = \min(g(w), x) \oplus w$ for some $w < z$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (a) (`integers-2025-G3-lem-3`). -/
public theorem_wanted HasNSProperty.exists_of_lt_xor {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z c : ℕ} (hx : x ≤ g z) (hc : c < x ^^^ z) :
    (∃ u < x, c = u ^^^ z) ∨ ∃ w < z, c = min (g w) x ^^^ w

/-- **Mex step for chocolate bars with two functions.** Let $g, h : \mathbb{N} \to \mathbb{N}$
have the NS property, and let $x, y, z, c$ be natural numbers with $x \le g(z)$, $y \le h(z)$
and $c < x \oplus y \oplus z$, where $\oplus$ is nim-sum (bitwise exclusive or). Then
$c = u \oplus y \oplus z$ for some $u < x$, or $c = x \oplus v \oplus z$ for some $v < y$, or
$c = \min(g(w), x) \oplus \min(h(w), y) \oplus w$ for some $w < z$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 3 (b) (`integers-2025-G3-lem-3`). -/
public theorem_wanted HasNSProperty.exists_of_lt_xor_xor {g h : ℕ → ℕ}
    (hg : HasNSProperty g) (hh : HasNSProperty h) {x y z c : ℕ} (hx : x ≤ g z)
    (hy : y ≤ h z) (hc : c < x ^^^ y ^^^ z) :
    (∃ u < x, c = u ^^^ y ^^^ z) ∨ (∃ v < y, c = x ^^^ v ^^^ z) ∨
      ∃ w < z, c = min (g w) x ^^^ min (h w) y ^^^ w

/-- **Mex step for chocolate bars with many functions.** Let $m$ be a natural number, let
$f_1, \dots, f_m : \mathbb{N} \to \mathbb{N}$ have the NS property, and let
$x_1, \dots, x_m, z, c$ be natural numbers with $x_t \le f_t(z)$ for all $t$ and
$c < x_1 \oplus \cdots \oplus x_m \oplus z$, where $\oplus$ is nim-sum (bitwise exclusive or).
Then either there are an index $i$ and some $u < x_i$ such that $c$ is the nim-sum
$x_1 \oplus \cdots \oplus x_m \oplus z$ with $x_i$ replaced by $u$, or there is some $w < z$
with $c = \min(x_1, f_1(w)) \oplus \cdots \oplus \min(x_m, f_m(w)) \oplus w$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 4 (`integers-2025-G3-lem-4`). -/
public theorem_wanted exists_of_lt_foldl_xor {m : ℕ} {f : Fin m → ℕ → ℕ}
    (hf : ∀ t, HasNSProperty (f t)) {x : Fin m → ℕ} {z c : ℕ} (hx : ∀ t, x t ≤ f t z)
    (hc : c < (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ z) :
    (∃ i, ∃ u < x i, c = (List.ofFn (Function.update x i u)).foldl (· ^^^ ·) 0 ^^^ z) ∨
      ∃ w < z, c = (List.ofFn fun t ↦ min (x t) (f t w)).foldl (· ^^^ ·) 0 ^^^ w

/-- **Nim-sum image identity for two NS functions.** Let $g, h : \mathbb{N} \to \mathbb{N}$ have
the NS property and let $x, y, z \in \mathbb{N}$ with $x \le g(z)$ and $y \le h(z)$. Writing
$\oplus$ for the nim-sum (bitwise exclusive or) of natural numbers, the sets
$\{x \oplus y \oplus w : w < z\}$ and $\{\min(g(w), x) \oplus \min(h(w), y) \oplus w : w < z\}$
are equal, where $w$ ranges over the natural numbers.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (19) (`integers-2025-G3-lem-5`). -/
public theorem_wanted HasNSProperty.image_xor_xor_eq {g h : ℕ → ℕ} (hg : HasNSProperty g)
    (hh : HasNSProperty h) {x y z : ℕ} (hx : x ≤ g z) (hy : y ≤ h z) :
    {c | ∃ w < z, c = x ^^^ y ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ min (h w') y ^^^ w'}

/-- **Nim-sum image identity for one NS function.** Let $g : \mathbb{N} \to \mathbb{N}$ have the
NS property and let $x, z \in \mathbb{N}$ with $x \le g(z)$. Writing $\oplus$ for the nim-sum
(bitwise exclusive or) of natural numbers, the sets $\{x \oplus w : w < z\}$ and
$\{\min(g(w), x) \oplus w : w < z\}$ are equal, where $w$ ranges over the natural numbers.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 5, equation (20) (`integers-2025-G3-lem-5`). -/
public theorem_wanted HasNSProperty.image_xor_eq {g : ℕ → ℕ} (hg : HasNSProperty g)
    {x z : ℕ} (hx : x ≤ g z) :
    {c | ∃ w < z, c = x ^^^ w} = {c | ∃ w' < z, c = min (g w') x ^^^ w'}

/-- **Halving functions have the NS property.** For every natural number $m \ge 1$, the function
$x \mapsto \lfloor x / 2^m \rfloor$ on $\mathbb{N}$ has the NS property.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 7 (`integers-2025-G3-lem-7`). -/
public theorem_wanted hasNSProperty_div_two_pow {m : ℕ} (hm : 0 < m) :
    HasNSProperty fun x ↦ x / 2 ^ m

/-- **Equal quotients by a power of two lie in one dyadic block.** Let $i$ be a natural number
and let $z < z'$ be natural numbers. Then $\lfloor z / 2^i \rfloor = \lfloor z' / 2^i \rfloor$ if
and only if there is a natural number $d$ with $d \cdot 2^i \le z$ and $z' < (d + 1) \cdot 2^i$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 8 (a) (`integers-2025-G3-lem-8`). -/
public theorem_wanted div_two_pow_eq_iff_exists_block {z z' i : ℕ} (hzz' : z < z') :
    z / 2 ^ i = z' / 2 ^ i ↔ ∃ d, d * 2 ^ i ≤ z ∧ z' < (d + 1) * 2 ^ i

/-- **Dyadic splitting of two numbers with different quotients.** Let $z, z', i$ be natural
numbers with $\lfloor z / 2^i \rfloor < \lfloor z' / 2^i \rfloor$. Then there are natural numbers
$c$, $s$ and $t$ with $s \ge i$, $t < 2^s$, $z = c \cdot 2^{s+1} + t$ and
$c \cdot 2^{s+1} + 2^s \le z'$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 8 (b) (`integers-2025-G3-lem-8`). -/
public theorem_wanted exists_split_of_div_two_pow_lt {z z' i : ℕ}
    (h : z / 2 ^ i < z' / 2 ^ i) :
    ∃ c s t : ℕ, i ≤ s ∧ t < 2 ^ s ∧ z = c * 2 ^ (s + 1) + t ∧
      c * 2 ^ (s + 1) + 2 ^ s ≤ z'

/-- **Indicator functions with the NS property.** Let $f : \mathbb{N} \to \mathbb{N}$ be monotone,
with $f(x) \le 1$ for all $x$ and $f(x) = 1$ for some $x$. Then $f$ has the NS property if and
only if there is an even $m \in \mathbb{N}$ such that $f$ is the indicator function of
$\{n \in \mathbb{N} : n \ge m\}$, that is, $f(n) = 1$ for $n \ge m$ and $f(n) = 0$ for $n < m$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 9 (`integers-2025-G3-lem-9`). -/
public theorem_wanted indicator_Ici_even_iff_hasNSProperty {f : ℕ → ℕ} (hf : Monotone f)
    (hle : ∀ x, f x ≤ 1) (hone : ∃ x, f x = 1) :
    (∃ m, Even m ∧ f = (Set.Ici m).indicator 1) ↔ HasNSProperty f

/-- **Grundy number of a chocolate bar.** Let $f_1, \dots, f_s : \mathbb{N} \to \mathbb{N}$. For
coordinates $x = (x_1, \dots, x_s) \in \mathbb{N}^s$ and a width $z \in \mathbb{N}$, the position
$(x, z)$ stands for the chocolate bar $\mathrm{CB}(f_1, \dots, f_s, x_1, \dots, x_s, z)$, whose
column at width $w \le z$ extends $\min(f_t(w), x_t) + 1$ cells along axis $t$. A move either
lowers one coordinate $x_i$ to some $u < x_i$, keeping the width $z$, or cuts the width to some
$w < z$, which replaces every $x_t$ by $\min(x_t, f_t(w))$. The Grundy number of $(x, z)$ is the
mex (least natural number not attained) of the Grundy numbers of the positions reachable from
$(x, z)$ in one move. It is defined for all $(x, z)$; the bars themselves are the positions with
$x_t \le f_t(z)$ for all $t$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 2, 8, 9 and 10 (two functions) and Section 4, before Theorem 5
(four functions). -/
public noncomputable def chocolateBarGrundy {s : ℕ} (f : Fin s → ℕ → ℕ) (x : Fin s → ℕ)
    (z : ℕ) : ℕ :=
  sInf {m | (∀ i u, u < x i → chocolateBarGrundy f (Function.update x i u) z ≠ m) ∧
    ∀ w, w < z → chocolateBarGrundy f (fun t ↦ min (x t) (f t w)) w ≠ m}
termination_by z + ∑ t, x t
decreasing_by
  · have hlt : ∑ t, Function.update x i u t < ∑ t, x t := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨i, Finset.mem_univ _, by simpa⟩
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; omega
      · simp [Function.update_of_ne hj]
    omega
  · have hle : ∑ t, min (x t) (f t w) ≤ ∑ t, x t :=
      Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
    omega

/-- **Mex recursion for the Grundy number of a chocolate bar.** Let $f_1, \dots, f_s$ be
functions $\mathbb{N} \to \mathbb{N}$ and write $G(x, z)$ for the Grundy number of the chocolate
bar with coordinates $x = (x_1, \dots, x_s) \in \mathbb{N}^s$ and width $z \in \mathbb{N}$. For
all $x$ and $z$, $G(x, z)$ is the least natural number $m$ such that $m \ne G(x', z)$ for every
$x'$ obtained from $x$ by replacing one coordinate $x_i$ with some $u < x_i$, and
$m \ne G(x^{(w)}, w)$ for every $w < z$, where $x^{(w)}_t = \min(x_t, f_t(w))$ for all $t$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Definitions 9 and 10. -/
public theorem chocolateBarGrundy_eq {s : ℕ} (f : Fin s → ℕ → ℕ) (x : Fin s → ℕ) (z : ℕ) :
    chocolateBarGrundy f x z =
      sInf {m | (∀ i u, u < x i → chocolateBarGrundy f (Function.update x i u) z ≠ m) ∧
        ∀ w, w < z → chocolateBarGrundy f (fun t ↦ min (x t) (f t w)) w ≠ m} := by
  rw [chocolateBarGrundy]

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

/-- **Pass indicator of Nim with a restricted pass.** For $s$ piles with thresholds
$m_0, \dots, m_{s-1}$ and pile sizes $x_0, \dots, x_{s-1}$ (natural numbers), the pass
indicator is $1$ if $m_j \le x_j$ for some pile $j$ (the pass may be used), and $0$ if
$x_j < m_j$ for every pile $j$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 and Corollary 2 (the function `F`). -/
public def nimPassIndicator {s : ℕ} (m x : Fin s → ℕ) : ℕ :=
  if ∃ j, m j ≤ x j then 1 else 0

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

/-- **Nim-sum sets under clamping by functions with the NS property.** Let $m \in \mathbb{N}$,
let $f_0, \dots, f_{m-1} : \mathbb{N} \to \mathbb{N}$ have the NS property, and let
$x_0, \dots, x_{m-1}, z \in \mathbb{N}$ satisfy $x_t \le f_t(z)$ for every $t < m$. Then
$$
\{x_0 \oplus \cdots \oplus x_{m-1} \oplus w : w < z\} =
\{\min(x_0, f_0(w)) \oplus \cdots \oplus \min(x_{m-1}, f_{m-1}(w)) \oplus w : w < z\},
$$
where $\oplus$ denotes nim-sum (bitwise exclusive or).

The printed left-hand nim-sum carries a stray index $j \ne i$ with $i$ unbound; it is read as the
full nim-sum, as in Lemma 5 (the case of two functions), which the proof generalises.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 6 (`integers-2025-G3-lem-6`). -/
public theorem_wanted image_foldl_xor_eq_image_min {m : ℕ} {f : Fin m → ℕ → ℕ}
    (hf : ∀ t, HasNSProperty (f t)) {x : Fin m → ℕ} {z : ℕ} (hx : ∀ t, x t ≤ f t z) :
    {c | ∃ w < z, c = (List.ofFn x).foldl (· ^^^ ·) 0 ^^^ w} =
      {c | ∃ w < z, c = (List.ofFn fun t ↦ min (x t) (f t w)).foldl (· ^^^ ·) 0 ^^^ w}

/-- **The NS property characterises nim-sum Grundy numbers of two-dimensional chocolate bars.**
Let $f : \mathbb{N} \to \mathbb{N}$ be monotone. Then $f$ has the NS property if and only if, for
all $x, z \in \mathbb{N}$ with $x \le f(z)$, the chocolate bar $\mathrm{CB}(f, 0, x, 0, z)$ of
width $z$ (first function $f$, first coordinate $x$, second function constantly $0$, second
coordinate $0$) has Grundy number $x \oplus z$, where $\oplus$ denotes nim-sum (bitwise exclusive
or).

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 2 (`integers-2025-G3-thm-2`). -/
public theorem_wanted hasNSProperty_iff_chocolateBarGrundy_depth_zero {f : ℕ → ℕ}
    (hf : Monotone f) :
    HasNSProperty f ↔
      ∀ x z, x ≤ f z → chocolateBarGrundy ![f, fun _ ↦ 0] ![x, 0] z = x ^^^ z

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

/-- **Nim-sum Grundy numbers of chocolate bars with two functions.** Let
$g, h : \mathbb{N} \to \mathbb{N}$ be monotone. Then $g$ and $h$ both have the NS property if and
only if, for all natural numbers $x, y, z$ with $x \le g(z)$ and $y \le h(z)$, the Grundy number
of the chocolate bar $\mathrm{CB}(g, h, x, y, z)$ equals $x \oplus y \oplus z$, where $\oplus$ is
nim-sum (bitwise exclusive or).

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Theorem 4 (`integers-2025-G3-thm-4`). -/
public theorem_wanted hasNSProperty_and_iff_chocolateBarGrundy_eq_xor {g h : ℕ → ℕ}
    (hg : Monotone g) (hh : Monotone h) :
    HasNSProperty g ∧ HasNSProperty h ↔
      ∀ x y z, x ≤ g z → y ≤ h z → chocolateBarGrundy ![g, h] ![x, y] z = x ^^^ y ^^^ z

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

/-- **Sections of the Nim pass indicator with the NS property.** Let $s \in \mathbb{N}$ and
$m \in \mathbb{N}^s$ with $m_i > 0$ for every $i < s$, and let $F : \mathbb{N}^s \to \mathbb{N}$ be
the pass indicator of $m$: $F(x) = 1$ if $m_j \le x_j$ for some $j$, and $F(x) = 0$ otherwise.
For $x \in \mathbb{N}^s$, $i < s$ and $t \in \mathbb{N}$ write $x[i \mapsto t]$ for $x$ with its
$i$-th coordinate replaced by $t$. Then the following are equivalent: (a) for all
$x \in \mathbb{N}^s$ and $i < s$, the function $t \mapsto F(x[i \mapsto t])$ has the NS property;
(b) $m_i$ is even for every $i < s$.

Source: Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of
Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025),
Article G3, Lemma 10 (`integers-2025-G3-lem-10`). -/
public theorem_wanted nimPassIndicator_sections_hasNSProperty_iff {s : ℕ} {m : Fin s → ℕ}
    (hm : ∀ i, 0 < m i) :
    (∀ (x : Fin s → ℕ) i, HasNSProperty fun t ↦ nimPassIndicator m (Function.update x i t)) ↔
      ∀ i, Even (m i)

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
