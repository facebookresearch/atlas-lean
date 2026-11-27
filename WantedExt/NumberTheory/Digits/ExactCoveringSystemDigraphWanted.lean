/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphTypeTwo
public import MathlibExt.NumberTheory.Digits.NegTwoCubeDvd
public import MathlibExt.NumberTheory.Digits.NineDvdExponent
public import MathlibExt.NumberTheory.Digits.PositiveTwoCubeDvd
public import MathlibExt.NumberTheory.Digits.ThreePowCubeBound
public import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeOneRelIso
public import MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeThreeRelIso

/-!
# Exact covering system digraphs of degree 2

Statements from Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and
Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107.
The theorem `ecsd_type_three_relIso` is proved in
`MathlibExt.NumberTheory.Digits.ExactCoveringSystemDigraphEcsdTypeThreeRelIso`.

For a representative set `S = {(aᵢ, dᵢ)}` of an exact covering system, the exact
covering system digraph (ECSD) `G_S` has vertex set `ℤ` and an edge `n → dᵢ n + aᵢ`
for each `n` and each `i`; the paper writes it `G(d₁n + a₁, …, d_r n + a_r)`. Here it is
the relation `ecsdAdj d a` with `d a : Fin r → ℤ`, so `G(d₁n + a₁, d₂n + a₂)` is
`ecsdAdj ![d₁, d₂] ![a₁, a₂]`.

Conventions used below, following Section 1 of the paper:
* a *cyclic vertex* `m` is a vertex on a cycle, stated as
  `Relation.TransGen (ecsdAdj d a) m m`;
* the ECSD *has a single component* when every two vertices are joined in the
  underlying undirected graph, stated as `∀ m n, Relation.EqvGen (ecsdAdj d a) m n`;
* a *`k`-descendant* of `m` is the end of a directed walk of exactly `k` edges from `m`
  (`IsKDescendant`);
* a cycle `(c₁, …, c_t)` is a list of distinct vertices with consecutive edges closing
  up (`IsDigraphCycle`);
* `ord(g, a)` is `orderOf (g : ZMod a)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Cycles of the digraph $G(2n, 2n - a)$.** For an integer $b$ write $G_b$ for the digraph
$G(2n, 2n - b)$ on $\mathbb{Z}$, with an edge $m \to 2m$ and an edge $m \to 2m - b$ for every
integer $m$. Let $a$ be an odd natural number, write $x \bmod a$ for the residue of $x$ in
$\{0, \dots, a - 1\}$, and write $\operatorname{ord}(2, q)$ for the multiplicative order of $2$
modulo $q$. Then (i) $G_a$ has a loop at $m$ if and only if $m = 0$ or $m = a$; (ii) $G_a$ has a
directed walk of positive length from $m$ back to $m$ if and only if $0 \le m \le a$; (iii) the
list $(2^k \bmod a)_{0 \le k < \operatorname{ord}(2, a)}$ is a cycle of $G_a$; for every integer
$b$ with $1 \le b < a$ the list $(b 2^k \bmod a)_{0 \le k < \operatorname{ord}(2, a/\gcd(a, b))}$
is a cycle of $G_a$; and every cycle of $G_a$ with more than one vertex is a rotation of one of
these lists for some integer $b$ with $1 \le b < a$; (iv) for all natural numbers $t$ and $a'$
with $a = t a'$, a list $(c_1, \dots, c_s)$ of integers is a cycle of $G_{a'}$ if and only if
$(t c_1, \dots, t c_s)$ is a cycle of $G_a$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 6
(`integers-2026-A107-thm-6`). -/
theorem_wanted ecsd_two_two_sub_cycles (a : ℕ) (ha : Odd a) :
    (∀ m : ℤ, ecsdAdj ![2, 2] ![0, -(a : ℤ)] m m ↔ m = 0 ∨ m = a) ∧
    (∀ m : ℤ, Relation.TransGen (ecsdAdj ![2, 2] ![0, -(a : ℤ)]) m m ↔ 0 ≤ m ∧ m ≤ a) ∧
    IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)])
      ((List.range (orderOf (2 : ZMod a))).map fun k => (2 : ℤ) ^ k % a) ∧
    (∀ b : ℤ, 1 ≤ b → b < a → IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)])
      ((List.range (orderOf (2 : ZMod (a / Int.gcd a b)))).map fun k => (b * 2 ^ k) % a)) ∧
    (∀ c : List ℤ, IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)]) c → 1 < c.length →
      ∃ b : ℤ, 1 ≤ b ∧ b < a ∧ c ~r
        (List.range (orderOf (2 : ZMod (a / Int.gcd a b)))).map fun k => (b * 2 ^ k) % a) ∧
    ∀ a' t : ℕ, a = t * a' → ∀ c : List ℤ,
      (IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a' : ℤ)]) c ↔
        IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)]) (c.map ((t : ℤ) * ·)))

/-- **Descendants in the digraph $G(2n, -2n + a)$.** Let $a$ and $m$ be integers and let
$k \ge 1$. In the digraph $G(2n, -2n + a)$ on $\mathbb{Z}$, with an edge $x \to 2x$ and an edge
$x \to -2x + a$ for every integer $x$, the $k$-descendants of $m$ (the ends of directed walks of
exactly $k$ edges from $m$) are exactly the integers $2^k m$, the integers $2^k m - ba$ and
$-(2^k m - ba)$ for natural numbers $b$ with $1 \le b < 2^{k-1}$, and $-(2^k m - 2^{k-1} a)$.

This holds for every integer $a$, not only for odd $a$, for which $G(2n, -2n + a)$ is an exact
covering system digraph.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Proposition 1
(`integers-2026-A107-prop-1`). -/
theorem_wanted ecsd_two_neg_two_descendants (a m n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    IsKDescendant (ecsdAdj ![2, -2] ![0, a]) k m n ↔
      n = 2 ^ k * m ∨
        (∃ b : ℕ, 1 ≤ b ∧ b < 2 ^ (k - 1) ∧
          (n = 2 ^ k * m - b * a ∨ n = -(2 ^ k * m - b * a))) ∨
        n = -(2 ^ k * m - 2 ^ (k - 1) * a)

/-- **Cycles of the digraph $G(2n, -2n + a)$.** For an integer $b$ write $G_b$ for the digraph
$G(2n, -2n + b)$ on $\mathbb{Z}$, with an edge $m \to 2m$ and an edge $m \to -2m + b$ for every
integer $m$. Let $a$ be an odd natural number. Then (i) $G_a$ has a loop at $m$ if and only if
$m = 0$ or $3m = a$; (ii) $G_a$ has a directed walk of positive length from $m$ back to $m$ if
and only if $0 \le m < a/2$; (iii) for all natural numbers $t$ and $a'$ with $a = t a'$, a list
$(c_1, \dots, c_s)$ of integers is a cycle of $G_{a'}$ if and only if $(t c_1, \dots, t c_s)$ is
a cycle of $G_a$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 7
(`integers-2026-A107-thm-7`). -/
theorem_wanted ecsd_two_neg_two_cycles (a : ℕ) (ha : Odd a) :
    (∀ m : ℤ, ecsdAdj ![2, -2] ![0, (a : ℤ)] m m ↔ m = 0 ∨ 3 * m = a) ∧
    (∀ m : ℤ, Relation.TransGen (ecsdAdj ![2, -2] ![0, (a : ℤ)]) m m ↔ 0 ≤ m ∧ 2 * m < a) ∧
    ∀ a' t : ℕ, a = t * a' → ∀ c : List ℤ,
      (IsDigraphCycle (ecsdAdj ![2, -2] ![0, (a' : ℤ)]) c ↔
        IsDigraphCycle (ecsdAdj ![2, -2] ![0, (a : ℤ)]) (c.map ((t : ℤ) * ·)))

/-- **Descendants modulo the difference of offsets.** Let $a_1, a_2, x, y$ be integers and
$k \in \mathbb{N}$. If $y$ is a $k$-descendant of $x$ in $G(-2n + a_1, -2n + a_2)$, that is,
the end of a directed walk of exactly $k$ edges from $x$, then
$$y \equiv (-2)^k x + a_1 \cdot \frac{1 - (-2)^k}{3} \pmod{|a_1 - a_2|}.$$
The quotient is an integer because $3$ divides $1 - (-2)^k$.

The exact-covering condition on $a_1, a_2$ is not needed.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 8
(`integers-2026-A107-thm-8`). -/
theorem_wanted ecsd_neg_two_descendant_modEq (a₁ a₂ m n : ℤ) (k : ℕ)
    (h : IsKDescendant (ecsdAdj ![-2, -2] ![a₁, a₂]) k m n) :
    n ≡ (-2) ^ k * m + a₁ * ((1 - (-2) ^ k) / 3) [ZMOD |a₁ - a₂|]

/-- **Cyclic vertices in every residue class.** Let $a_1, a_2$ be integers with $a_1 - a_2$
odd. Then every residue class modulo $|a_1 - a_2|$ contains a vertex that lies on a directed
cycle of $G(-2n + a_1, -2n + a_2)$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 9
(`integers-2026-A107-thm-9`). -/
theorem_wanted ecsd_neg_two_cyclic_residues (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) (c : ℤ) :
    ∃ m : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![a₁, a₂]) m m ∧ m ≡ c [ZMOD |a₁ - a₂|]

/-- **Cycles of $G(-2n, -2n + a)$.** Let $a$ be an odd natural number and $G = G(-2n, -2n + a)$.
A cycle of $G$ is a list $(c_1, \dots, c_t)$, $t \ge 1$, of distinct integers with edges
$c_1 \to c_2, \dots, c_{t-1} \to c_t$ and $c_t \to c_1$; a vertex is cyclic if it lies on a
cycle. For an integer $x$ let $\hat{x}$ be the representative of $x$ modulo $a$ in the interval
$(-a/3, 2a/3]$, and let $\operatorname{ord}_q(-2)$ be the multiplicative order of $-2$ modulo
$q$. Then:
(i) for every integer $m$, $G$ has a loop at $m$ iff $m = 0$ or $3m = a$;
(ii) an integer $m$ is cyclic iff $-a \le 3m \le 2a$;
(iii) if $3 \nmid a$, then $G$ has exactly $a$ cyclic vertices and each residue class modulo
$a$ contains exactly one of them; if $3 \mid a$, then $G$ has exactly $a + 1$ cyclic vertices,
each residue class modulo $a$ other than the class of $2a/3$ contains exactly one of them, and
the two-vertex list $(-a/3, 2a/3)$ is a cycle of $G$;
(iv) the list $(\widehat{(-2)^k})_{0 \le k < \operatorname{ord}_a(-2)}$ is a cycle of $G$, and
for every integer $b$ with $-a < 3b < 2a$, $b \ne 0$ and $3b \ne a$, so is the list
$(\widehat{b(-2)^k})_{0 \le k < \operatorname{ord}_{a/\gcd(a, b)}(-2)}$;
(v) if $a = t a'$ with $t, a' \in \mathbb{N}$, then a list $C$ of integers is a cycle of
$G(-2n, -2n + a')$ iff the list $tC$ obtained by multiplying every entry by $t$ is a cycle of
$G$.

The paper also assumes $a'$ odd in (v); this follows from $a$ odd.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 10
(`integers-2026-A107-thm-10`). -/
theorem_wanted ecsd_neg_two_neg_two_cycles (a : ℕ) (ha : Odd a) :
    (∀ m : ℤ, ecsdAdj ![-2, -2] ![0, (a : ℤ)] m m ↔ m = 0 ∨ 3 * m = a) ∧
    (∀ m : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m ↔
      -(a : ℤ) ≤ 3 * m ∧ 3 * m ≤ 2 * a) ∧
    (¬ 3 ∣ a →
      {m : ℤ | Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m}.ncard = a ∧
      ∀ c : ℤ, ∃! m : ℤ,
        Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m ∧ m ≡ c [ZMOD a]) ∧
    (3 ∣ a →
      {m : ℤ | Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m}.ncard = a + 1 ∧
      (∀ c : ℤ, ¬ c ≡ 2 * ((a : ℤ) / 3) [ZMOD a] → ∃! m : ℤ,
        Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m ∧ m ≡ c [ZMOD a]) ∧
      IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) [-((a : ℤ) / 3), 2 * ((a : ℤ) / 3)]) ∧
    IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)])
      ((List.range (orderOf (-2 : ZMod a))).map
        fun k => ((-2) ^ k + ((a : ℤ) - 1) / 3) % a - ((a : ℤ) - 1) / 3) ∧
    (∀ b : ℤ, -(a : ℤ) < 3 * b → 3 * b < 2 * a → b ≠ 0 → 3 * b ≠ a →
      IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)])
        ((List.range (orderOf (-2 : ZMod (a / Int.gcd a b)))).map
          fun k => (b * (-2) ^ k + ((a : ℤ) - 1) / 3) % a - ((a : ℤ) - 1) / 3)) ∧
    ∀ a' t : ℕ, a = t * a' → ∀ c : List ℤ,
      (IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a' : ℤ)]) c ↔
        IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) (c.map ((t : ℤ) * ·)))

/-- **Cyclic vertices of $G(-2n + 1, -2n + a)$ when $a \equiv 1 \pmod 3$.** Let $a$ be an even
natural number with $a \equiv 1 \pmod 3$ and let $m$ be an integer. The digraph
$G(-2n + 1, -2n + a)$ on $\mathbb{Z}$, with an edge $x \to -2x + 1$ and an edge $x \to -2x + a$
for every integer $x$, has a directed walk of positive length from $m$ back to $m$ if and only
if $-(a - 1)/3 < m < 2a/3$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 11
(`integers-2026-A107-thm-11`). -/
theorem_wanted ecsd_type_three_two_cyclic_iff (a : ℕ) (ha : Even a) (ha3 : a % 3 = 1)
    (m : ℤ) :
    Relation.TransGen (ecsdAdj ![-2, -2] ![1, (a : ℤ)]) m m ↔
      -((a : ℤ) - 1) < 3 * m ∧ 3 * m < 2 * a

/-- **Bounds on the cyclic vertices of $G(-2n + 1, -2n + a)$ when $a \equiv 2 \pmod 3$.** Let $a$
be an even integer with $a \equiv 2 \pmod 3$, and let $m$ be an integer such that the digraph
$G(-2n + 1, -2n + a)$ on $\mathbb{Z}$, with an edge $x \to -2x + 1$ and an edge $x \to -2x + a$
for every integer $x$, has a directed walk of positive length from $m$ back to $m$. If $a \ge 2$,
then $-(a - 1)/3 < m < 2a/3$; if $a \le -2$, then $-2(|a| + 1)/3 < m < (|a| + 3)/3$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 12
(`integers-2026-A107-thm-12`). -/
theorem_wanted ecsd_type_three_three_cyclic_bounds (a : ℤ) (ha : Even a) (ha3 : a % 3 = 2)
    (m : ℤ) (hm : Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m) :
    (2 ≤ a → -(a - 1) < 3 * m ∧ 3 * m < 2 * a) ∧
      (a ≤ -2 → -2 * (|a| + 1) < 3 * m ∧ 3 * m < |a| + 3)

/-- **Cyclic vertices of $G(-2n + 1, -2n + a)$ and their residues when $a \equiv 2 \pmod 3$.** Let
$a$ be an even integer with $a \equiv 2 \pmod 3$, and call an integer $m$ cyclic if the digraph
$G(-2n + 1, -2n + a)$ on $\mathbb{Z}$, with an edge $x \to -2x + 1$ and an edge $x \to -2x + a$
for every integer $x$, has a directed walk of positive length from $m$ back to $m$. Then: if
$a \ge 2$, every integer $m$ with $-(a - 1)/3 < m < 2a/3$ is cyclic; if $a \le -2$, every integer
$m$ with $-2(|a| + 1)/3 < m < (|a| + 3)/3$ is cyclic; every residue class modulo $|a - 1|$
contains a cyclic integer; and there are a least cyclic integer $\ell$ and a greatest cyclic
integer $h$ such that $\ell \equiv h \pmod{|a - 1|}$, the list $(\ell, h)$ is a cycle, and any
two distinct cyclic integers that are congruent modulo $|a - 1|$ are $\ell$ and $h$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 13
(`integers-2026-A107-thm-13`). -/
theorem_wanted ecsd_type_three_three_cyclic (a : ℤ) (ha : Even a) (ha3 : a % 3 = 2) :
    (∀ m : ℤ, ((2 ≤ a ∧ -(a - 1) < 3 * m ∧ 3 * m < 2 * a) ∨
        (a ≤ -2 ∧ -2 * (|a| + 1) < 3 * m ∧ 3 * m < |a| + 3)) →
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m) ∧
    (∀ c : ℤ, ∃ m : ℤ,
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m ∧ m ≡ c [ZMOD |a - 1|]) ∧
    ∃ lo hi : ℤ,
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) lo lo ∧
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) hi hi ∧
      (∀ m : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m → lo ≤ m ∧ m ≤ hi) ∧
      lo ≡ hi [ZMOD |a - 1|] ∧
      IsDigraphCycle (ecsdAdj ![-2, -2] ![1, a]) [lo, hi] ∧
      ∀ m m' : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m →
        Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m' m' → m ≡ m' [ZMOD |a - 1|] →
        m ≠ m' → ({m, m'} : Set ℤ) = {lo, hi}

/-- **Digit representations and connected digraphs.** Let $d \ge 2$ be a natural number, let
$D$ be an integer with $|D| = d$, and let $a_1, \dots, a_d$ be integers such that for every
integer $n$ there is exactly one $i$ with $D \mid n - a_i$. Let
$G = G(Dn + a_1, \dots, Dn + a_d)$. Then every integer $z$ can be written as
$z = \sum_{j=0}^{k} b_j D^j$ with $k \in \mathbb{N}$ and digits
$b_0, \dots, b_k \in \{a_1, \dots, a_d\}$ if and only if the underlying undirected graph of $G$
is connected and $0$ lies on a directed cycle of $G$.

The paper also states that the representation is unique; that clause is omitted here.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 14
(`integers-2026-A107-thm-14`). -/
theorem_wanted ecsd_digit_representation_iff (d : ℕ) (hd : 2 ≤ d) (D : ℤ) (hD : |D| = d)
    (a : Fin d → ℤ) (hS : ∀ n : ℤ, ∃! i, D ∣ n - a i) :
    (∀ z : ℤ, ∃ (k : ℕ) (b : ℕ → ℤ), (∀ j ≤ k, ∃ i, b j = a i) ∧
        z = ∑ j ∈ Finset.range (k + 1), b j * D ^ j) ↔
      (∀ m n : ℤ, Relation.EqvGen (ecsdAdj (fun _ => D) a) m n) ∧
        Relation.TransGen (ecsdAdj (fun _ => D) a) 0 0

/-- **Connectivity of $G(-2n + 1, -2n + a)$.** For an even integer $a$, the underlying undirected
graph of $G(-2n + 1, -2n + a)$ is connected iff $a = 1 + 3^m$ or $a = 1 - 3^m$ for some
integer $m \ge 0$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 15
(`integers-2026-A107-thm-15`). -/
theorem_wanted ecsd_one_component_iff (a : ℤ) (ha : Even a) :
    (∀ m n : ℤ, Relation.EqvGen (ecsdAdj ![-2, -2] ![1, a]) m n) ↔
      ∃ m : ℕ, a = 1 + 3 ^ m ∨ a = 1 - 3 ^ m

/-- **Shortest walks to $\pm(a - 1)$ in $G(-2n + 1, -2n + a)$.** Let $m \ge 1$ be an integer and
$a = 1 + 3^m$ or $a = 1 - 3^m$. Then in $G(-2n + 1, -2n + a)$ the least $k \in \mathbb{N}$ such
that $a - 1$ is a $k$-descendant of $0$ (the end of a directed walk of exactly $k$ edges from
$0$) is $3^m$, and the least $k$ such that $-(a - 1)$ is a $k$-descendant of $0$ is also $3^m$.

The paper states this for every $a \notin \{0, 2\}$, which is false: for $a = 6$ the shortest
walk from $0$ to $5$ has $4$ edges. Its proof uses that the cycle through $0$ has $|a - 1|$
edges, which holds when the digraph has a single component.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 16
(`integers-2026-A107-thm-16`). -/
theorem_wanted ecsd_path_length_to_a_sub_one (m : ℕ) (hm : 1 ≤ m) (a : ℤ)
    (ha : a = 1 + 3 ^ m ∨ a = 1 - 3 ^ m) :
    IsLeast {k : ℕ | IsKDescendant (ecsdAdj ![-2, -2] ![1, a]) k 0 (a - 1)} (3 ^ m) ∧
      IsLeast {k : ℕ | IsKDescendant (ecsdAdj ![-2, -2] ![1, a]) k 0 (-(a - 1))} (3 ^ m)

/-- **Degree-2 ECSDs with one component and $0$ on a cycle.** Let $d_1, d_2 \in \{2, -2\}$ and let
$a_1, a_2$ be integers with $a_1 - a_2$ odd, excluding the case $d_1 = d_2 = -2$ with
$|a_1 - a_2| = 1$. Consider the exact covering system digraph $G(d_1 n + a_1, d_2 n + a_2)$, with
an edge $m \to d_i m + a_i$ for every integer $m$ and $i = 1, 2$. It has a single component (any
two integers are joined by a path in its underlying undirected graph) and a directed walk of
positive length from $0$ back to $0$ if and only if one of the following holds: $d_1 = 2$,
$d_2 = -2$, $a_1 = 0$ and $a_2 = \pm 1$; or $d_1 = -2$, $d_2 = 2$, $a_2 = 0$ and $a_1 = \pm 1$;
or $d_1 = d_2 = -2$, $|a_1 - a_2| = 3^m$ for some integer $m \ge 0$, neither $a_1$ nor $a_2$ is
divisible by $3$, and $\max(|a_1|, |a_2|) \le 2|a_1 - a_2| - 1$.

The excluded case behaves differently: $G(-2n + 1, -2n + 2)$ has a single component and the
cycle $(0, 1)$, although $\max(1, 2) = 2 > 2 \cdot 1 - 1$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 17
(`integers-2026-A107-thm-17`). -/
theorem_wanted ecsd_single_component_zero_cyclic_iff (d₁ d₂ a₁ a₂ : ℤ)
    (hd₁ : d₁ = 2 ∨ d₁ = -2) (hd₂ : d₂ = 2 ∨ d₂ = -2) (ha : Odd (a₁ - a₂))
    (hne : ¬ (d₁ = -2 ∧ d₂ = -2 ∧ |a₁ - a₂| = 1)) :
    ((∀ m n : ℤ, Relation.EqvGen (ecsdAdj ![d₁, d₂] ![a₁, a₂]) m n) ∧
        Relation.TransGen (ecsdAdj ![d₁, d₂] ![a₁, a₂]) 0 0) ↔
      (d₁ = 2 ∧ d₂ = -2 ∧ a₁ = 0 ∧ (a₂ = 1 ∨ a₂ = -1)) ∨
        (d₁ = -2 ∧ d₂ = 2 ∧ a₂ = 0 ∧ (a₁ = 1 ∨ a₁ = -1)) ∨
        (d₁ = -2 ∧ d₂ = -2 ∧ (∃ m : ℕ, |a₁ - a₂| = 3 ^ m) ∧ ¬ 3 ∣ a₁ ∧ ¬ 3 ∣ a₂ ∧
          max |a₁| |a₂| ≤ 2 * |a₁ - a₂| - 1)

/-- **Negabinary representations with digits $1$ and $a$.** Let $a \in \mathbb{Z}$. Every integer
$z$ can be written as $z = \sum_{j=0}^{k} b_j (-2)^j$ for some $k \in \mathbb{N}$ and digits
$b_0, \dots, b_k \in \{1, a\}$ if and only if $a = 1 + 3^m$ or $a = 1 - 3^m$ for some integer
$m \ge 0$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Corollary 1
(`integers-2026-A107-cor-1`). -/
theorem_wanted negabinary_digits_one_a_complete_iff (a : ℤ) :
    (∀ z : ℤ, ∃ (k : ℕ) (b : ℕ → ℤ), (∀ j ≤ k, b j = 1 ∨ b j = a) ∧
        z = ∑ j ∈ Finset.range (k + 1), b j * (-2) ^ j) ↔
      ∃ m : ℕ, a = 1 + 3 ^ m ∨ a = 1 - 3 ^ m

/-- **Negabinary representations with two digits.** Let $a_1, a_2 \in \mathbb{Z}$ with
$|a_1 - a_2| \ne 1$. Every integer $z$ can be written as $z = \sum_{j=0}^{k} b_j (-2)^j$ for some
$k \in \mathbb{N}$ and digits $b_0, \dots, b_k \in \{a_1, a_2\}$ if and only if
$|a_1 - a_2| = 3^m$ for some integer $m \ge 0$, neither $a_1$ nor $a_2$ is divisible by $3$, and
$\max\{|a_1|, |a_2|\} \le 2|a_1 - a_2| - 1$.

The hypothesis $|a_1 - a_2| \ne 1$ restricts the printed statement, which fails when
$|a_1 - a_2| = 1$: the digits $\{1, 2\}$ represent every integer, yet $\max\{1, 2\} = 2 > 1$.
The paper's alternative $\{a_1, a_2\} = \{0, \pm 1\}$ lies in the excluded case and is dropped.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Corollary 2
(`integers-2026-A107-cor-2`). -/
theorem_wanted negabinary_two_digits_complete_iff (a₁ a₂ : ℤ) (h : |a₁ - a₂| ≠ 1) :
    (∀ z : ℤ, ∃ (k : ℕ) (b : ℕ → ℤ), (∀ j ≤ k, b j = a₁ ∨ b j = a₂) ∧
        z = ∑ j ∈ Finset.range (k + 1), b j * (-2) ^ j) ↔
      (∃ m : ℕ, |a₁ - a₂| = 3 ^ m) ∧ ¬ 3 ∣ a₁ ∧ ¬ 3 ∣ a₂ ∧
        max |a₁| |a₂| ≤ 2 * |a₁ - a₂| - 1

/-- **Single-component degree-2 ECSDs up to isomorphism.** Let $d_1, d_2 \in \{2, -2\}$ and let
$a_1, a_2$ be integers with $a_1 - a_2$ odd. If the exact covering system digraph
$G(d_1 n + a_1, d_2 n + a_2)$, with an edge $m \to d_i m + a_i$ for every integer $m$ and
$i = 1, 2$, has a single component, that is, any two integers are joined by a path in its
underlying undirected graph, then it is isomorphic as a digraph to $G(2n, -2n + 1)$ or to
$G(-2n + 1, -2n + a)$ for some integer $a$ with $a = 0$, $a = 2$ or $a \equiv 1 \pmod 3$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Proposition 2
(`integers-2026-A107-prop-2`). -/
theorem_wanted ecsd_single_component_relIso (d₁ d₂ a₁ a₂ : ℤ)
    (hd₁ : d₁ = 2 ∨ d₁ = -2) (hd₂ : d₂ = 2 ∨ d₂ = -2) (ha : Odd (a₁ - a₂))
    (h : ∀ m n : ℤ, Relation.EqvGen (ecsdAdj ![d₁, d₂] ![a₁, a₂]) m n) :
    Nonempty (ecsdAdj ![d₁, d₂] ![a₁, a₂] ≃r ecsdAdj ![2, -2] ![0, 1]) ∨
      ∃ a : ℤ, (a = 0 ∨ a = 2 ∨ a % 3 = 1) ∧
        Nonempty (ecsdAdj ![d₁, d₂] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![1, a])

end

end MetaMathlibExt
