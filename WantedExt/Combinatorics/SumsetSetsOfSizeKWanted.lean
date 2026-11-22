/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Order.Group.Defs

/-!
# The sumset of sets of size `k`

Statements from Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26
(2026), Article A31.

The definitions of `R_G(h, k)` and of the trivial elements of `hA` are taken from the
arXiv version of the paper (arXiv:2505.07679v2, Section 1, Notation before
Definition 1.8 and Definition 1.8).  Throughout, `R_G(h, k)` is written out as the set
of cardinalities `(h • A).card` of `k`-element finsets `A`, and a `k`-element set
`a 0 < a 1 < ⋯ < a (k - 1)` is given by a function `a : ℕ → G` restricted to
`Finset.range k`.
-/

open scoped Pointwise

namespace MetaMathlibExt

@[expose] public section

/-- **Trivial elements of an $h$-fold sumset.** Let $G$ be an additive commutative monoid, let
$h, k \in \mathbb{N}$ and let $a \colon \mathbb{N} \to G$ list the set
$A = \{a_0, a_1, \dots, a_{k-1}\}$; write $n x$ for the $n$-fold sum $x + \dots + x$. The
trivial elements of the $h$-fold sumset $hA$ form the finite set that is empty when $k = 0$ and
otherwise consists of $h a_0$ together with the sums $(h - i) a_j + i a_{j+1}$ for all natural
numbers $i \le h$ and $j$ with $j + 1 < k$. An element of $hA$ that is not trivial is called
nontrivial.

These are the sums obtained by moving one summand at a time from each element to the next.
When $k \ge 1$ and $a_0 < a_1 < \dots < a_{k-1}$ in a linearly ordered additive group (the
paper's setting) they form an increasing list of $hk - h + 1$ distinct sums; for an arbitrary
$a$ they may coincide (for example $a = 0$ and $h = k = 2$ give a single element). The sum
$h a_0$ is listed separately so that for $k = 1$ the single sum $h a_0$ is trivial, as in the
paper's list.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial and nontrivial elements (arXiv:2505.07679v2,
Definition 1.8). -/
public def sumsetTrivialElements {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h k : ℕ) (a : ℕ → G) : Finset G :=
  if k = 0 then ∅
  else insert (h • a 0) ((Finset.range (k - 1) ×ˢ Finset.range (h + 1)).image
    fun p => (h - p.2) • a p.1 + p.2 • a (p.1 + 1))

/-- **No trivial elements for $k = 0$.** Let $G$ be an additive commutative monoid, $h$ a natural
number and $a \colon \mathbb{N} \to G$. For $k = 0$, when $\{a_0, \dots, a_{k-1}\}$ is the empty
set, the set of trivial elements of its $h$-fold sumset is empty.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem sumsetTrivialElements_zero {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h : ℕ) (a : ℕ → G) : sumsetTrivialElements h 0 a = ∅ := by
  simp [sumsetTrivialElements]

/-- **Trivial elements of a one-element set.** Let $G$ be an additive commutative monoid, $h$ a
natural number and $a \colon \mathbb{N} \to G$. For $k = 1$, when $\{a_0, \dots, a_{k-1}\}$ is
the one-element set $\{a_0\}$, the set of trivial elements of its $h$-fold sumset is exactly
$\{h a_0\}$, where $h a_0 = a_0 + \dots + a_0$ is the $h$-fold sum of $a_0$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem sumsetTrivialElements_one {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (h : ℕ) (a : ℕ → G) : sumsetTrivialElements h 1 a = {h • a 0} := by
  simp [sumsetTrivialElements]

/-- **Adjacent sums are trivial elements.** Let $G$ be an additive commutative monoid,
$a_0, a_1, \ldots$ a sequence in $G$, and $h, k, i, j$ natural numbers with $j + 1 < k$ and
$i \le h$. Then $(h - i)a_j + i a_{j+1}$ is a trivial element of the $h$-fold sumset of
$a_0, \ldots, a_{k-1}$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem adjacent_sum_mem_sumsetTrivialElements {G : Type*} [AddCommMonoid G]
    [DecidableEq G] {h k i j : ℕ} (a : ℕ → G) (hj : j + 1 < k) (hi : i ≤ h) :
    (h - i) • a j + i • a (j + 1) ∈ sumsetTrivialElements h k a := by
  unfold sumsetTrivialElements
  simp only [show k ≠ 0 by omega, ↓reduceIte]
  refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(j, i), ?_, rfl⟩)
  simp only [Finset.mem_product, Finset.mem_range]
  omega

/-- **Characterization of the trivial elements.** Let $G$ be an additive commutative monoid,
$a_0, a_1, \ldots$ a sequence in $G$, and $h, k$ natural numbers. An element $x \in G$ is a
trivial element of the $h$-fold sumset of $a_0, \ldots, a_{k-1}$ if and only if either $k > 0$
and $x = h a_0$, or $x = (h - i)a_j + i a_{j+1}$ for some natural numbers $j$ and $i$ with
$j + 1 < k$ and $i \le h$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, definition of trivial elements (arXiv:2505.07679v2, Definition 1.8). -/
public theorem mem_sumsetTrivialElements_iff {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {h k : ℕ} (a : ℕ → G) (x : G) :
    x ∈ sumsetTrivialElements h k a ↔
      (0 < k ∧ x = h • a 0) ∨
        ∃ j i : ℕ, j + 1 < k ∧ i ≤ h ∧ x = (h - i) • a j + i • a (j + 1) := by
  unfold sumsetTrivialElements
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  simp only [show k ≠ 0 by omega, ↓reduceIte]
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_product, Finset.mem_range,
    Prod.exists]
  constructor
  · rintro (hx | ⟨j, i, ⟨hj, hi⟩, rfl⟩)
    · exact Or.inl ⟨hk, hx⟩
    · exact Or.inr ⟨j, i, by omega, by omega, rfl⟩
  · rintro (⟨-, hx⟩ | ⟨j, i, hj, hi, rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨j, i, ⟨by omega, by omega⟩, rfl⟩

/-- **Dropping the largest element keeps nontrivial sums nontrivial.** Let $G$ be a linearly
ordered additive commutative group, let $h$ and $k > 1$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $a_0 < a_1 < \cdots < a_{k-1}$. Put
$A = \{a_0, \ldots, a_{k-1}\}$ and $B = \{a_0, \ldots, a_{k-2}\}$, and write $hX$ for the
$h$-fold sumset of a set $X$, the set of sums of $h$ elements of $X$. Then $hB \subseteq hA$,
and every element of $hB$ that is not a trivial element of the $h$-fold sumset of
$a_0, \ldots, a_{k-2}$ is not a trivial element of the $h$-fold sumset of $a_0, \ldots, a_{k-1}$.

The paper takes $h > 1$; the statement holds for every $h$ (for $h = 0$ there are no
nontrivial elements).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Lemma 1 (`integers-2026-A31-lem-1`; arXiv:2505.07679v2, Lemma 3.2). -/
public theorem_wanted nsmul_sumset_erase_max_nontrivial
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 1 < k) (a : ℕ → G) (ha : ∀ i, i + 1 < k → a i < a (i + 1)) :
    h • (Finset.range (k - 1)).image a ⊆ h • (Finset.range k).image a ∧
      ∀ c ∈ h • (Finset.range (k - 1)).image a,
        c ∉ sumsetTrivialElements h (k - 1) a → c ∉ sumsetTrivialElements h k a

/-- **Many nontrivial sums when the last gap is not a multiple of the previous one.** Let $G$ be
a linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-3}$. Suppose that
$a_{k-2} = a_{k-3} + b$ and $a_{k-1} = a_{k-3} + b + c$, where $b, c \in G$ satisfy $b > 0$,
$c > 0$ and $c \ne db$ for every integer $d \ge 1$. Then at least $h - 1$ elements of the
$h$-fold sumset $h\{a_0, \ldots, a_{k-1}\}$ (the set of sums of $h$ elements of
$\{a_0, \ldots, a_{k-1}\}$) are not trivial elements of the $h$-fold sumset of
$a_0, \ldots, a_{k-1}$.

The paper takes $h > 1$; the bound is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 1 (`integers-2026-A31-thm-1`; arXiv:2505.07679v2,
Theorem 3.3). -/
public theorem_wanted nontrivial_sumset_card_of_last_gap_ne_nsmul
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 ≤ k - 3 → a i < a (i + 1)) (b c : G) (hb : 0 < b) (hc : 0 < c)
    (hb' : a (k - 2) = a (k - 3) + b) (hc' : a (k - 1) = a (k - 3) + b + c)
    (hcb : ∀ d : ℕ, 1 ≤ d → c ≠ d • b) :
    h - 1 ≤ (h • (Finset.range k).image a \ sumsetTrivialElements h k a).card

/-- **Many nontrivial sums when the last gap is a proper multiple of the previous one.** Let $G$
be a linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and
let $a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-3}$. Suppose
that $a_{k-2} = a_{k-3} + b$ and $a_{k-1} = a_{k-3} + b + db$, where $b \in G$ satisfies
$b > 0$ and $d > 1$ is an integer. Then at least $h - 1$ elements of the $h$-fold sumset
$h\{a_0, \ldots, a_{k-1}\}$ (the set of sums of $h$ elements of $\{a_0, \ldots, a_{k-1}\}$)
are not trivial elements of the $h$-fold sumset of $a_0, \ldots, a_{k-1}$.

The paper's last gap $c$ is written as $db$ (its positivity follows). The paper takes $h > 1$;
the bound is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 2 (`integers-2026-A31-thm-2`; arXiv:2505.07679v2,
Theorem 3.4). -/
public theorem_wanted nontrivial_sumset_card_of_last_gap_eq_nsmul
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 ≤ k - 3 → a i < a (i + 1)) (b : G) (hb : 0 < b) (d : ℕ) (hd : 1 < d)
    (hb' : a (k - 2) = a (k - 3) + b) (hc' : a (k - 1) = a (k - 3) + b + d • b) :
    h - 1 ≤ (h • (Finset.range k).image a \ sumsetTrivialElements h k a).card

/-- **Equal last two gaps: an arithmetic progression or many nontrivial sums.** Let $G$ be a
linearly ordered additive commutative group, let $h$ and $k \ge 4$ be natural numbers, and let
$a_0, a_1, \ldots$ be a sequence in $G$ with $0 = a_0 < a_1 < \cdots < a_{k-1}$ and
$a_{k-1} - a_{k-2} = a_{k-2} - a_{k-3}$. Then either $a_i = i a_1$ for every $i < k$, or at
least $h - 1$ elements of the $h$-fold sumset $hB$ of $B = \{a_0, \ldots, a_{k-2}\}$ (the set
of sums of $h$ elements of $B$) are not trivial elements of the $h$-fold sumset of
$a_0, \ldots, a_{k-2}$.

The gap hypothesis is the paper's $b_{k-2} = b_{k-3}$, where $b_j = a_{j+1} - a_j$ for
$j \ge 1$. The paper takes $h > 1$; the second alternative is vacuous for $h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 3 (`integers-2026-A31-thm-3`; arXiv:2505.07679v2,
Theorem 3.5). -/
public theorem_wanted arithProg_or_nontrivial_sumset_card_of_last_gaps_eq
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (h k : ℕ) (hk : 4 ≤ k) (a : ℕ → G) (ha0 : a 0 = 0)
    (ha : ∀ i, i + 1 < k → a i < a (i + 1))
    (hgap : a (k - 1) - a (k - 2) = a (k - 2) - a (k - 3)) :
    (∀ i < k, a i = i • a 1) ∨
      h - 1 ≤ (h • (Finset.range (k - 1)).image a \
        sumsetTrivialElements h (k - 1) a).card

/-- **A gap in the possible sumset sizes.** Let $G$ be a torsion-free additive commutative
group and let $h$ and $k \ge 4$ be natural numbers. For every $k$-element set $A \subseteq G$,
the $h$-fold sumset $hA$ (the set of sums of $h$ elements of $A$) does not satisfy
$hk - h + 2 \le |hA| \le hk - 1$.

Equivalently, writing $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets
$A \subseteq G$, $R_G(h, k) \cap [hk - h + 2, hk - 1] = \emptyset$. The interval is empty for
$h \le 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 4 (`integers-2026-A31-thm-4`; arXiv:2505.07679v2,
Theorem 3.6). -/
public theorem_wanted card_nsmul_notMem_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (A : Finset G) (hA : A.card = k) :
    (h • A).card ∉ Set.Icc (h * k - h + 2) (h * k - 1)

/-- **Sumset sizes between $hk - h + 1$ and $hk$.** Let $G$ be a nontrivial torsion-free
additive commutative group and let $h \ge 1$ and $k \ge 4$ be natural numbers. For a finite
set $A \subseteq G$ write $hA$ for its $h$-fold sumset, the set of sums of $h$ elements of $A$,
and write $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets $A \subseteq G$. Then
$R_G(h, k) \cap [hk - h + 1, hk] = \{hk - h + 1, hk\}$.

The hypotheses that $G$ is nontrivial (otherwise there is no $k$-element set and
$R_G(h, k)$ is empty) and that $h \ge 1$ (for $h = 0$ the interval $[1, 0]$ is empty while
the right side is $\{1, 0\}$) are added. The arXiv version states only $hk \in R_G(h, k)$
(Corollary 3.8); the rest combines Theorem 4 with the arithmetic-progression size
$hk - h + 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Corollary 1 (`integers-2026-A31-cor-1`). -/
public theorem_wanted sumsetSizes_inter_Icc_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [Nontrivial G] [DecidableEq G]
    (h k : ℕ) (hk : 4 ≤ k) (hh : 1 ≤ h) :
    {n : ℕ | ∃ A : Finset G, A.card = k ∧ (h • A).card = n} ∩
        Set.Icc (h * k - h + 1) (h * k) = {h * k - h + 1, h * k}

/-- **Sumset of an arithmetic progression with its second-to-last term removed.** Let $G$ be a
linearly ordered additive commutative group, let $a \in G$ with $a > 0$, and let $k \ge 3$ and
$h \ge 1$ be natural numbers. The set $A = \{0, a, 2a, \ldots, (k - 2)a, ka\}$, obtained from
$\{0, a, 2a, \ldots, ka\}$ by removing $(k - 1)a$, has $|hA| = hk$, where $hA$ is the $h$-fold
sumset of $A$, the set of sums of $h$ elements of $A$.

The paper leaves $h$ unquantified; $h \ge 1$ is needed, since $|0A| = 1$.

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 5 (`integers-2026-A31-thm-5`). -/
public theorem_wanted card_nsmul_arithProg_skip_penultimate
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (a : G) (ha : 0 < a) (k h : ℕ) (hk : 3 ≤ k) (hh : 1 ≤ h) :
    (h • insert (k • a) ((Finset.range (k - 1)).image fun i => i • a)).card = h * k


/-- **Rajagopal's family of missing sumset sizes.** Let $G$ be a torsion-free additive
commutative group and let $h$, $k$ and $\ell$ be natural numbers with $\ell + 3 \le \min(h, k)$.
For every $k$-element set $A \subseteq G$, the $h$-fold sumset $hA$ (the set of sums of $h$
elements of $A$) does not satisfy
$hk - h + 2 + \ell h \le |hA| \le hk - h + 1 + \ell h + (h - 2 - \ell)$.

Equivalently, writing $R_G(h, k)$ for the set of sizes $|hA|$ of $k$-element sets
$A \subseteq G$, $R_G(h, k)$ misses the interval
$[hk - h + 2 + \ell h, hk - h + 1 + \ell h + (h - 2 - \ell)]$ for each
$0 \le \ell \le \min(h, k) - 3$, stated here one $\ell$ at a time. The journal statement does
not name the group; torsion-freeness is the setting of Theorem 4 and Corollary 1, which this
generalizes ($\ell = 0$ is Theorem 4, here also for $k = 3$).

Source: Vincent Schinina, *On the Sumset of Sets of Size k*, INTEGERS 26 (2026),
Article A31, Theorem 6 (`integers-2026-A31-thm-6`, journal version; credited to Rajagopal,
Theorem 1.3). -/
public theorem_wanted card_nsmul_notMem_Icc_add_mul_of_isAddTorsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (h k ℓ : ℕ) (hℓ : ℓ + 3 ≤ min h k) (A : Finset G) (hA : A.card = k) :
    (h • A).card ∉
      Set.Icc (h * k - h + 1 + ℓ * h + 1) (h * k - h + 1 + ℓ * h + (h - 2 - ℓ))

end

end MetaMathlibExt
