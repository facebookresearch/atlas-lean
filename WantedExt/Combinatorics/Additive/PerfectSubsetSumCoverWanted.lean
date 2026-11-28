/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import MathlibExt.Combinatorics.Additive.PerfectCoverCoordinateOrders
public import MathlibExt.Combinatorics.Additive.PerfectCoverPrescribedOddCoordinates
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCoverErase
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCoverInit
public import MathlibExt.Combinatorics.Additive.PerfectSubsetSumCoverOddMultiple

/-!
# Perfect subset-sum covers of abelian groups of order a power of two

Greene and Higgins count sets `S` in an abelian group `G` of order `2^n` whose subset
sums cover every element of `G` exactly once (*perfect covers*), and more generally
colored multisets whose subset sums cover every element exactly `m` times (*perfect
`m`-covers*). A colored multiset is an indexed family `s : ι → G`; its subsets are the
index sets `I : Finset ι`, so repeated values are distinguished. The record text fixes
these notions: a perfect cover of a group of order `2^n` is a set of `n` nonzero elements
with distinct subset sums (Lemma 16), a perfect `m`-cover covers each element `m` times
(Lemmas 5 and 8), and `C(G)` is the number of perfect covers of `G`. The relation `a ∼ b`
("`b` is an odd multiple of `a`") and the operator `𝒯` are taken from the paper's Section 3.
-/

namespace MetaMathlibExt

@[expose] public section

open PerfectSubsetSumCover

/-- **Existence of perfect covers.** Every finite abelian group $G$ of order $2^n$ has a perfect
cover, and every nonzero $x \in G$ lies in some perfect cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 1
(`jis-2025-25.7.8-thm-1`). -/
public theorem_wanted exists_isPerfectCover_mem {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) :
    (∃ S : Finset G, IsPerfectCover S) ∧
      ∀ x : G, x ≠ 0 → ∃ S : Finset G, IsPerfectCover S ∧ x ∈ S

/-- **Number of perfect covers of a cyclic 2-group.** For every $n \ge 0$, the cyclic group
$\mathbb{Z}_{2^n}$ has exactly $2^{n(n-1)/2}$ perfect covers.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 2
(`jis-2025-25.7.8-thm-2`). -/
public theorem_wanted count_zmod_two_pow (n : ℕ) :
    count (ZMod (2 ^ n)) = 2 ^ (n * (n - 1) / 2)

/-- **Perfect covers of a product of two cyclic 2-groups.** Write $C(K)$ for the number of
perfect covers of a group $K$, and $a_{m,n} = C(\mathbb{Z}_{2^m} \oplus \mathbb{Z}_{2^n})$.
For all $m \ge n \ge 1$,
$a_{m,n} = 2^{m+n-1} (a_{m-1,n} + 2 a_{m,n-1}) -
3 \cdot 2^{2m+2n-4} \, a_{m-1,n-1}$.
Moreover, for every $n \ge 0$ there is a polynomial $p$ of degree $n$ with rational coefficients
such that $a_{m,n} = 2^{(m-1)n} \, 2^{m(m-1)/2} \, p(m)$ for all $m \ge n$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 3
(`jis-2025-25.7.8-thm-3`). -/
public theorem_wanted count_zmod_two_pow_prod_recurrence :
    (∀ m n : ℕ, 1 ≤ n → n ≤ m →
      (count (ZMod (2 ^ m) × ZMod (2 ^ n)) : ℤ) =
        2 ^ (m + n - 1) * (count (ZMod (2 ^ (m - 1)) × ZMod (2 ^ n)) +
          2 * count (ZMod (2 ^ m) × ZMod (2 ^ (n - 1)))) -
        3 * 2 ^ (2 * m + 2 * n - 4) * count (ZMod (2 ^ (m - 1)) × ZMod (2 ^ (n - 1)))) ∧
    ∀ n : ℕ, ∃ p : Polynomial ℚ, p.natDegree = n ∧ ∀ m : ℕ, n ≤ m →
      (count (ZMod (2 ^ m) × ZMod (2 ^ n)) : ℚ) =
        2 ^ ((m - 1) * n) * 2 ^ (m * (m - 1) / 2) * p.eval (m : ℚ)

/-- **Perfect covers of $(\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n}$.** Write $C(K)$ for the number
of perfect covers of a group $K$, and for natural numbers $m$ and $n$ let
$b_{m,n} = C((\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n})$. Then:
for every $m \ge 0$, $C((\mathbb{Z}_2)^m) \cdot m! = \prod_{i=0}^{m-1} (2^m - 2^i)$;
for all $m, n \ge 1$, writing $B_{m,k} = 2^m \prod_{i=0}^{k-1} (2^m - 2^i) / (k+1)!$ for
$1 \le k \le m$, we have $b_{m,n} = 2^{m+n-1} b_{m,n-1} +
\sum_{k=1}^{m} B_{m,k} \, 2^{k(m-k)} \, 2^{(k+1)(n-1)} \, b_{m-k,n-1}$;
and for every $m \ge 0$ there is a polynomial $q$ of degree $m$ with rational coefficients such
that $b_{m,n} = 2^{m(n-1)} \, 2^{n(n-1)/2} \, q(n)$ for all $n \ge 0$, where the power
$2^{m(n-1)}$ has an integer exponent (it is $2^{-m}$ at $n = 0$).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 4
(`jis-2025-25.7.8-thm-4`). -/
public theorem_wanted count_elementary_prod_zmod_two_pow :
    (∀ m : ℕ, count (Fin m → ZMod 2) * m.factorial =
      ∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      (count ((Fin m → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
        2 ^ (m + n - 1) * count ((Fin m → ZMod 2) × ZMod (2 ^ (n - 1))) +
          ∑ k ∈ Finset.Icc 1 m,
            (2 ^ m * ∏ i ∈ Finset.range k, ((2 : ℚ) ^ m - 2 ^ i)) / (k + 1).factorial *
              2 ^ (k * (m - k)) * 2 ^ ((k + 1) * (n - 1)) *
              count ((Fin (m - k) → ZMod 2) × ZMod (2 ^ (n - 1)))) ∧
    ∀ m : ℕ, ∃ q : Polynomial ℚ, q.natDegree = m ∧ ∀ n : ℕ,
      (count ((Fin m → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
        (2 : ℚ) ^ ((m : ℤ) * ((n : ℤ) - 1)) * 2 ^ (n * (n - 1) / 2) * q.eval (n : ℚ)

/-- **Perfect covers of a cyclic 2-group times a cyclic group of order 2, 4 or 8.** Write
$C(K)$ for the number of perfect covers of a group $K$. For every $n \ge 0$,
$C(\mathbb{Z}_{2^n} \oplus \mathbb{Z}_2) = 2^{n-1} \, 2^{n(n-1)/2} \, (n + 2)$, where $2^{n-1}$
is an integer power of $2$ (equal to $1/2$ at $n = 0$). For every $n \ge 1$,
$C(\mathbb{Z}_{2^n} \oplus \mathbb{Z}_4) = 2^{2n-2} \, 2^{n(n-1)/2} \, (n^2 + 11n + 4)$.
For every $n \ge 2$,
$C(\mathbb{Z}_{2^n} \oplus \mathbb{Z}_8) =
2^{3n-3} \, 2^{n(n-1)/2} \, (4n^3 + 108n^2 + 512n - 384)/3$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 25
(`jis-2025-25.7.8-cor-25`). The record gives no range; the second identity fails at
`n = 0` (`C(ℤ₄) = 2`, formula `1`) and the third at `n = 0, 1` (`C(ℤ₈) = 8`, formula `-16`;
`C(ℤ₂ ⊕ ℤ₈) = 160`, formula `80`), matching Theorem 3's range `m ≥ n`. -/
public theorem_wanted count_zmod_two_pow_prod_small_special :
    (∀ n : ℕ, (count (ZMod (2 ^ n) × ZMod 2) : ℚ) =
      (2 : ℚ) ^ ((n : ℤ) - 1) * 2 ^ (n * (n - 1) / 2) * ((n : ℚ) + 2)) ∧
    (∀ n : ℕ, 1 ≤ n → (count (ZMod (2 ^ n) × ZMod 4) : ℚ) =
      2 ^ (2 * n - 2) * 2 ^ (n * (n - 1) / 2) * ((n : ℚ) ^ 2 + 11 * n + 4)) ∧
    ∀ n : ℕ, 2 ≤ n → (count (ZMod (2 ^ n) × ZMod 8) : ℚ) =
      2 ^ (3 * n - 3) * 2 ^ (n * (n - 1) / 2) *
        ((4 * (n : ℚ) ^ 3 + 108 * n ^ 2 + 512 * n - 384) / 3)

/-- **Perfect covers of an elementary abelian group of order 4 or 8 times a cyclic 2-group.**
Write $C(K)$ for the number of perfect covers of a group $K$. For every $n \ge 0$,
$C((\mathbb{Z}_2)^2 \oplus \mathbb{Z}_{2^n}) = 2^{2n-2} \, 2^{n(n-1)/2} \, (3n^2 + 13n + 12)$
and
$C((\mathbb{Z}_2)^3 \oplus \mathbb{Z}_{2^n}) =
2^{3n-3} \, 2^{n(n-1)/2} \, (28n^3 + 196n^2 + 392n + 224)$,
where $2^{2n-2}$ and $2^{3n-3}$ are integer powers of $2$ (fractional at $n = 0$).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 26
(`jis-2025-25.7.8-cor-26`). The record's third identity, for `(ℤ₂)^4 ⊕ ℤ_{2^n}`, is
omitted: it fails as printed at `n = 1` (`C((ℤ₂)^5) = 83328`, formula `72328`). -/
public theorem_wanted count_elementary_two_three_prod_zmod :
    (∀ n : ℕ, (count ((Fin 2 → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
      (2 : ℚ) ^ (2 * (n : ℤ) - 2) * 2 ^ (n * (n - 1) / 2) * (3 * (n : ℚ) ^ 2 + 13 * n + 12)) ∧
    ∀ n : ℕ, (count ((Fin 3 → ZMod 2) × ZMod (2 ^ n)) : ℚ) =
      (2 : ℚ) ^ (3 * (n : ℤ) - 3) * 2 ^ (n * (n - 1) / 2) *
        (28 * (n : ℚ) ^ 3 + 196 * n ^ 2 + 392 * n + 224)

/-- **Odd multiples and replacement in perfect covers.** Let $G$ be a finite abelian group of order
$2^n$ and let $a, b \in G$ be nonzero. Then $b = (2j+1)a$ for some integer $j$ if and only if, for
every perfect cover $S$ of $G$ with $a \in S$, the set $(S \setminus \{a\}) \cup \{b\}$ is again a
perfect cover of $G$. If moreover $a \ne b$, then $b = (2j+1)a$ for some integer $j$ if and only if
no perfect cover of $G$ contains both $a$ and $b$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 10
(`jis-2025-25.7.8-thm-10`). `a, b ≠ 0` added and `a ≠ b` added for (3): for `a = 0, b ≠ 0`
conditions (2) and (3) hold vacuously while (1) fails, and for `a = b ≠ 0` condition (3)
fails (Theorem 1 puts `a` in a perfect cover) while (1) holds. -/
public theorem_wanted oddMultiple_iff_perfectCover_replace {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) {a b : G} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    ((∃ j : ℤ, b = (2 * j + 1) • a) ↔
      ∀ S : Finset G, IsPerfectCover S → a ∈ S → IsPerfectCover (insert b (S.erase a))) ∧
    (a ≠ b → ((∃ j : ℤ, b = (2 * j + 1) • a) ↔
      ∀ S : Finset G, IsPerfectCover S → ¬ (a ∈ S ∧ b ∈ S)))

/-- **Which families are perfect $m$-covers of $\mathbb{Z}_{2^n}$.** Let $s = (s_i)_{i \in \iota}$
be a family in $\mathbb{Z}_{2^n}$ indexed by a finite type $\iota$ (a colored multiset). Then $s$
is a perfect $m$-cover of $\mathbb{Z}_{2^n}$ for some $m$ if and only if for every $j$ with
$1 \le j \le n$ some $s_i$ has additive order $2^j$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 12
(`jis-2025-25.7.8-thm-12`). The multiplicity `m` is existentially quantified. -/
public theorem_wanted exists_isPerfectMCover_zmod_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → ZMod (2 ^ n)) :
    (∃ m, IsPerfectMCover m s) ↔
      ∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ i, addOrderOf (s i) = 2 ^ j

/-- **Perfect $m$-covers of $\mathbb{Z}_{2^n}$ contain perfect covers.** Let
$s = (s_i)_{i \in \iota}$ be a family in $\mathbb{Z}_{2^n}$ indexed by a finite type $\iota$. If
$s$ is a perfect $m$-cover of $\mathbb{Z}_{2^n}$, then there is a finite set $T \subseteq \iota$
such that the subfamily $(s_i)_{i \in T}$ is a perfect $1$-cover of $\mathbb{Z}_{2^n}$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 13
(`jis-2025-25.7.8-cor-13`). -/
public theorem_wanted exists_perfectCover_subfamily_zmod {n m : ℕ} {ι : Type*} [Fintype ι]
    {s : ι → ZMod (2 ^ n)} (hs : IsPerfectMCover m s) :
    ∃ T : Finset ι, IsPerfectMCover 1 (fun i : T => s i)

/-- **Odd combinations of disjoint parts of a perfect cover.** Let $G$ be an abelian group of
order $2^n$ and $S$ a perfect cover of $G$. For a finite $A \subseteq G$, let $\mathcal{T}(A)$ be
the set of combinations $\sum_{x \in A} c_x x$ in which every integer coefficient $c_x$ is $0$
or odd. Then: (a) for disjoint $A, B \subseteq S$, $\mathcal{T}(A) \cap \mathcal{T}(B) = \{0\}$;
(b) if $A \subseteq S$ and $s \in S \setminus A$, then $s \notin \mathcal{T}(A)$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 15 (a), (b)
(`jis-2025-25.7.8-thm-15`). -/
public theorem_wanted oddCombinations_inter_of_isPerfectCover {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) {S : Finset G}
    (hS : IsPerfectCover S) :
    (∀ A B : Finset G, A ⊆ S → B ⊆ S → Disjoint A B →
      oddCombinations A ∩ oddCombinations B = {0}) ∧
    ∀ A : Finset G, A ⊆ S → ∀ s ∈ S, s ∉ A → s ∉ oddCombinations A

/-- **Perfect covers containing a perfect cover of a subgroup.** Let $G$ be an abelian group of
order $2^n$ and $H$ a subgroup of order $2^m$. Then the number of perfect covers of $G$ that
contain a perfect cover of $H$ is $2^{m(n-m)} \cdot C(G/H) \cdot C(H)$, where $C(K)$ denotes the
number of perfect covers of a group $K$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 17
(`jis-2025-25.7.8-lem-17`). -/
public theorem_wanted card_perfectCover_superset_subgroup {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n m : ℕ} (hG : Fintype.card G = 2 ^ n) (H : AddSubgroup G)
    (hH : Nat.card H = 2 ^ m) [DecidableEq (G ⧸ H)] :
    Nat.card {S : Finset G // IsPerfectCover S ∧
        ∃ A : Finset H, IsPerfectCover A ∧ A.map (Function.Embedding.subtype _) ⊆ S} =
      2 ^ (m * (n - m)) * count (G ⧸ H) * count H

/-- **Elements of order two among odd combinations of part of a perfect cover.** Let $G$ be an
abelian group of order $2^n$, let $S$ be a perfect cover of $G$, and let $A \subseteq S$ contain
no element of order $2$. Let $\mathcal{T}(A)$ be the set of combinations $\sum_{x \in A} c_x x$ in
which every integer coefficient $c_x$ is $0$ or odd. Then $\mathcal{T}(A)$ does not contain
exactly one element of order $2$: it contains none or at least two.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 18
(`jis-2025-25.7.8-lem-18`). "No elements of order `2`, or at least two" is stated as "not
exactly one". -/
public theorem_wanted not_existsUnique_addOrderOf_two_mem_oddCombinations {G : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n)
    {S A : Finset G} (hS : IsPerfectCover S) (hA : A ⊆ S) (hA2 : ∀ x ∈ A, addOrderOf x ≠ 2) :
    ¬ ∃! h : G, h ∈ oddCombinations A ∧ addOrderOf h = 2

/-- **Elements of order $2$ in perfect covers of $\mathbb{Z}_{2^m} \oplus \mathbb{Z}_{2^n}$.**
Let $m, n$ be natural numbers with $m + n > 0$. Every perfect cover of
$\mathbb{Z}_{2^m} \oplus \mathbb{Z}_{2^n}$ contains an element of order $2$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 19
(`jis-2025-25.7.8-lem-19`). Hypothesis `0 < m + n` added: the trivial group's perfect
cover is empty. -/
public theorem_wanted exists_addOrderOf_eq_two_of_isPerfectCover {m n : ℕ} (hmn : 0 < m + n)
    {S : Finset (ZMod (2 ^ m) × ZMod (2 ^ n))} (hS : IsPerfectCover S) :
    ∃ x ∈ S, addOrderOf x = 2

/-- **Spans of the odd and even entries of a perfect cover.** Let $m$, $n$ and $k$ be natural
numbers with $k + 1 \le m + n$, and let $s = (s_1, \dots, s_{m+n})$, $s_i = (x_i, y_i)$, be a
family in $(\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n}$ that is a perfect $1$-cover: every element of
the group is the sum of the $s_i$ over exactly one set of indices. Suppose that $y_i$, read as an
integer in $\{0, \dots, 2^n - 1\}$, is odd exactly when $i \le k + 1$. Let $U$ be the
$\mathbb{Z}_2$-span of $x_1 + x_2, \dots, x_1 + x_{k+1}$ and $V$ the $\mathbb{Z}_2$-span of
$x_{k+2}, \dots, x_{m+n}$ in $(\mathbb{Z}_2)^m$. Then $\dim U = k$, $\dim V = m - k$,
$U \cap V = 0$ and $U + V = (\mathbb{Z}_2)^m$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 23
(`jis-2025-25.7.8-lem-23`). Indices are `0`-based (`i < k + 1` are the odd ones, and
`k + 1 ≤ m + n` makes `y_1, …, y_{k+1}` exist); the perfect cover is an indexed family
(perfect covers have distinct entries); `(ℤ₂)^m = U ⊕ V` is stated as `U ⊔ V = ⊤`. -/
public theorem_wanted perfectCover_odd_even_span {m n k : ℕ} (hk : k + 1 ≤ m + n)
    {s : Fin (m + n) → (Fin m → ZMod 2) × ZMod (2 ^ n)} (hs : IsPerfectMCover 1 s)
    (hodd : ∀ i : Fin (m + n), Odd (s i).2.val ↔ i.val < k + 1) :
    let U := Submodule.span (ZMod 2)
      {v | ∃ i : Fin (m + n), 1 ≤ i.val ∧ i.val < k + 1 ∧ v = (s ⟨0, by omega⟩).1 + (s i).1}
    let V := Submodule.span (ZMod 2) {v | ∃ i : Fin (m + n), k + 1 ≤ i.val ∧ v = (s i).1}
    Module.finrank (ZMod 2) U = k ∧ Module.finrank (ZMod 2) V = m - k ∧ U ⊓ V = ⊥ ∧ U ⊔ V = ⊤

/-- **The even tail of a perfect cover.** Let $s = (s_1, \dots, s_{m+n})$, $s_i = (x_i, y_i)$, be a
family in $(\mathbb{Z}_2)^m \oplus \mathbb{Z}_{2^n}$ that is a perfect $1$-cover: every element of
the group is the sum of the $s_i$ over exactly one set of indices. Let $k + 1 \le m + n$ and suppose
that $y_i$, read as an integer in $\{0, \dots, 2^n - 1\}$, is odd exactly when $i \le k + 1$. Let
$V$ be the $\mathbb{Z}_2$-span of $x_{k+2}, \dots, x_{m+n}$ in $(\mathbb{Z}_2)^m$. Then every
$(x, y)$ with $x \in V$ and $y$ even (again read in $\{0, \dots, 2^n - 1\}$) is the sum of the
$s_i$ over exactly one set of indices taken from $\{k+2, \dots, m+n\}$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 24
(`jis-2025-25.7.8-lem-24`). The family's elements lie in `V ⊕ 2ℤ_{2^n}` by hypothesis and
by definition of `V`; only the covering statement is stated. -/
public theorem_wanted perfectCover_even_tail_coverCount {m n k : ℕ} (hk : k + 1 ≤ m + n)
    {s : Fin (m + n) → (Fin m → ZMod 2) × ZMod (2 ^ n)} (hs : IsPerfectMCover 1 s)
    (hodd : ∀ i : Fin (m + n), Odd (s i).2.val ↔ i.val < k + 1)
    (g : (Fin m → ZMod 2) × ZMod (2 ^ n))
    (hgV : g.1 ∈ Submodule.span (ZMod 2) {v | ∃ i : Fin (m + n), k + 1 ≤ i.val ∧ v = (s i).1})
    (hg2 : Even g.2.val) :
    coverCount (fun i : {i : Fin (m + n) // k + 1 ≤ i.val} => s i) g = 1

end

end MetaMathlibExt
