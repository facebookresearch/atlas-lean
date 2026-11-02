/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Interval.Finset.Fin

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

namespace PerfectSubsetSumCover

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- **Cover count.** Let $G$ be an abelian group, $s = (s_i)_{i \in \iota}$ a family in $G$
indexed by a finite type $\iota$ (a colored multiset), and $g \in G$. The cover count of $g$ by
$s$ is the number of index sets $I \subseteq \iota$ with $\sum_{i \in I} s_i = g$: the number of
times $s$ covers $g$ by its subset sums (the empty set covers $0$).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (subset sums,
"covered `m` times", Lemma 8). -/
def coverCount {ι : Type*} [Fintype ι] (s : ι → G) (g : G) : ℕ :=
  (Finset.univ.filter fun I : Finset ι => ∑ i ∈ I, s i = g).card

/-- **Perfect $m$-cover.** Let $G$ be an abelian group, $m$ a natural number and
$s = (s_i)_{i \in \iota}$ a family of elements of $G$ indexed by a finite set $\iota$ (a colored
multiset: repeated values count separately). The family $s$ is a perfect $m$-cover of $G$ when
every $g \in G$ equals $\sum_{i \in I} s_i$ for exactly $m$ subsets $I \subseteq \iota$ (the
empty subset has sum $0$).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (perfect
`m`-covers, Lemmas 5 and 8). -/
def IsPerfectMCover {ι : Type*} [Fintype ι] (m : ℕ) (s : ι → G) : Prop :=
  ∀ g, coverCount s g = m

instance {ι : Type*} [Fintype ι] [Fintype G] (m : ℕ) (s : ι → G) :
    Decidable (IsPerfectMCover m s) := by
  unfold IsPerfectMCover; infer_instance

/-- **Perfect cover.** Let $G$ be an abelian group. A finite set $S \subseteq G$ is a perfect cover
of $G$ when every element of $G$ is the sum of exactly one subset of $S$ (the empty subset has
sum $0$); that is, the family of the elements of $S$ is a perfect $1$-cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (perfect covers,
Lemma 16). -/
def IsPerfectCover (S : Finset G) : Prop :=
  IsPerfectMCover 1 (fun x : S => (x : G))

instance [Fintype G] (S : Finset G) : Decidable (IsPerfectCover S) := by
  unfold IsPerfectCover; infer_instance

/-- **Number of perfect covers.** For an abelian group $G$, $C(G)$ is the number of perfect
covers of $G$: finite subsets $S \subseteq G$ such that every element of $G$ is the sum of
exactly one subset of $S$ (the empty subset has sum $0$).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (`C(G)`). -/
noncomputable def count (G : Type*) [AddCommGroup G] [DecidableEq G] : ℕ :=
  Nat.card {S : Finset G // IsPerfectCover S}

/-- **Perfect cover count as a finset cardinality.** For a finite abelian group $G$, the number
$C(G)$ of perfect covers of $G$ equals the number of elements of the finite set of all subsets of
$G$ that are perfect covers.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (`C(G)`). -/
theorem count_eq_card_filter [Fintype G] :
    count G = (Finset.univ.filter fun S : Finset G => IsPerfectCover S).card := by
  rw [count, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Small values of the perfect cover count.** Writing $C(K)$ for the number of perfect covers
of a group $K$, we have $C(\mathbb{Z}_2) = 1$, $C(\mathbb{Z}_4) = 2$ and
$C(\mathbb{Z}_2 \oplus \mathbb{Z}_2) = 3$.

The two perfect covers of $\mathbb{Z}_4$ are $\{1, 2\}$ and $\{2, 3\}$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorems 2 and 4 at
`n = 1, 2` and `m = 2`. -/
theorem count_small :
    count (ZMod 2) = 1 ∧ count (ZMod 4) = 2 ∧ count (ZMod 2 × ZMod 2) = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [count_eq_card_filter] <;> decide

/-- **Perfect covers of ℤ₄: an example and a non-example.** In the cyclic group
$\mathbb{Z}_4 = \mathbb{Z}/4\mathbb{Z}$, the set $\{1, 2\}$ is a perfect cover and the set
$\{1, 3\}$ is not, since $1 + 3 = 0$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (perfect
covers). -/
theorem isPerfectCover_zmod_four :
    IsPerfectCover ({1, 2} : Finset (ZMod 4)) ∧ ¬ IsPerfectCover ({1, 3} : Finset (ZMod 4)) := by
  decide

omit [DecidableEq G] in
/-- **Odd combinations.** For a finite subset $A$ of an abelian group $G$, $\mathcal{T}(A)$ is the
set of all sums $\sum_{x \in A} c_x x$ with integer coefficients $c_x$ such that every $c_x$ is
either $0$ or odd.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
def oddCombinations (A : Finset G) : Set G :=
  {g | ∃ c : G → ℤ, (∀ x ∈ A, c x = 0 ∨ Odd (c x)) ∧ g = ∑ x ∈ A, c x • x}

omit [DecidableEq G] in
/-- **Zero is an odd combination.** For every finite subset $A$ of an abelian group $G$, $0$ lies
in the set $\mathcal{T}(A)$ of odd combinations of $A$ (take every coefficient equal to $0$).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
theorem zero_mem_oddCombinations (A : Finset G) : (0 : G) ∈ oddCombinations A :=
  ⟨0, fun _ _ => Or.inl rfl, by simp⟩

/-- **Elements of a finite set are odd combinations of it.** Let $G$ be an abelian group and $A$ a
finite subset of $G$, and let $\mathcal{T}(A)$ be the set of combinations $\sum_{y \in A} c_y y$
in which every integer coefficient $c_y$ is $0$ or odd. Every $x \in A$ lies in $\mathcal{T}(A)$:
take $c_x = 1$ and $c_y = 0$ for $y \neq x$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
theorem mem_oddCombinations_of_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    x ∈ oddCombinations A := by
  refine ⟨fun y => if y = x then 1 else 0, fun y _ => ?_, ?_⟩
  · by_cases h : y = x <;> simp [h]
  · simp [ite_smul, Finset.sum_ite_eq', hx]

omit [DecidableEq G] in
/-- **Odd combinations of the empty set.** Let $G$ be an abelian group and, for a finite
$A \subseteq G$, let $\mathcal{T}(A)$ be the set of combinations $\sum_{x \in A} c_x x$ in which
every integer coefficient $c_x$ is $0$ or odd. Then $\mathcal{T}(\emptyset) = \{0\}$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
theorem oddCombinations_empty : oddCombinations (∅ : Finset G) = {0} := by
  ext g
  simp [oddCombinations]

end PerfectSubsetSumCover

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

/-- **Adjoining an element doubles the multiplicity of a perfect cover.** Let $G$ be an abelian
group and let $s = (s_1, \dots, s_k)$ be a perfect $m$-cover of $G$. For every $g \in G$, the
family $(g, s_1, \dots, s_k)$ is a perfect $2m$-cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 5
(`jis-2025-25.7.8-lem-5`). -/
public theorem_wanted isPerfectMCover_cons {G : Type*} [AddCommGroup G] [DecidableEq G]
    {k m : ℕ} {s : Fin k → G} (hs : IsPerfectMCover m s) (g : G) :
    IsPerfectMCover (2 * m) (Fin.cons g s : Fin (k + 1) → G)

/-- **Projections of a perfect cover of a direct sum.** Let $H$ and $K$ be finite abelian groups
with $|H| = 2^m$ and $|K| = 2^n$, and let $s = (s_i)_{i \in \iota}$, indexed by a finite set
$\iota$, be a perfect $l$-cover of $H \oplus K$. Then the first coordinates of the $s_i$ form a
perfect $2^n l$-cover of $H$, and the second coordinates form a perfect $2^m l$-cover of $K$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 6
(`jis-2025-25.7.8-lem-6`). -/
public theorem_wanted isPerfectMCover_fst_snd {H K : Type*} [AddCommGroup H] [DecidableEq H]
    [Fintype H] [AddCommGroup K] [DecidableEq K] [Fintype K] {m n l : ℕ}
    (hH : Fintype.card H = 2 ^ m) (hK : Fintype.card K = 2 ^ n) {ι : Type*} [Fintype ι]
    {s : ι → H × K} (hs : IsPerfectMCover l s) :
    IsPerfectMCover (2 ^ n * l) (fun i => (s i).1) ∧
      IsPerfectMCover (2 ^ m * l) (fun i => (s i).2)

/-- **Removing one element from a perfect cover.** Let $G$ be a finite abelian group of order $2^n$,
let $S$ be a perfect cover of $G$, let $z \in S$ and let $S_1 = S \setminus \{z\}$. Then (a) every
element of $G$ is the sum of at most one subset of $S_1$, and exactly half of the $2^n$ elements
of $G$ are the sum of a subset of $S_1$; (b) if $g \in G$ is the sum of a subset of $S_1$ and $j$
is an integer with $j \ge 1$, then $g + 2jz$ is the sum of a subset of $S_1$ and $g + (2j-1)z$ is
not.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 7
(`jis-2025-25.7.8-lem-7`). -/
public theorem_wanted perfectCover_erase_coverCount {G : Type*} [AddCommGroup G]
    [DecidableEq G] [Fintype G] {n : ℕ} (hG : Fintype.card G = 2 ^ n) {S : Finset G}
    (hS : IsPerfectCover S) {z : G} (hz : z ∈ S) :
    ((∀ g : G, coverCount (fun x : S.erase z => (x : G)) g ≤ 1) ∧
      2 * (Finset.univ.filter fun g : G =>
        coverCount (fun x : S.erase z => (x : G)) g = 1).card = 2 ^ n) ∧
    ∀ g : G, 1 ≤ coverCount (fun x : S.erase z => (x : G)) g → ∀ j : ℕ, 1 ≤ j →
      1 ≤ coverCount (fun x : S.erase z => (x : G)) (g + (2 * j) • z) ∧
        coverCount (fun x : S.erase z => (x : G)) (g + (2 * j - 1) • z) = 0

/-- **Removing the last element of a perfect $2^j$-cover.** Let $G$ be an abelian group, let
$s = (x_1, \dots, x_{k+1})$ be a family in $G$ that is a perfect $2^j$-cover of $G$, and let
$S_1 = (x_1, \dots, x_k)$. For every $a \in G$, if $S_1$ covers $a$ exactly $c$ times, then
$S_1$ covers $a + x_{k+1}$ exactly $2^j - c$ times.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 8
(`jis-2025-25.7.8-lem-8`). The paper's `|G| = 2^n` and `k + 1 = j + n` are not needed. -/
public theorem_wanted coverCount_init_add_last {G : Type*} [AddCommGroup G] [DecidableEq G]
    {j k : ℕ} {s : Fin (k + 1) → G} (hs : IsPerfectMCover (2 ^ j) s) (a : G) :
    coverCount (s ∘ Fin.castSucc) (a + s (Fin.last k)) =
      2 ^ j - coverCount (s ∘ Fin.castSucc) a

/-- **Shifting by multiples of the last element of a perfect $2^j$-cover.** Let $G$ be an
abelian group, let $s = (x_1, \dots, x_{k+1})$ be a family in $G$ that is a perfect $2^j$-cover
of $G$, and let $S_1 = (x_1, \dots, x_k)$. For every $b \in G$, if $S_1$ covers $b$ exactly $c$
times, then for every integer $t$ it covers $b + 2t\,x_{k+1}$ exactly $c$ times and
$b + (2t + 1)\,x_{k+1}$ exactly $2^j - c$ times.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 9
(`jis-2025-25.7.8-cor-9`). `t` ranges over `ℤ`. -/
public theorem_wanted coverCount_init_add_zsmul_last {G : Type*} [AddCommGroup G]
    [DecidableEq G] {j k : ℕ} {s : Fin (k + 1) → G} (hs : IsPerfectMCover (2 ^ j) s)
    (b : G) (t : ℤ) :
    coverCount (s ∘ Fin.castSucc) (b + (2 * t) • s (Fin.last k)) =
        coverCount (s ∘ Fin.castSucc) b ∧
      coverCount (s ∘ Fin.castSucc) (b + (2 * t + 1) • s (Fin.last k)) =
        2 ^ j - coverCount (s ∘ Fin.castSucc) b

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

/-- **Replacing an entry of a perfect $2^k$-cover by an odd multiple.** Let $G$ be an abelian
group, let $k$ and $N$ be natural numbers, and let $a, b, s_1, \dots, s_N \in G$. If the family
$(a, s_1, \dots, s_N)$ is a perfect $2^k$-cover of $G$ and $b = (2j + 1)a$ for some integer $j$,
then the family $(b, s_1, \dots, s_N)$ is also a perfect $2^k$-cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 11
(`jis-2025-25.7.8-lem-11`). The paper's `|G| = 2^n` and length `n + k` are not needed. -/
public theorem_wanted isPerfectMCover_cons_oddMultiple {G : Type*} [AddCommGroup G]
    [DecidableEq G] {k N : ℕ} {a b : G} {s : Fin N → G}
    (hs : IsPerfectMCover (2 ^ k) (Fin.cons a s : Fin (N + 1) → G))
    (hab : ∃ j : ℤ, b = (2 * j + 1) • a) :
    IsPerfectMCover (2 ^ k) (Fin.cons b s : Fin (N + 1) → G)

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

/-- **Orders of second coordinates in perfect $m$-covers.** Let $H$ be a finite abelian group of
order $2^r$ and let $s = (s_i)_{i \in \iota}$ be a family in $H \oplus \mathbb{Z}_{2^n}$ indexed by
a finite type $\iota$. If $s$ is a perfect $m$-cover of $H \oplus \mathbb{Z}_{2^n}$, then for
every $j$ with $1 \le j \le n$ the second coordinate of some $s_i$ has additive order $2^j$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Corollary 14
(`jis-2025-25.7.8-cor-14`). The family has any finite index type (the record reuses `n`
for its length). -/
public theorem_wanted exists_snd_addOrderOf_of_isPerfectMCover {H : Type*} [AddCommGroup H]
    [DecidableEq H] [Fintype H] {r n m : ℕ} (hH : Fintype.card H = 2 ^ r) {ι : Type*}
    [Fintype ι] {s : ι → H × ZMod (2 ^ n)} (hs : IsPerfectMCover m s) :
    ∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ i, addOrderOf (s i).2 = 2 ^ j

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

/-- **Odd combinations are closed under odd multiples.** Let $A$ be a finite subset of an abelian
group $G$. If $g$ lies in the set $\mathcal{T}(A)$ of odd combinations of $A$, then
$(2j+1)g \in \mathcal{T}(A)$ for every integer $j$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 15 (c)
(`jis-2025-25.7.8-thm-15`). "Union of equivalence classes" is stated as closure under odd
multiples (`0 ∈ 𝒯(A)` is `zero_mem_oddCombinations`). -/
public theorem_wanted zsmul_mem_oddCombinations {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) {g : G} (hg : g ∈ oddCombinations A) (j : ℤ) :
    (2 * j + 1) • g ∈ oddCombinations A

/-- **Distinct subset sums from the odd-combination condition.** Let $G$ be an abelian group,
and for a finite set $A \subseteq G$ write $\mathcal{T}(A)$ for the set of odd combinations of
$A$. Let $x = (x_1, \dots, x_m)$ be a family in $G$ such that
$x_i \notin \mathcal{T}(\{x_1, \dots, x_{i-1}\})$ for every $i$ (for $i = 1$ this says
$x_1 \ne 0$, and for $i \ge 2$ it forces $x_i \ne 0$). Then $x$ covers every element of $G$ at
most once, that is, all subset sums of $x$ are distinct; if moreover $|G| = 2^m$, then $x$ is a
perfect $1$-cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 16
(`jis-2025-25.7.8-lem-16`). The paper's "nonzero" hypothesis is the `i = 1` case of `hx`;
distinctness needs no finiteness, and "`m = n`" is `Nat.card G = 2 ^ m`. -/
public theorem_wanted coverCount_le_one_of_not_mem_oddCombinations {G : Type*}
    [AddCommGroup G] [DecidableEq G] {m : ℕ} {x : Fin m → G}
    (hx : ∀ i : Fin m, x i ∉ oddCombinations ((Finset.Iio i).image x)) :
    (∀ g : G, coverCount x g ≤ 1) ∧ (Nat.card G = 2 ^ m → IsPerfectMCover 1 x)

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

/-- **Perfect covers with a prescribed number of odd last coordinates.** Let $H$ be a finite
abelian group of order $2^m$, let $n \ge 1$, and let $G = H \oplus \mathbb{Z}_{2^n}$. For every
$k$ with $1 \le k \le m + 1$, some perfect cover $S$ of $G$ has exactly $k$ elements $(h, y)$
whose coordinate $y \in \mathbb{Z}_{2^n}$ is odd.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 20
(`jis-2025-25.7.8-lem-20`). The setting `G = H ⊕ ℤ_{2^n}`, `|H| = 2^m`, is the one fixed
before the lemma in Section 5; `y` odd means `y.val` odd; `n ≥ 1` added (for `n = 0` no `y` is
odd). -/
public theorem_wanted exists_isPerfectCover_card_odd {H : Type*} [AddCommGroup H]
    [DecidableEq H] [Fintype H] {m n k : ℕ} (hH : Fintype.card H = 2 ^ m) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hkm : k ≤ m + 1) :
    ∃ S : Finset (H × ZMod (2 ^ n)), IsPerfectCover S ∧ (S.filter fun x => Odd x.2.val).card = k

/-- **Perfect covers with exactly one odd element.** Let $H$ be an abelian group of order $2^m$,
let $n \ge 1$ and let $G = H \oplus \mathbb{Z}_{2^n}$. Call an element of $G$ odd when its
$\mathbb{Z}_{2^n}$-coordinate, taken as a representative in $\{0, 1, \dots, 2^n - 1\}$, is odd.
Then the number of perfect covers of $G$ with exactly one odd element is
$2^m \cdot 2^{n-1} \cdot C(H \oplus \mathbb{Z}_{2^{n-1}})$, where $C(K)$ denotes the number of
perfect covers of a group $K$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 21
(`jis-2025-25.7.8-lem-21`). "`y_1` odd, all other `y_i` even" is read as "exactly one odd
`y`" for the unordered set; `y` odd means `y.val` odd; `n ≥ 1` added (`ℤ_{2^{n-1}}`). -/
public theorem_wanted card_perfectCover_one_odd {H : Type*} [AddCommGroup H] [DecidableEq H]
    [Fintype H] {m n : ℕ} (hH : Fintype.card H = 2 ^ m) (hn : 1 ≤ n) :
    Nat.card {S : Finset (H × ZMod (2 ^ n)) // IsPerfectCover S ∧
        (S.filter fun x => Odd x.2.val).card = 1} =
      2 ^ m * 2 ^ (n - 1) * count (H × ZMod (2 ^ (n - 1)))

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
