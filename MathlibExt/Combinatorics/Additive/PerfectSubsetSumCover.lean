/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Perfect subset-sum covers

A perfect `l`-cover represents each group element as a subset sum of the indexed family
in exactly `l` ways. Projecting a perfect cover of a product onto one factor multiplies
the cover multiplicity by the order of the other factor.
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

instance instDecidableIsPerfectMCoverOfFintype {ι : Type*} [Fintype ι] [Fintype G]
    (m : ℕ) (s : ι → G) : Decidable (IsPerfectMCover m s) := by
  unfold IsPerfectMCover; infer_instance

/-- **Perfect cover.** Let $G$ be an abelian group. A finite set $S \subseteq G$ is a perfect cover
of $G$ when every element of $G$ is the sum of exactly one subset of $S$ (the empty subset has
sum $0$); that is, the family of the elements of $S$ is a perfect $1$-cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 1 (perfect covers,
Lemma 16). -/
def IsPerfectCover (S : Finset G) : Prop :=
  IsPerfectMCover 1 (fun x : S => (x : G))

instance instDecidableIsPerfectCoverOfFintype [Fintype G] (S : Finset G) :
    Decidable (IsPerfectCover S) := by
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

omit [DecidableEq G] in
/-- **Elements of a finite set are odd combinations of it.** Let $G$ be an abelian group and $A$ a
finite subset of $G$, and let $\mathcal{T}(A)$ be the set of combinations $\sum_{y \in A} c_y y$
in which every integer coefficient $c_y$ is $0$ or odd. Every $x \in A$ lies in $\mathcal{T}(A)$:
take $c_x = 1$ and $c_y = 0$ for $y \neq x$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 3 (the operator `𝒯`). -/
theorem mem_oddCombinations_of_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    x ∈ oddCombinations A := by
  classical
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

/-- **Adjoining an element doubles the multiplicity of a perfect cover.** Let $G$ be an abelian
group and let $s = (s_1, \dots, s_k)$ be a perfect $m$-cover of $G$. For every $g \in G$, the
family $(g, s_1, \dots, s_k)$ is a perfect $2m$-cover of $G$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 5
(`jis-2025-25.7.8-lem-5`). -/
theorem isPerfectMCover_cons {G : Type*} [AddCommGroup G] [DecidableEq G]
    {k m : ℕ} {s : Fin k → G} (hs : IsPerfectMCover m s) (g : G) :
    IsPerfectMCover (2 * m) (Fin.cons g s : Fin (k + 1) → G) := by
  intro x
  let e := Fin.succEmb k
  have hzero (I : Finset (Fin k)) : (0 : Fin (k + 1)) ∉ I.map e := by
    simp [e]
  have huniv : (Finset.univ : Finset (Fin (k + 1))) = insert 0 (Finset.univ.map e) := by
    rw [Fin.univ_succ, Finset.cons_eq_insert]
    rfl
  have hmap : (Finset.univ.map e).powerset = Finset.univ.image (Finset.map e) := by
    simp only [funext (Finset.map_eq_image e), Finset.powerset_image, Finset.powerset_univ]
  let hit (I : Finset (Fin (k + 1))) : ℕ :=
    if (∑ i ∈ I, Fin.cons g s i) = x then 1 else 0
  -- Split the sum over index sets according to whether they contain index zero.
  have hsplit : (∑ I, hit I) =
      (∑ I : Finset (Fin k), hit (I.map e)) +
        ∑ I : Finset (Fin k), hit (insert 0 (I.map e)) := by
    conv_lhs => rw [← Finset.powerset_univ, huniv, Finset.sum_powerset_insert (hzero _), hmap]
    rw [Finset.sum_image (Finset.map_injective e).injOn,
      Finset.sum_image (Finset.map_injective e).injOn]
  have htail (I : Finset (Fin k)) : (∑ i ∈ I.map e, Fin.cons g s i) = ∑ i ∈ I, s i := by
    simp [Finset.sum_map, e]
  have hcount : coverCount (Fin.cons g s) x = coverCount s x + coverCount s (x - g) := by
    simpa only [coverCount, Finset.card_eq_sum_ones, Finset.sum_filter, hit, htail,
      Finset.sum_insert (hzero _), Fin.cons_zero, add_comm g, ← eq_sub_iff_add_eq] using hsplit
  rw [hcount, hs x, hs (x - g), two_mul]

/-- **Projections of a perfect cover of a direct sum.** Let $H$ and $K$ be finite abelian groups
with $|H| = 2^m$ and $|K| = 2^n$, and let $s = (s_i)_{i \in \iota}$, indexed by a finite set
$\iota$, be a perfect $l$-cover of $H \oplus K$. Then the first coordinates of the $s_i$ form a
perfect $2^n l$-cover of $H$, and the second coordinates form a perfect $2^m l$-cover of $K$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Lemma 6
(`jis-2025-25.7.8-lem-6`). -/
theorem isPerfectMCover_fst_snd {H K : Type*} [AddCommGroup H] [DecidableEq H]
    [Fintype H] [AddCommGroup K] [DecidableEq K] [Fintype K] {m n l : ℕ}
    (hH : Fintype.card H = 2 ^ m) (hK : Fintype.card K = 2 ^ n) {ι : Type*} [Fintype ι]
    {s : ι → H × K} (hs : IsPerfectMCover l s) :
    IsPerfectMCover (2 ^ n * l) (fun i => (s i).1) ∧
      IsPerfectMCover (2 ^ m * l) (fun i => (s i).2) := by
  constructor
  · intro h
    unfold coverCount
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I : Finset ι => ∑ i ∈ I, (s i).2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _), ← hK, ← Finset.card_univ]
    apply Finset.sum_const_nat
    intro k _
    simpa only [coverCount, Finset.filter_filter, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum] using
      hs (h, k)
  · intro k
    unfold coverCount
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I : Finset ι => ∑ i ∈ I, (s i).1)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _), ← hH, ← Finset.card_univ]
    apply Finset.sum_const_nat
    intro h _
    simpa only [coverCount, Finset.filter_filter, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum,
      and_comm] using hs (h, k)

end

end MetaMathlibExt
