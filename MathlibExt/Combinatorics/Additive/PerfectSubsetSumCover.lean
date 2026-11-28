/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Perfect subset-sum covers

A perfect `l`-cover represents each group element as a subset sum of the indexed family
in exactly `l` ways. Projecting a perfect cover of a product onto one factor multiplies
the cover multiplicity by the order of the other factor.

For a finite abelian group `H` of order `2^m` and `n ≥ 1`, perfect covers of
`H × ZMod (2^n)` with exactly one odd last-coordinate representative correspond to a
choice of that odd element and a perfect cover of `H × ZMod (2^(n-1))`. The latter
is embedded by doubling the last coordinate.

## References

* John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power of 2*,
  Journal of Integer Sequences 28 (2025), Article 25.7.8, pp. 1–18, especially §1 for the cover
  definitions, §2, Lemmas 5 and 6 (p. 4), Theorem 15(c) and Lemma 16 (p. 8), and §4,
  Lemma 21 (p. 12).
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
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 2 (the operator `𝒯`). -/
def oddCombinations (A : Finset G) : Set G :=
  {g | ∃ c : G → ℤ, (∀ x ∈ A, c x = 0 ∨ Odd (c x)) ∧ g = ∑ x ∈ A, c x • x}

omit [DecidableEq G] in
/-- **Zero is an odd combination.** For every finite subset $A$ of an abelian group $G$, $0$ lies
in the set $\mathcal{T}(A)$ of odd combinations of $A$ (take every coefficient equal to $0$).

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 2 (the operator `𝒯`). -/
theorem zero_mem_oddCombinations (A : Finset G) : (0 : G) ∈ oddCombinations A :=
  ⟨0, fun _ _ => Or.inl rfl, by simp⟩

omit [DecidableEq G] in
/-- **Elements of a finite set are odd combinations of it.** Let $G$ be an abelian group and $A$ a
finite subset of $G$, and let $\mathcal{T}(A)$ be the set of combinations $\sum_{y \in A} c_y y$
in which every integer coefficient $c_y$ is $0$ or odd. Every $x \in A$ lies in $\mathcal{T}(A)$:
take $c_x = 1$ and $c_y = 0$ for $y \neq x$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 2 (the operator `𝒯`). -/
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
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Section 2 (the operator `𝒯`). -/
theorem oddCombinations_empty : oddCombinations (∅ : Finset G) = {0} := by
  ext g
  simp [oddCombinations]

end PerfectSubsetSumCover

open PerfectSubsetSumCover

-- Preserve the existing `DecidableEq` instance argument for legacy clients.
set_option linter.unusedDecidableInType false in
/-- **Odd combinations are closed under odd multiples.** Let $A$ be a finite subset of an abelian
group $G$. If $g$ lies in the set $\mathcal{T}(A)$ of odd combinations of $A$, then
$(2j+1)g \in \mathcal{T}(A)$ for every integer $j$.

Source: John Greene and Clayton Higgins, *Maximal Subset Sums in a Group of Order a Power
of 2*, Journal of Integer Sequences 28 (2025), Article 25.7.8, Theorem 15 (c)
(`jis-2025-25.7.8-thm-15`). "Union of equivalence classes" is stated as closure under odd
multiples (`0 ∈ 𝒯(A)` is `zero_mem_oddCombinations`). -/
public theorem zsmul_mem_oddCombinations {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) {g : G} (hg : g ∈ oddCombinations A) (j : ℤ) :
    (2 * j + 1) • g ∈ oddCombinations A := by
  obtain ⟨c, hc, rfl⟩ := hg
  have hj : Odd (2 * j + 1) := ⟨j, rfl⟩
  refine ⟨fun x => (2 * j + 1) * c x, ?_, ?_⟩
  · intro x hx
    rcases hc x hx with hzero | hodd
    · exact Or.inl (by simp [hzero])
    · exact Or.inr (hj.mul hodd)
  · change zsmulAddGroupHom (2 * j + 1) (∑ x ∈ A, c x • x) =
      ∑ x ∈ A, ((2 * j + 1) * c x) • x
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => (mul_zsmul x _ _).symm

/-- **Cover count after prepending an entry.** Let $s$ be a finite indexed family in an abelian
group $G$ and let $g, x \in G$. The number of subsets of indices of $(g, s)$ that sum to $x$ is
the sum of the cover counts of $x$ and $x - g$ in $s$. These count subsets that omit and contain
the first index, respectively. No perfectness assumption is needed.

Source: the subset partition in the proof of Lemma 5 of John Greene and Clayton Higgins,
*Maximal Subset Sums in a Group of Order a Power of 2*, Journal of Integer Sequences 28 (2025),
Article 25.7.8. -/
theorem coverCount_cons {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ}
    (s : Fin k → G) (g x : G) :
    coverCount (Fin.cons g s) x = coverCount s x + coverCount s (x - g) := by
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
    simp only [Finset.sum_image (Finset.map_injective e).injOn]
  have htail (I : Finset (Fin k)) : (∑ i ∈ I.map e, Fin.cons g s i) = ∑ i ∈ I, s i := by
    simp [Finset.sum_map, e]
  simpa only [coverCount, Finset.card_eq_sum_ones, Finset.sum_filter, hit, htail,
    Finset.sum_insert (hzero _), Fin.cons_zero, add_comm g, ← eq_sub_iff_add_eq] using hsplit

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
  rw [coverCount_cons, hs x, hs (x - g), two_mul]

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
theorem coverCount_le_one_of_not_mem_oddCombinations {G : Type*}
    [AddCommGroup G] [DecidableEq G] {m : ℕ} {x : Fin m → G}
    (hx : ∀ i : Fin m, x i ∉ oddCombinations ((Finset.Iio i).image x)) :
    (∀ g : G, coverCount x g ≤ 1) ∧ (Nat.card G = 2 ^ m → IsPerfectMCover 1 x) := by
  have hinj : Function.Injective x := by
    have hne {i j : Fin m} (hij : i < j) : x i ≠ x j := by
      intro h
      exact hx j (h ▸ mem_oddCombinations_of_mem
        (Finset.mem_image_of_mem x (Finset.mem_Iio.mpr hij)))
    intro i j h
    exact le_antisymm (le_of_not_gt fun hji => hne hji h.symm)
      (le_of_not_gt fun hij => hne hij h)
  let subsetSum (s : Finset (Fin m)) : G := ∑ i ∈ s, x i
  have hsum_inj : Function.Injective subsetSum := by
    intro s t hsum
    by_contra hne
    let d := (s \ t) ∪ (t \ s)
    have hd : d.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      obtain ⟨hst, hts⟩ := Finset.union_eq_empty.mp he
      exact hne (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp hst)
        (Finset.sdiff_eq_empty_iff_subset.mp hts))
    let i := d.max' hd
    have hbelow {j : Fin m} (hj : j ∈ d) (hji : j ≠ i) : j ∈ Finset.Iio i :=
      Finset.mem_Iio.mpr (lt_of_le_of_ne (Finset.le_max' d j hj) hji)
    -- Cancel the common summands, then isolate the greatest remaining index.
    have hcancel : subsetSum (s \ t) = subsetSum (t \ s) := by
      apply sub_eq_zero.mp
      calc
        _ = subsetSum s - subsetSum t := Finset.sum_sdiff_sub_sum_sdiff
        _ = 0 := sub_eq_zero.mpr hsum
    have hbad (a b : Finset (Fin m)) (hia : i ∈ a) (hib : i ∉ b)
        (ha : a ⊆ d) (hb : b ⊆ d) (heq : subsetSum a = subsetSum b) : False := by
      have ha' : a.erase i ⊆ Finset.Iio i := fun _ hj =>
        hbelow (ha (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
      have hb' : b ⊆ Finset.Iio i := fun _ hj => hbelow (hb hj) fun h => hib (h ▸ hj)
      -- The difference of the membership indicators gives coefficients in {0, 1, -1}.
      let c (g : G) : ℤ := (if g ∈ b.image x then 1 else 0) -
        (if g ∈ (a.erase i).image x then 1 else 0)
      have hsumImage (u : Finset (Fin m)) (hu : u ⊆ Finset.Iio i) :
          (∑ g ∈ (Finset.Iio i).image x, (if g ∈ u.image x then (1 : ℤ) else 0) • g) =
            subsetSum u := by
        simp only [ite_smul, one_zsmul, zero_zsmul]
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.mpr (Finset.image_subset_image hu), Finset.sum_image hinj.injOn]
      apply hx i
      refine ⟨c, fun g _ => ?_, ?_⟩
      · simp only [c]
        split_ifs <;> decide
      · simp only [c, sub_zsmul, ← sub_eq_add_neg, Finset.sum_sub_distrib,
          hsumImage b hb', hsumImage (a.erase i) ha']
        exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans
          ((Finset.sum_erase_add _ _ hia).trans heq))
    rcases Finset.mem_union.mp (Finset.max'_mem d hd) with hi | hi
    · exact hbad (s \ t) (t \ s) hi (fun hj => (Finset.mem_sdiff.mp hi).2
        (Finset.mem_sdiff.mp hj).1) Finset.subset_union_left Finset.subset_union_right hcancel
    · exact hbad (t \ s) (s \ t) hi (fun hj => (Finset.mem_sdiff.mp hi).2
        (Finset.mem_sdiff.mp hj).1) Finset.subset_union_right Finset.subset_union_left hcancel.symm
  have hle (g : G) : coverCount x g ≤ 1 := by
    rw [coverCount, Finset.card_le_one_iff]
    intro s t hs ht
    obtain ⟨-, hs⟩ := Finset.mem_filter.mp hs
    obtain ⟨-, ht⟩ := Finset.mem_filter.mp ht
    exact hsum_inj (hs.trans ht.symm)
  refine ⟨hle, ?_⟩
  intro hcard
  have : Finite G := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero m (by decide))
  let : Fintype G := Fintype.ofFinite G
  have hcard' : Fintype.card (Finset (Fin m)) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card (α := G), hcard, Fintype.card_finset, Fintype.card_fin]
  have hsurj : Function.Surjective subsetSum :=
    ((Fintype.bijective_iff_injective_and_card subsetSum).2 ⟨hsum_inj, hcard'⟩).2
  intro g
  obtain ⟨s, hs⟩ := hsurj g
  refine le_antisymm (hle g) ?_
  exact Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩

end

open PerfectSubsetSumCover

private theorem coverCount_reindex {ι κ G : Type*} [Fintype ι] [Fintype κ] [AddCommGroup G]
    [DecidableEq G] (e : ι ≃ κ) (s : κ → G) (x : G) :
    coverCount (s ∘ e) x = coverCount s x := by
  unfold coverCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  apply Fintype.card_congr (Equiv.subtypeEquiv (Equiv.finsetCongr e) ?_)
  intro I
  simp [Equiv.finsetCongr_apply, Finset.sum_map]

private theorem coverCount_insert_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) {z : G} (hz : z ∉ S) (x : G) :
    coverCount (fun a : ↥(insert z S) => (a : G)) x =
      coverCount (fun a : S => (a : G)) x + coverCount (fun a : S => (a : G)) (x - z) := by
  let e := S.equivFin.symm
  let s : Fin S.card → G := fun i => (e i : G)
  let EFun (i : Fin (S.card + 1)) : ↥(insert z S) :=
    Fin.cases ⟨z, Finset.mem_insert_self _ _⟩ (fun j => ⟨e j, Finset.mem_insert_of_mem (e j).2⟩) i
  have hval (i : Fin (S.card + 1)) :
      (EFun i : G) = (Fin.cons z s : Fin (S.card + 1) → G) i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [EFun, s]
  have hhead : z ∉ Set.range s := by
    rintro ⟨i, hi⟩
    exact hz (hi ▸ (e i).2)
  have htail : Function.Injective s := fun _ _ h => e.injective (Subtype.ext h)
  have hinj : Function.Injective EFun := by
    intro i j h
    apply Fin.cons_injective_of_injective hhead htail
    simpa only [hval] using congrArg (fun a : ↥(insert z S) => (a : G)) h
  let E := Equiv.ofBijective EFun ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [Finset.card_insert_of_notMem hz]⟩)
  have hE : (fun a : ↥(insert z S) => (a : G)) ∘ E = Fin.cons z s := by
    funext i
    simpa only [E, Function.comp_apply, Equiv.ofBijective_apply] using hval i
  rw [← coverCount_reindex E, hE, coverCount_cons]
  exact congrArg₂ (· + ·) (coverCount_reindex e _ _) (coverCount_reindex e _ _)

private theorem coverCount_map_finset {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [DecidableEq K] (f : G →+ K) (hf : Function.Injective f)
    (S : Finset G) (x : K) :
    coverCount (fun a : S.map ⟨f, hf⟩ => (a : K)) x =
      (Finset.univ.filter fun I : Finset S => f (∑ a ∈ I, (a : G)) = x).card := by
  rw [← coverCount_reindex (S.equivMap (⟨f, hf⟩ : G ↪ K))]
  simp [coverCount, ← map_sum]

-- A perfect cover with a single element over `1` is determined by that element and its tail.
private noncomputable def perfectCoverOneOddEquiv {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [DecidableEq G] [DecidableEq K] (f : G →+ K) (hf : Function.Injective f)
    (p : K →+ ZMod 2) (hp : ∀ x, x ∈ Set.range f ↔ p x = 0) :
    ({z : K // p z = 1} × {S : Finset G // IsPerfectCover S}) ≃
      {T : Finset K // IsPerfectCover T ∧ (T.filter fun z => p z = 1).card = 1} := by
  let e : G ↪ K := ⟨f, hf⟩
  have hzero (a : G) : p (f a) = 0 := (hp _).mp ⟨a, rfl⟩
  have hnotMem (z : {z : K // p z = 1}) (S : Finset G) : (z : K) ∉ S.map e := by
    rintro hz
    obtain ⟨a, -, ha⟩ := Finset.mem_map.mp hz
    exact zero_ne_one ((hzero a).symm.trans ((congrArg p ha).trans z.2))
  have hfilter (z : {z : K // p z = 1}) (S : Finset G) :
      (insert (z : K) (S.map e)).filter (fun x => p x = 1) = {z.val} := by
    have htail : (S.map e).filter (fun x => p x = 1) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      rintro _ hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hx
      simp [e, hzero]
    simp [Finset.filter_insert, z.2, htail]
  have hcover (z : {z : K // p z = 1}) (S : Finset G) :
      IsPerfectCover (insert (z : K) (S.map e)) ↔ IsPerfectCover S := by
    let c := coverCount (fun a : S.map e => (a : K))
    have hcount (x : G) : c (f x) = coverCount (fun a : S => (a : G)) x := by
      rw [show c (f x) = (Finset.univ.filter fun I : Finset S =>
        f (∑ a ∈ I, (a : G)) = f x).card from coverCount_map_finset f hf S _]
      simp only [hf.eq_iff, coverCount]
    have houtside (x : K) (hx : p x ≠ 0) : c x = 0 := by
      change coverCount (fun a : S.map ⟨f, hf⟩ => (a : K)) x = 0
      rw [coverCount_map_finset f hf, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun I _ h => hx (h ▸ hzero (∑ a ∈ I, (a : G)))
    have hsplit (x : K) :
        coverCount (fun a : ↥(insert (z : K) (S.map e)) => (a : K)) x = c x + c (x - z) :=
      coverCount_insert_eq _ (hnotMem z S) x
    constructor
    · intro h x
      have hx : p (f x - z) ≠ 0 := by simp [map_sub, hzero, z.2]
      have hfx : coverCount (fun a : ↥(insert (z : K) (S.map e)) => (a : K)) (f x) = 1 :=
        h (f x)
      simpa only [hsplit, houtside _ hx, add_zero, hcount] using hfx
    · intro h x
      change coverCount (fun a : ↥(insert (z : K) (S.map e)) => (a : K)) x = 1
      rw [hsplit]
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (p x) with hx | hx
      · obtain ⟨y, rfl⟩ := (hp x).mpr hx
        rw [hcount, h y, houtside _ (by simp [map_sub, hzero, z.2]), add_zero]
      · obtain ⟨y, hy⟩ := (hp (x - z)).mpr (by rw [map_sub, hx, z.2, sub_self])
        rw [houtside _ (by rw [hx]; exact one_ne_zero), ← hy, hcount, h y, zero_add]
  let liftCover : ({z : K // p z = 1} × {S : Finset G // IsPerfectCover S}) →
      {T : Finset K // IsPerfectCover T ∧ (T.filter fun z => p z = 1).card = 1} :=
    fun ⟨z, S⟩ => ⟨insert z.val (S.val.map e), (hcover z S).mpr S.2, by simp [hfilter]⟩
  refine Equiv.ofBijective liftCover ⟨?_, ?_⟩
  · rintro ⟨z, S⟩ ⟨w, T⟩ h
    have heq : insert z.val (S.val.map e) = insert w.val (T.val.map e) := congrArg Subtype.val h
    have hzw : z = w := by
      apply Subtype.ext
      simpa only [hfilter, Finset.singleton_inj] using
        congrArg (Finset.filter fun x : K => p x = 1) heq
    subst w
    congr 1
    apply Subtype.ext
    apply Finset.map_injective e
    simpa only [Finset.erase_insert (hnotMem z S), Finset.erase_insert (hnotMem z T)] using
      congrArg (fun U : Finset K => U.erase z.val) heq
  · rintro ⟨T, hT, hodd⟩
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hodd
    have hz' : z ∈ T ∧ p z = 1 := Finset.mem_filter.mp (hz.symm ▸ Finset.mem_singleton_self z)
    let S := (T.erase z).preimage e e.injective.injOn
    have hmap : S.map e = T.erase z := by
      classical
      rw [Finset.map_eq_image, Finset.image_preimage, Finset.filter_eq_self]
      intro x hx
      apply (hp x).mpr
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (p x) with h | h
      · exact h
      · have hx' : x ∈ T.filter (fun a => p a = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hx, h⟩
        rw [hz, Finset.mem_singleton] at hx'
        exact (Finset.ne_of_mem_erase hx hx').elim
    have hfull : insert z (S.map e) = T := by rw [hmap, Finset.insert_erase hz'.1]
    exact ⟨(⟨z, hz'.2⟩, ⟨S, (hcover ⟨z, hz'.2⟩ S).mp (hfull.symm ▸ hT)⟩),
      Subtype.ext hfull⟩

private def doubleZMod (q : ℕ) : ZMod q →+ ZMod (q * 2) :=
  ZMod.lift q ⟨(Int.castAddHom (ZMod (q * 2))).comp (AddMonoidHom.mulLeft (2 : ℤ)), by
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, Int.coe_castAddHom]
    exact_mod_cast (show ((2 * q : ℕ) : ZMod (q * 2)) = 0 by rw [mul_comm, ZMod.natCast_self])⟩

private theorem doubleZMod_val {q : ℕ} [NeZero q] (x : ZMod q) :
    (doubleZMod q x).val = 2 * x.val := by
  have heq : doubleZMod q x = ((2 * x.val : ℕ) : ZMod (q * 2)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast]
    rw [doubleZMod, ZMod.lift_coe]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, Int.coe_castAddHom]
    push_cast
    rfl
  rw [heq, ZMod.val_natCast_of_lt (by have := ZMod.val_lt x; omega)]

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
public theorem card_perfectCover_one_odd {H : Type*} [AddCommGroup H] [DecidableEq H]
    [Fintype H] {m n : ℕ} (hH : Fintype.card H = 2 ^ m) (hn : 1 ≤ n) :
    Nat.card {S : Finset (H × ZMod (2 ^ n)) // IsPerfectCover S ∧
        (S.filter fun x => Odd x.2.val).card = 1} =
      2 ^ m * 2 ^ (n - 1) * count (H × ZMod (2 ^ (n - 1))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.pow_succ, Nat.succ_sub_one]
  let q : ℕ := 2 ^ n
  have : NeZero q := ⟨pow_ne_zero _ (by decide)⟩
  let f : (H × ZMod q) →+ H × ZMod (q * 2) := (AddMonoidHom.id H).prodMap (doubleZMod q)
  have hf_apply (a : H × ZMod q) : f a = (a.1, doubleZMod q a.2) := by
    cases a
    simp only [f, AddMonoidHom.coe_prodMap, Prod.map_apply, AddMonoidHom.id_apply]
  have hf : Function.Injective f := by
    intro a b h
    rw [hf_apply, hf_apply, Prod.mk.injEq] at h
    refine Prod.ext h.1 (ZMod.val_injective _ ?_)
    have hv := congrArg ZMod.val h.2
    rw [doubleZMod_val, doubleZMod_val] at hv
    omega
  let p : (H × ZMod (q * 2)) →+ ZMod 2 :=
    (ZMod.castHom (dvd_mul_left 2 q) (ZMod 2)).toAddMonoidHom.comp (AddMonoidHom.snd H _)
  have hpval (a : H × ZMod (q * 2)) : p a = (a.2.val : ZMod 2) := by
    simp only [p, AddMonoidHom.comp_apply, AddMonoidHom.coe_snd]
    exact (ZMod.castHom_apply (h := dvd_mul_left 2 q) a.2).trans (ZMod.natCast_val a.2).symm
  have hp (a : H × ZMod (q * 2)) : a ∈ Set.range f ↔ p a = 0 := by
    rw [hpval, ZMod.natCast_eq_zero_iff_even]
    constructor
    · rintro ⟨b, rfl⟩
      rw [hf_apply, doubleZMod_val]
      exact even_two.mul_right _
    · rintro ⟨k, hk⟩
      have hlt := ZMod.val_lt a.2
      have hkq : k < q := by omega
      refine ⟨(a.1, (k : ZMod q)), ?_⟩
      rw [hf_apply]
      refine Prod.ext ?_ (ZMod.val_injective _ ?_)
      · rfl
      · simp only [doubleZMod_val, ZMod.val_natCast_of_lt hkq]
        omega
  have hodd (a : H × ZMod (q * 2)) : Odd a.2.val ↔ p a = 1 := by
    rw [hpval, ZMod.natCast_eq_one_iff_odd]
  -- Translation by `(0, 1)` identifies the even and odd fibers.
  let u : H × ZMod (q * 2) := (0, 1)
  have hu : p u = 1 := by simp [p, u]
  let oddEquiv : (H × ZMod q) ≃ {a : H × ZMod (q * 2) // p a = 1} := by
    refine Equiv.ofBijective (fun b => ⟨f b + u, by rw [map_add, (hp _).mp ⟨b, rfl⟩, hu, zero_add]⟩)
      ⟨?_, ?_⟩
    · intro b c h
      exact hf (add_right_cancel (congrArg Subtype.val h))
    · intro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := (hp (a - u)).mpr (by rw [map_sub, ha, hu, sub_self])
      exact ⟨b, Subtype.ext (eq_sub_iff_add_eq.mp hb)⟩
  let parityEquiv :
      {S : Finset (H × ZMod (q * 2)) // IsPerfectCover S ∧
        (S.filter fun a => Odd a.2.val).card = 1} ≃
      {S : Finset (H × ZMod (q * 2)) // IsPerfectCover S ∧
        (S.filter fun a => p a = 1).card = 1} :=
    Equiv.subtypeEquivRight fun S => by
      rw [Finset.filter_congr (fun a _ => hodd a)]
  change Nat.card {S : Finset (H × ZMod (q * 2)) // IsPerfectCover S ∧
      (S.filter fun a => Odd a.2.val).card = 1} = 2 ^ m * q * count (H × ZMod q)
  rw [Nat.card_congr parityEquiv, ← Nat.card_congr (perfectCoverOneOddEquiv f hf p hp),
    Nat.card_prod, ← Nat.card_congr oddEquiv, Nat.card_prod,
    Nat.card_eq_fintype_card (α := H), Nat.card_eq_fintype_card (α := ZMod q), ZMod.card, hH]
  rfl

end MetaMathlibExt
