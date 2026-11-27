/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import MathlibExt.Combinatorics.Enumerative.Partition.TriangularQBinomial
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax

/-!
# Lit cells of weakly decreasing bargraphs

Removing the first column of a bargraph in which only that column is lit leaves a
partition contained in a staircase. This gives a coefficientwise generating function.
-/

open PowerSeries PowerSeries.WithPiTopology
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Lit cells of a weakly decreasing bargraph.** Let $p$ be a partition of $n$ with $\ell$
parts $x_1 \ge x_2 \ge \cdots \ge x_\ell$. The number of lit cells of $p$, drawn as a weakly
decreasing bargraph, is defined as $\max_{1 \le i \le \ell} (x_i + i - 1)$, and as $0$ when $p$
has no parts. It is the largest part of the image of $p$ under Prodinger's bijection
$x_i \mapsto x_i + i - 1$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 5. -/
public def litCellsDecreasing {n : ℕ} (p : Nat.Partition n) : ℕ :=
  ((decreasingParts p).mapIdx fun i x => x + i).foldr max 0

/-- **Triangle partition series.** For a natural number $r$, the triangle partition series is the
power series $T_q(r) = \sum_{s=0}^{r} t[r, s] \in \mathbb{Z}[[q]]$, where $t[r, s]$ is the
triangular $q$-binomial coefficient. It is the generating function of partitions contained in the
triangle with column heights $r, r - 1, \dots, 1$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Definition 1. -/
public noncomputable def trianglePartitionSeries (r : ℕ) : ℤ⟦X⟧ :=
  ∑ s ∈ Finset.range (r + 1), triangularQBinomial r s

private abbrev FitsStaircase {n : ℕ} (r : ℕ) (p : Nat.Partition n) : Prop :=
  ∀ i < p.parts.card, (decreasingParts p).getD i 0 + i ≤ r

private theorem length_decreasingParts {n : ℕ} (p : Nat.Partition n) :
    (decreasingParts p).length = p.parts.card := by
  simp [decreasingParts]

private theorem litCellsDecreasing_le_iff {n k : ℕ} (p : Nat.Partition n) :
    litCellsDecreasing p ≤ k ↔ FitsStaircase k p := by
  constructor
  · intro h i hi
    have hi' : i < (decreasingParts p).length := by rwa [length_decreasingParts]
    rw [List.getD_eq_getElem _ _ hi']
    exact le_trans (List.le_max_of_le' 0 (List.mem_mapIdx.mpr ⟨i, hi', rfl⟩) le_rfl) h
  · intro h
    apply List.max_le_of_forall_le
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp ha
    simpa only [List.getD_eq_getElem _ _ hi] using h i (by rwa [length_decreasingParts] at hi)

-- The new head contributes its own height. Each tail entry's index increases by one.
private theorem firstColumn_cons_iff {n d r : ℕ} {p : Nat.Partition n} {q : Nat.Partition d}
    (hp : p.parts = (r + 2) ::ₘ q.parts) :
    (litCellsDecreasing p = p.parts.sup ∧ p.parts.sup = r + 2) ↔ FitsStaircase (r + 1) q := by
  have hsup : p.parts.sup = r + 2 ↔ ∀ a ∈ q.parts, a ≤ r + 2 := by
    rw [hp, Multiset.sup_cons, sup_eq_left, Multiset.sup_le]
  have hfit (h : ∀ a ∈ q.parts, a ≤ r + 2) :
      litCellsDecreasing p = r + 2 ↔ FitsStaircase (r + 1) q := by
    have hsort : decreasingParts p = (r + 2) :: decreasingParts q := by
      rw [decreasingParts, hp, Multiset.sort_cons _ _ _ h]
      rfl
    have hcard : p.parts.card = q.parts.card + 1 := by rw [hp, Multiset.card_cons]
    have hhead : r + 2 ≤ litCellsDecreasing p := by
      have hzero := (litCellsDecreasing_le_iff p).mp le_rfl 0 (by omega)
      simpa [hsort] using hzero
    rw [le_antisymm_iff, and_iff_left hhead, litCellsDecreasing_le_iff]
    constructor
    · intro h' i hi
      have hb := h' (i + 1) (by omega)
      simp only [hsort, List.getD_cons_succ] at hb
      omega
    · intro h' i hi
      cases i with
      | zero => simp [hsort]
      | succ i =>
        have hb := h' i (by omega)
        simp only [hsort, List.getD_cons_succ]
        omega
  constructor
  · rintro ⟨hlit, hm⟩
    exact (hfit (hsup.mp hm)).mp (hlit.trans hm)
  · intro h
    have hm := hsup.mpr (fun a ha => by
      have ha' : a ∈ decreasingParts q := (Multiset.mem_sort _).mpr ha
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ha'
      have hb := h i (by simpa only [length_decreasingParts] using hi)
      rw [List.getD_eq_getElem _ _ hi, heq] at hb
      omega)
    exact ⟨((hfit (hsup.mp hm)).mpr h).trans hm.symm, hm⟩

private theorem sup_mem_of_pos (s : Multiset ℕ) (h : 0 < s.sup) : s.sup ∈ s := by
  induction s using Multiset.induction_on with
  | empty => simp at h
  | cons a s ih =>
    rcases le_total s.sup a with ha | ha
    · simp [sup_eq_left.mpr ha]
    · simp only [Multiset.sup_cons, sup_eq_right.mpr ha] at h ⊢
      exact Multiset.mem_cons_of_mem (ih h)

private abbrev firstColumnFiber (n r : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter fun p => litCellsDecreasing p = p.parts.sup ∧ p.parts.sup = r + 2

private theorem card_firstColumnFiber {n r : ℕ} (h : r + 2 ≤ n) :
    (firstColumnFiber n r).card =
      (Finset.univ.filter (FitsStaircase (r + 1) : Nat.Partition (n - (r + 2)) → Prop)).card := by
  let e := Nat.Partition.partitionWithPartEquiv (a := r + 2) (by omega) h
  have hmem (q : Nat.Partition (n - (r + 2))) :
      (e.symm q).val ∈ firstColumnFiber n r ↔ FitsStaircase (r + 1) q := by
    simp only [firstColumnFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact firstColumn_cons_iff (Nat.Partition.partitionWithPartEquiv_symm_apply_parts _ _ _)
  symm
  refine Finset.card_bij (fun q _ => (e.symm q).val) ?_ ?_ ?_
  · intro q hq
    exact (hmem q).mpr (Finset.mem_filter.mp hq).2
  · intro q _ q' _ heq
    exact e.symm.injective (Subtype.ext heq)
  · intro p hp
    have hm := (Finset.mem_filter.mp hp).2.2
    let p' : {p : Nat.Partition n // r + 2 ∈ p.parts} := ⟨p, by
      rw [← hm]
      exact sup_mem_of_pos _ (by omega)⟩
    have heq : (e.symm (e p')).val = p := congrArg Subtype.val (e.symm_apply_apply p')
    exact ⟨e p', Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem _).mp (heq ▸ hp)⟩, heq⟩

private theorem coeff_trianglePartitionSeries (n r : ℕ) :
    coeff n (trianglePartitionSeries r) =
      ((Finset.univ.filter (FitsStaircase r : Nat.Partition n → Prop)).card : ℤ) := by
  let fits := Finset.univ.filter (FitsStaircase r : Nat.Partition n → Prop)
  have hcard (p : Nat.Partition n) (hp : p ∈ fits) : p.parts.card ∈ Finset.range (r + 1) := by
    rw [Finset.mem_range]
    by_contra! h
    have hr : r < (decreasingParts p).length := by rw [length_decreasingParts]; omega
    have hb := (Finset.mem_filter.mp hp).2 r (by omega)
    rw [List.getD_eq_getElem _ _ hr] at hb
    have hpos := p.parts_pos ((Multiset.mem_sort _).mp (List.getElem_mem hr))
    omega
  rw [trianglePartitionSeries, map_sum]
  simp only [triangularQBinomial, coeff_mk, ← Nat.cast_sum, Nat.cast_inj]
  rw [Finset.sum_congr rfl (g := fun s => (fits.filter fun p => p.parts.card = s).card)]
  · exact Finset.card_eq_sum_card_fiberwise hcard |>.symm
  · intro s _
    congr 1
    ext p
    simp only [fits, Finset.mem_filter, Finset.mem_univ, true_and, FitsStaircase]
    exact ⟨fun ⟨hc, hf⟩ => ⟨hc ▸ hf, hc⟩, fun ⟨hf, hc⟩ => ⟨hc, hc.symm ▸ hf⟩⟩

private theorem largestPart_le {n : ℕ} (p : Nat.Partition n) : p.parts.sup ≤ n :=
  Multiset.sup_le.mpr fun _ ha => Nat.Partition.le_of_mem_parts ha

private noncomputable abbrev firstColumnTerm (r : ℕ) : ℤ⟦X⟧ :=
  ((r + 2 : ℕ) : ℤ⟦X⟧) * X ^ (r + 2) * trianglePartitionSeries (r + 1)

private theorem coeff_firstColumnTerm (n r : ℕ) :
    coeff n (firstColumnTerm r) = (r + 2 : ℕ) * ((firstColumnFiber n r).card : ℤ) := by
  rw [firstColumnTerm, mul_assoc, coeff_natCast_mul, coeff_X_pow_mul']
  by_cases h : r + 2 ≤ n
  · rw [ite_eq_left h, coeff_trianglePartitionSeries, card_firstColumnFiber h]
  · have hz : firstColumnFiber n r = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun p _ hp => h ?_
      rw [← hp.2]
      exact largestPart_le p
    simp [h, hz]

private theorem hasSum_firstColumn (n : ℕ) :
    HasSum (fun r => coeff n (firstColumnTerm r))
      (∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n =>
        litCellsDecreasing p = p.parts.sup ∧ 2 ≤ p.parts.sup), (p.parts.sup : ℤ)) := by
  let admissible := Finset.univ.filter (fun p : Nat.Partition n =>
    litCellsDecreasing p = p.parts.sup ∧ 2 ≤ p.parts.sup)
  have hmap (p : Nat.Partition n) (_ : p ∈ admissible) :
      p.parts.sup - 2 ∈ Finset.range (n + 1) := by
    have := largestPart_le p
    rw [Finset.mem_range]
    omega
  have hfiber (r : ℕ) :
      admissible.filter (fun p => p.parts.sup - 2 = r) = firstColumnFiber n r := by
    ext p
    simp only [admissible, firstColumnFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hs : HasSum (fun r => coeff n (firstColumnTerm r))
      (∑ r ∈ Finset.range (n + 1), coeff n (firstColumnTerm r)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro r hr
    rw [firstColumnTerm, mul_assoc, coeff_natCast_mul, coeff_X_pow_mul', ite_eq_right (by
      simp only [Finset.mem_range] at hr
      omega), mul_zero]
  convert hs using 1
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => (p.parts.sup : ℤ))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hfiber, coeff_firstColumnTerm]
  calc
    _ = ∑ _p ∈ firstColumnFiber n r, ((r + 2 : ℕ) : ℤ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2.2]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Lit cells when only the first column is lit.** For a partition $p$ of $n$ with $\ell \ge 1$
parts $x_1 \ge x_2 \ge \cdots \ge x_\ell$, say that only the first column of its weakly
decreasing bargraph is lit when the number of lit cells of $p$ equals its largest part $x_1$,
that is, when $x_i + i - 1 \le x_1$ for $1 \le i \le \ell$. Let $F(q) \in \mathbb{Z}[[q]]$ be
the power series whose coefficient of $q^n$ is the sum of $x_1$ over the partitions of $n$ in
which only the first column is lit and $x_1 \ge 2$. For $r \ge 0$ let $T_q(r)$ be the
generating function of partitions contained in the triangle with column heights
$r, r - 1, \ldots, 1$. Then
$$F(q) = \sum_{r \ge 1} (r + 1) q^{r+1} T_q(r),$$
where the sum converges coefficientwise.

The condition $x_1 \ge 2$ is the range $r \ge 1$ of the paper's
$T(u, q) = \sum_{r \ge 1} u^{r+1} q^{r+1} T_q(r)$; among the partitions in which only the first
column is lit it excludes only $(1)$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 6 (`integers-2024-A56-prop-6`). -/
public theorem litCellsDecreasing_firstColumn_generatingFunction :
    (mk fun n => ∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n =>
        litCellsDecreasing p = p.parts.sup ∧ 2 ≤ p.parts.sup), (p.parts.sup : ℤ)) =
      ∑' r : ℕ, ((r + 2 : ℕ) : ℤ⟦X⟧) * X ^ (r + 2) * trianglePartitionSeries (r + 1) := by
  symm
  apply HasSum.tsum_eq
  apply (hasSum_iff_hasSum_coeff ℤ).mpr
  intro n
  simpa only [coeff_mk] using hasSum_firstColumn n

private theorem part_add_index_le_sum (l : List ℕ) (hpos : ∀ a ∈ l, 0 < a)
    {i : ℕ} (hi : i < l.length) : l[i] + i ≤ l.sum := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      have h := ih (fun b hb => hpos b (List.mem_cons_of_mem _ hb))
        (i := i) (by simpa using hi)
      have ha := hpos a (List.mem_cons_self ..)
      simp only [List.getElem_cons_succ, List.sum_cons]
      omega

-- Positive parts before a column account for its index as well as its height.
private theorem litCellsDecreasing_le_size {n : ℕ} (p : Nat.Partition n) :
    litCellsDecreasing p ≤ n := by
  apply (litCellsDecreasing_le_iff p).mpr
  intro i hi
  have hi' : i < (decreasingParts p).length := by rwa [length_decreasingParts]
  rw [List.getD_eq_getElem _ _ hi']
  have hs : (decreasingParts p).sum = n := by
    rw [← Multiset.sum_coe, decreasingParts, Multiset.sort_eq, p.parts_sum]
  exact (part_add_index_le_sum _ (fun a ha => p.parts_pos ((Multiset.mem_sort _).mp ha))
    hi').trans_eq hs

private noncomputable def litCellsTail (k : ℕ) : ℤ⟦X⟧ :=
  (mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) - trianglePartitionSeries k

-- The coefficient is the number of partitions whose lit-cell count exceeds the threshold.
private theorem coeff_litCellsTail (n k : ℕ) :
    coeff n (litCellsTail k) =
      ∑ p : Nat.Partition n, if k < litCellsDecreasing p then 1 else 0 := by
  rw [litCellsTail, map_sub, coeff_mk, coeff_trianglePartitionSeries]
  have hfilter : (Finset.univ.filter (FitsStaircase k : Nat.Partition n → Prop)) =
      Finset.univ.filter (fun p : Nat.Partition n => litCellsDecreasing p ≤ k) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (litCellsDecreasing_le_iff p).symm
  rw [hfilter, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Nat.Partition n))) (p := fun p => litCellsDecreasing p ≤ k)
  simp only [not_le, Finset.card_univ] at hcard
  have hcardZ : ((Finset.univ.filter (fun p : Nat.Partition n =>
      litCellsDecreasing p ≤ k)).card : ℤ) +
      ((Finset.univ.filter (fun p : Nat.Partition n =>
        k < litCellsDecreasing p)).card : ℤ) = Fintype.card (Nat.Partition n) := by
    exact_mod_cast hcard
  omega

private theorem hasSum_litCellsTail (n : ℕ) :
    HasSum (fun k => coeff n (litCellsTail k))
      (∑ p : Nat.Partition n, (litCellsDecreasing p : ℤ)) := by
  have hsum : HasSum (fun k => coeff n (litCellsTail k))
      (∑ k ∈ Finset.range n, coeff n (litCellsTail k)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hnk : n ≤ k := Nat.le_of_not_lt (fun h => hk (Finset.mem_range.mpr h))
    rw [coeff_litCellsTail]
    exact Finset.sum_eq_zero fun p _ =>
      ite_eq_right (not_lt_of_ge ((litCellsDecreasing_le_size p).trans hnk))
  convert hsum using 1
  simp_rw [coeff_litCellsTail]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun k => k < litCellsDecreasing p) =
      Finset.range (litCellsDecreasing p) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨h.trans_le (litCellsDecreasing_le_size p), h⟩⟩
  simp [hf]

/-- **Generating function for lit cells of weakly decreasing bargraphs.** Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, for $k \ge 0$ let $T_q(k)$
be the generating function of partitions contained in the triangle with column heights
$k, k - 1, \ldots, 1$ (so $T_q(0) = 1$), and let $L(q) \in \mathbb{Z}[[q]]$ be the power series
whose coefficient of $q^n$ is the total number of lit cells over all partitions of $n$ drawn as
weakly decreasing bargraphs. Then
$$L(q) = \sum_{k \ge 0} \bigl(P(q) - T_q(k)\bigr),$$
where the sum converges coefficientwise.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Theorem 1, eq. (16)
(`integers-2024-A56-thm-1`). -/
public theorem litCellsDecreasing_generatingFunction :
    mk (fun n => ∑ p : Nat.Partition n, (litCellsDecreasing p : ℤ)) =
      ∑' k : ℕ, ((mk fun n => (Fintype.card (Nat.Partition n) : ℤ)) -
        trianglePartitionSeries k) := by
  symm
  apply HasSum.tsum_eq
  apply (hasSum_iff_hasSum_coeff ℤ).mpr
  intro n
  simpa only [coeff_mk, litCellsTail] using hasSum_litCellsTail n

end

end MetaMathlibExt
