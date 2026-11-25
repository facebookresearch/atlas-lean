/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Multiset.Sort
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Partitions under a staircase

Triangular q-binomial coefficients enumerate partitions of a given length under a
staircase. Removing the bottom row gives their recurrence.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Parts of a partition in decreasing order.** For a partition $p$ of $n$ with $\ell$ parts,
this is the list $x_1 \ge x_2 \ge \cdots \ge x_\ell$ of the parts of $p$, each repeated according
to its multiplicity, sorted in weakly decreasing order.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 1 (weakly decreasing bargraphs). -/
public def decreasingParts {n : ℕ} (p : Nat.Partition n) : List ℕ :=
  p.parts.sort (· ≥ ·)

/-- **Triangular $q$-binomial coefficient.** For natural numbers $r$ and $s$, the triangular
$q$-binomial coefficient $t[r, s] \in \mathbb{Z}[[q]]$ is the power series whose coefficient of
$q^n$ is the number of partitions of $n$ with exactly $s$ parts $x_1 \ge \dots \ge x_s$ that fit
in the staircase with column heights $r, r - 1, \dots, r - s + 1$, that is, with
$x_i + (i - 1) \le r$ for $1 \le i \le s$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 4. -/
public noncomputable def triangularQBinomial (r s : ℕ) : ℤ⟦X⟧ :=
  mk fun n => ((Finset.univ.filter fun p : Nat.Partition n =>
    p.parts.card = s ∧ ∀ i < s, (decreasingParts p).getD i 0 + i ≤ r).card : ℤ)

/-- **Triangular $q$-binomial coefficients with no parts.** For every natural number $r$, the
triangular $q$-binomial coefficient satisfies $t[r, 0] = 1$: only the empty partition has no
parts.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Section 4, initial conditions (10). -/
public theorem triangularQBinomial_zero_right (r : ℕ) : triangularQBinomial r 0 = 1 := by
  ext n
  rw [triangularQBinomial, coeff_mk, coeff_one]
  split_ifs with h
  · subst h
    rw [Nat.cast_eq_one, Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext p
    simp [Subsingleton.elim p default]
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    have h0 : p.parts = 0 := Multiset.card_eq_zero.mp hp.1
    have := p.parts_sum
    rw [h0, Multiset.sum_zero] at this
    exact h this.symm

private theorem length_decreasingParts {n : ℕ} (p : Nat.Partition n) :
    (decreasingParts p).length = p.parts.card := by
  simp [decreasingParts]

private theorem getD_decreasingParts_pos {n i : ℕ} (p : Nat.Partition n)
    (hi : i < p.parts.card) : 0 < (decreasingParts p).getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa only [length_decreasingParts] using hi)]
  exact p.parts_pos ((Multiset.mem_sort _).mp (List.getElem_mem _))

private theorem decreasingParts_ofSums {n : ℕ} (l : List ℕ)
    (hsum : (l : Multiset ℕ).sum = n) (hsort : l.Pairwise (· ≥ ·)) :
    decreasingParts (Nat.Partition.ofSums n l hsum) = l.filter (· ≠ 0) := by
  rw [decreasingParts, Nat.Partition.ofSums_parts, Multiset.filter_coe, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (hsort.filter _)

-- Removing the zeros from a decreasing list only removes a suffix.
private theorem getD_filter_ne_zero {l : List ℕ} (hl : l.Pairwise (· ≥ ·)) (i : ℕ) :
    (l.filter (· ≠ 0)).getD i 0 = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hl
    by_cases h : a = 0
    · subst a
      rw [List.filter_cons_of_neg (p := fun x : ℕ ↦ decide (x ≠ 0)) (by decide)]
      have hf : l.filter (· ≠ 0) = [] := by
        simpa only [List.filter_eq_nil_iff, decide_eq_true_eq, not_not] using
          (fun b hb => Nat.eq_zero_of_le_zero (ha b hb) : ∀ b ∈ l, b = 0)
      rw [hf, List.getD_nil]
      cases i with
      | zero => rfl
      | succ j => simpa only [hf, List.getD_nil, List.getD_cons_succ] using ih hs j
    · rw [List.filter_cons_of_pos (p := fun x : ℕ ↦ decide (x ≠ 0)) (decide_eq_true h)]
      cases i with
      | zero => rfl
      | succ j => exact ih hs j

private theorem sum_map_succ (l : List ℕ) :
    (l.map Nat.succ).sum = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

private theorem sum_decreasingParts_sub_one {n : ℕ} (p : Nat.Partition n) :
    ((decreasingParts p).map (· - 1)).sum + p.parts.card = n := by
  have hmap : ((decreasingParts p).map (· - 1)).map Nat.succ = decreasingParts p := by
    calc
      _ = (decreasingParts p).map id := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a ha
        have hpos := p.parts_pos ((Multiset.mem_sort _).mp ha)
        simp only [Function.comp_apply, id_eq]
        omega
      _ = _ := List.map_id _
  rw [← length_decreasingParts, ← List.length_map (f := (· - 1)), ← sum_map_succ, hmap,
    ← Multiset.sum_coe, decreasingParts, Multiset.sort_eq, p.parts_sum]

private theorem getD_append_zeros (l : List ℕ) (k i : ℕ) :
    (l ++ List.replicate k 0).getD i 0 = l.getD i 0 := by
  by_cases h : i < l.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default l 0 (by omega)]
    simp [List.getD_eq_getElem?_getD]

-- At degree `n + s`, remove the bottom row. The target groups the resulting
-- partitions of `n` without yet separating them by their number of parts.
private theorem card_strip_bottom_row (r s n : ℕ) (hs : s ≤ r + 1) :
    (Finset.univ.filter fun p : Nat.Partition (n + s) =>
      p.parts.card = s ∧ ∀ i < s, (decreasingParts p).getD i 0 + i ≤ r + 1).card =
    (Finset.univ.filter fun p : Nat.Partition n =>
      p.parts.card ≤ s ∧ ∀ i < p.parts.card, (decreasingParts p).getD i 0 + i ≤ r).card := by
  let small := Finset.univ.filter fun p : Nat.Partition n =>
    p.parts.card ≤ s ∧ ∀ i < p.parts.card, (decreasingParts p).getD i 0 + i ≤ r
  have stripSum (p : Nat.Partition (n + s)) (hp : p.parts.card = s) :
      (((decreasingParts p).map (· - 1) : List ℕ) : Multiset ℕ).sum = n := by
    rw [Multiset.sum_coe]
    exact Nat.add_right_cancel (by simpa only [hp] using sum_decreasingParts_sub_one p)
  let strip (p : Nat.Partition (n + s)) (hp : p.parts.card = s) :=
    Nat.Partition.ofSums n ((decreasingParts p).map (· - 1)) (stripSum p hp)
  have stripSorted (p : Nat.Partition (n + s)) :
      ((decreasingParts p).map (· - 1)).Pairwise (· ≥ ·) :=
    (Multiset.pairwise_sort _ _).map _ (fun _ _ h => Nat.sub_le_sub_right h 1)
  have stripList (p : Nat.Partition (n + s)) (hp : p.parts.card = s) :
      decreasingParts (strip p hp) = ((decreasingParts p).map (· - 1)).filter (· ≠ 0) :=
    decreasingParts_ofSums _ _ (stripSorted p)
  have stripGet (p : Nat.Partition (n + s)) (hp : p.parts.card = s) (i : ℕ) :
      (decreasingParts (strip p hp)).getD i 0 = (decreasingParts p).getD i 0 - 1 := by
    rw [stripList p hp, getD_filter_ne_zero (stripSorted p)]
    exact List.getD_map _ 0 (· - 1)
  change _ = small.card
  refine Finset.card_bij (fun p hp => strip p (Finset.mem_filter.mp hp).2.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hcard, hfit⟩ := (Finset.mem_filter.mp hp).2
    have hlen : (strip p hcard).parts.card ≤ s := by
      rw [← length_decreasingParts, stripList p hcard]
      simpa only [List.length_map, length_decreasingParts, hcard] using
        (List.length_filter_le (p := fun x : ℕ ↦ decide (x ≠ 0))
          (l := (decreasingParts p).map (· - 1)))
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlen, ?_⟩
    intro i hi
    have his : i < s := hi.trans_le hlen
    have hpos := getD_decreasingParts_pos p (hcard ▸ his)
    rw [stripGet p hcard]
    specialize hfit i his
    omega
  · intro p hp q hq h
    have hp' := (Finset.mem_filter.mp hp).2.1
    have hq' := (Finset.mem_filter.mp hq).2.1
    suffices he : decreasingParts p = decreasingParts q by
      apply Nat.Partition.ext
      simpa only [decreasingParts, Multiset.sort_eq] using
        congrArg (fun l : List ℕ => (l : Multiset ℕ)) he
    apply List.ext_getElem
    · simp only [length_decreasingParts, hp', hq']
    · intro i hip hiq
      rw [← List.getD_eq_getElem _ 0 hip, ← List.getD_eq_getElem _ 0 hiq]
      have hi := congrArg (fun a => (decreasingParts a).getD i 0) h
      change (decreasingParts (strip p hp')).getD i 0 =
        (decreasingParts (strip q hq')).getD i 0 at hi
      rw [stripGet p hp', stripGet q hq'] at hi
      have hp0 := getD_decreasingParts_pos p (by simpa only [length_decreasingParts] using hip)
      have hq0 := getD_decreasingParts_pos q (by simpa only [length_decreasingParts] using hiq)
      omega
  · intro q hq
    change q ∈ small at hq
    obtain ⟨hcard, hfit⟩ := (Finset.mem_filter.mp hq).2
    -- Pad on the right with zeros, then add one to all `s` entries.
    let padded := decreasingParts q ++ List.replicate (s - q.parts.card) 0
    let raised := padded.map Nat.succ
    have hlen : padded.length = s := by
      simp only [padded, List.length_append, length_decreasingParts, List.length_replicate]
      omega
    have hsum : (raised : Multiset ℕ).sum = n + s := by
      rw [Multiset.sum_coe, show raised = padded.map Nat.succ from rfl, sum_map_succ, hlen]
      have hqsum : (decreasingParts q).sum = n := by
        rw [← Multiset.sum_coe, decreasingParts, Multiset.sort_eq, q.parts_sum]
      simp [padded, hqsum]
    have hsort : padded.Pairwise (· ≥ ·) := by
      refine List.pairwise_append.mpr ⟨Multiset.pairwise_sort _ _,
        List.pairwise_replicate_of_refl, ?_⟩
      intro _ _ b hb
      obtain rfl := List.eq_of_mem_replicate hb
      exact Nat.zero_le _
    let p := Nat.Partition.ofSums (n + s) raised hsum
    have hp : decreasingParts p = raised := by
      rw [decreasingParts_ofSums _ _ (hsort.map _ (fun _ _ h => Nat.succ_le_succ h))]
      exact List.filter_eq_self.mpr (by simp)
    have hpCard : p.parts.card = s := by
      rw [← length_decreasingParts, hp, List.length_map, hlen]
    have hmem : p ∈ Finset.univ.filter (fun p : Nat.Partition (n + s) =>
        p.parts.card = s ∧ ∀ i < s, (decreasingParts p).getD i 0 + i ≤ r + 1) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpCard, ?_⟩
      intro i hi
      have hir : i < raised.length := by simpa only [raised, List.length_map, hlen] using hi
      have hget : raised.getD i 0 = Nat.succ (padded.getD i 0) := by
        calc
          _ = raised.getD i 1 := by rw [List.getD_eq_getElem _ 0 hir, List.getD_eq_getElem _ 1 hir]
          _ = _ := List.getD_map padded 0 Nat.succ
      rw [hp, hget, getD_append_zeros]
      by_cases hiq : i < q.parts.card
      · specialize hfit i hiq
        omega
      · have hlenq : (decreasingParts q).length ≤ i := by
          simpa only [length_decreasingParts] using not_lt.mp hiq
        rw [List.getD_eq_default _ _ hlenq]
        omega
    refine ⟨p, hmem, ?_⟩
    have hfilter : (padded.filter (· ≠ 0)) = decreasingParts q := by
      rw [show padded = decreasingParts q ++ List.replicate (s - q.parts.card) 0 from rfl,
        List.filter_append]
      have hpos : (decreasingParts q).filter (· ≠ 0) = decreasingParts q := by
        refine List.filter_eq_self.mpr fun a ha => decide_eq_true ?_
        exact (q.parts_pos ((Multiset.mem_sort _).mp ha)).ne'
      have hzeros : (List.replicate (s - q.parts.card) (0 : ℕ)).filter (· ≠ 0) = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_not]
        exact fun _ hb => List.eq_of_mem_replicate hb
      simp only [hpos, hzeros, List.append_nil]
    apply Nat.Partition.ext
    change (strip p hpCard).parts = q.parts
    rw [← Multiset.sort_eq (s := (strip p hpCard).parts) (· ≥ ·)]
    change (decreasingParts (strip p hpCard) : Multiset ℕ) = q.parts
    rw [stripList p hpCard, hp, show raised = padded.map Nat.succ from rfl, List.map_map]
    simp only [Function.comp_def, Nat.succ_sub_one, (show (fun x : ℕ => x) = id from rfl),
      List.map_id, hfilter, decreasingParts, Multiset.sort_eq]

private theorem triangularQBinomial_outside (r s : ℕ) (hrs : r < s) :
    triangularQBinomial r s = 0 := by
  ext n
  rw [triangularQBinomial, coeff_mk, map_zero, Nat.cast_eq_zero, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro p _ ⟨hcard, hfit⟩
  have hi : r < p.parts.card := hcard ▸ hrs
  have hpos := getD_decreasingParts_pos p hi
  have hbound := hfit r hrs
  omega

private theorem triangularQBinomial_step (r s : ℕ) (hs : s ≤ r + 1) :
    triangularQBinomial (r + 1) s =
      X ^ s * ∑ i ∈ Finset.range (s + 1), triangularQBinomial r i := by
  ext d
  rw [coeff_X_pow_mul']
  by_cases hd : s ≤ d
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hd
    rw [ite_eq_left hd, Nat.add_sub_cancel_left, Nat.add_comm s n]
    simp only [map_sum, triangularQBinomial, coeff_mk, ← Nat.cast_sum, Nat.cast_inj]
    rw [card_strip_bottom_row r s n hs]
    let fits := Finset.univ.filter fun p : Nat.Partition n =>
      ∀ j < p.parts.card, (decreasingParts p).getD j 0 + j ≤ r
    rw [Finset.sum_congr rfl (g := fun i => (fits.filter fun p => p.parts.card = i).card)]
    · rw [Finset.sum_card_fiberwise_eq_card_filter]
      congr 1
      ext p
      simp only [fits, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      exact ⟨fun ⟨hc, hf⟩ => ⟨hf, Nat.lt_succ_of_le hc⟩,
        fun ⟨hf, hc⟩ => ⟨Nat.le_of_lt_succ hc, hf⟩⟩
    · intro i _
      congr 1
      ext p
      simp only [fits, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h, hf⟩ => ⟨h ▸ hf, h⟩, fun ⟨hf, h⟩ => ⟨h, h.symm ▸ hf⟩⟩
  · rw [ite_eq_right hd, triangularQBinomial, coeff_mk, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro p _ hp
    have h := sum_decreasingParts_sub_one p
    omega

/-- **Recursion for triangular $q$-binomial coefficients.** The triangular $q$-binomial
coefficients $t[r, s] \in \mathbb{Z}[[q]]$ satisfy the recursion
$t[r, s] = q^s \sum_{i=0}^{s} t[r - 1, i]$ for all natural numbers $r \ge 1$ and $s \le r$,
together with the initial conditions $t[1, 1] = q$, $t[2, 1] = q(1 + q)$, $t[r, 0] = 1$ for
every $r$, and $t[r, s] = 0$ whenever $r < s$.

The recursion is stated for $s \le r$ only: for $s > r$ the left side is $0$, while the right
side is $q^s \sum_{i=0}^{r-1} t[r - 1, i] \ne 0$; for example $t[1, 2] = 0$ but
$q^2 (t[0, 0] + t[0, 1] + t[0, 2]) = q^2$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 3, eqs. (9), (10)
(`integers-2024-A56-prop-3`). -/
public theorem triangularQBinomial_recursion :
    (∀ r s : ℕ, s ≤ r + 1 →
      triangularQBinomial (r + 1) s = X ^ s * ∑ i ∈ Finset.range (s + 1), triangularQBinomial r i) ∧
    triangularQBinomial 1 1 = X ∧ triangularQBinomial 2 1 = X * (1 + X) ∧
    (∀ r, triangularQBinomial r 0 = 1) ∧ ∀ r s, r < s → triangularQBinomial r s = 0 := by
  have h11 : triangularQBinomial 1 1 = X := by
    rw [triangularQBinomial_step 0 1 (by decide)]
    simp [Finset.sum_range_succ, triangularQBinomial_zero_right,
      triangularQBinomial_outside 0 1 (by decide)]
  refine ⟨triangularQBinomial_step, h11, ?_, triangularQBinomial_zero_right,
    triangularQBinomial_outside⟩
  rw [triangularQBinomial_step 1 1 (by decide)]
  simp [Finset.sum_range_succ, triangularQBinomial_zero_right, h11]

private noncomputable abbrev rectangleSeries (r s : ℕ) : ℤ⟦X⟧ :=
  MathlibExt.gaussBinom X (r + s) s

private noncomputable abbrev staircaseSeries (r s : ℕ) : ℤ⟦X⟧ :=
  ∑ j ∈ Finset.range (s + 1), triangularQBinomial r j

private theorem rectangleSeries_step (r s : ℕ) :
    rectangleSeries (r + 1) (s + 1) =
      rectangleSeries (r + 1) s + X ^ (s + 1) * rectangleSeries r (s + 1) := by
  unfold rectangleSeries
  rw [show r + 1 + (s + 1) = (r + 1 + s) + 1 by omega, MathlibExt.gaussBinom_succ_succ,
    show r + (s + 1) = r + 1 + s by omega]

private theorem staircaseSeries_saturates (r s : ℕ) (h : r ≤ s) :
    staircaseSeries r s = staircaseSeries r r := by
  symm
  exact Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj =>
    triangularQBinomial_outside r j (by simpa using hj)

-- The `i`th column is the first to exceed the staircase. It has height `r + 2 - i`
-- (the preceding column fits). Above the common base of height `r + 1 - i` is a
-- full-width staircase of height `i - 1`; the first violation adds one more cell.
-- To its right is a rectangle with at most `s - i` parts.
private noncomputable def firstViolation (r s i : ℕ) : ℤ⟦X⟧ :=
  if i ≤ s then
    triangularQBinomial (i - 1) (i - 1) * X ^ (1 + i * (r + 1 - i)) *
      rectangleSeries (r + 2 - i) (s - i)
  else 0

private noncomputable abbrev violationSeries (r s : ℕ) : ℤ⟦X⟧ :=
  ∑ i ∈ Finset.Icc 2 (r + 1), firstViolation r s i

-- Pascal's rule for the remaining rectangle propagates each existing first violation.
private theorem firstViolation_step (r s i : ℕ) (hi : i ≤ r + 1) :
    firstViolation (r + 1) (s + 1) i =
      firstViolation (r + 1) s i + X ^ (s + 1) * firstViolation r (s + 1) i := by
  by_cases h : i ≤ s + 1
  · have hw : r + 1 + 2 - i = (r + 2 - i) + 1 := by omega
    have hp : (X : ℤ⟦X⟧) ^ (1 + i * (r + 1 + 1 - i)) =
        X ^ (1 + i * (r + 1 - i)) * X ^ i := by
      rw [← pow_add, show r + 1 + 1 - i = (r + 1 - i) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
    by_cases hs : i ≤ s
    · have hn : s + 1 - i = (s - i) + 1 := by omega
      have hx : (X : ℤ⟦X⟧) ^ i * X ^ (s + 1 - i) = X ^ (s + 1) := by
        rw [← pow_add, show i + (s + 1 - i) = s + 1 by omega]
      simp only [firstViolation, ite_eq_left h, ite_eq_left hs, hw, hp]
      rw [hn, rectangleSeries_step, ← hn]
      calc
        _ = triangularQBinomial (i - 1) (i - 1) * X ^ (1 + i * (r + 1 - i)) * X ^ i *
              rectangleSeries ((r + 2 - i) + 1) (s - i) +
            triangularQBinomial (i - 1) (i - 1) * X ^ (1 + i * (r + 1 - i)) *
              (X ^ i * X ^ (s + 1 - i)) * rectangleSeries (r + 2 - i) (s + 1 - i) := by ring
        _ = _ := by rw [hx]; ring
    · simp only [firstViolation, ite_eq_left h, ite_eq_right hs, hp,
        show s + 1 - i = 0 by omega, rectangleSeries, MathlibExt.gaussBinom_zero_right, mul_one,
        zero_add]
      rw [show i = s + 1 by omega]
      ring
  · have hs : ¬ i ≤ s := by omega
    simp [firstViolation, h, hs]

-- At the new possible exit `i = r + 2`, the tail rectangle has height one.
-- Its increment consists of a row of ones, and the fitting prefix is saturated.
private theorem firstViolation_boundary (r s : ℕ) :
    firstViolation (r + 1) (s + 1) (r + 2) = firstViolation (r + 1) s (r + 2) +
      if r < s then X ^ (s + 1) * staircaseSeries r (s + 1) else 0 := by
  by_cases h : r < s
  · have hdiag : triangularQBinomial (r + 1) (r + 1) = X ^ (r + 1) * staircaseSeries r r := by
      calc
        _ = X ^ (r + 1) * staircaseSeries r (r + 1) := triangularQBinomial_step r (r + 1) le_rfl
        _ = _ := by rw [staircaseSeries_saturates r (r + 1) (by omega)]
    have hx : (X : ℤ⟦X⟧) ^ (r + 1) * X * X ^ (s + 1 - (r + 2)) = X ^ (s + 1) := by
      rw [← pow_succ, ← pow_add, show r + 1 + 1 + (s + 1 - (r + 2)) = s + 1 by omega]
    simp only [firstViolation, ite_eq_left (show r + 2 ≤ s + 1 by omega), ite_eq_left h,
      show r + 1 + 1 - (r + 2) = 0 by omega, Nat.mul_zero, Nat.add_zero, pow_one,
      show r + 2 - 1 = r + 1 by omega, show r + 1 + 2 - (r + 2) = 1 by omega, hdiag]
    rw [staircaseSeries_saturates r (s + 1) (by omega)]
    by_cases hs : r + 2 ≤ s
    · have hn : s + 1 - (r + 2) = (s - (r + 2)) + 1 := by omega
      have hstep (j : ℕ) : rectangleSeries 1 (j + 1) = rectangleSeries 1 j + X ^ (j + 1) := by
        simpa [rectangleSeries] using rectangleSeries_step 0 j
      rw [ite_eq_left hs, hn, hstep, ← hn]
      calc
        _ = X ^ (r + 1) * staircaseSeries r r * X * rectangleSeries 1 (s - (r + 2)) +
            (X ^ (r + 1) * X * X ^ (s + 1 - (r + 2))) * staircaseSeries r r := by ring
        _ = _ := by rw [hx]
    · have hz : s + 1 - (r + 2) = 0 := by omega
      rw [ite_eq_right hs, zero_add, hz, show rectangleSeries 1 0 = 1 by simp [rectangleSeries],
        mul_one]
      rw [hz, pow_zero, mul_one] at hx
      rw [← hx]
      ring
  · simp [firstViolation, h, show ¬ r + 2 ≤ s + 1 by omega, show ¬ r + 2 ≤ s by omega]

-- Work with at most `s` positive parts (the mandatory bottom row is restored
-- at the end). Allow `s > r` here: when the staircase saturates, the new
-- boundary term accounts for the whole increment from that row count.
private theorem rectangleSeries_eq_staircase_add_violation (r s : ℕ) :
    rectangleSeries r s = staircaseSeries r s + violationSeries r s := by
  induction r generalizing s with
  | zero =>
    rw [staircaseSeries_saturates 0 s (Nat.zero_le _)]
    simp [rectangleSeries, staircaseSeries, triangularQBinomial_zero_right, violationSeries]
  | succ r ihr =>
    induction s with
    | zero => simp [rectangleSeries, staircaseSeries, triangularQBinomial_zero_right,
        violationSeries, firstViolation]
    | succ s ihs =>
      have hsplit : Finset.Icc 2 (r + 1 + 1) = insert (r + 2) (Finset.Icc 2 (r + 1)) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : r + 2 ∉ Finset.Icc 2 (r + 1) := by simp
      have hsum : ∑ i ∈ Finset.Icc 2 (r + 1), firstViolation (r + 1) (s + 1) i =
          (∑ i ∈ Finset.Icc 2 (r + 1), firstViolation (r + 1) s i) +
            X ^ (s + 1) * violationSeries r (s + 1) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i hi => firstViolation_step r s i (Finset.mem_Icc.mp hi).2
      have hv : violationSeries (r + 1) (s + 1) = violationSeries (r + 1) s +
          X ^ (s + 1) * violationSeries r (s + 1) +
            (if r < s then X ^ (s + 1) * staircaseSeries r (s + 1) else 0) := by
        simp only [violationSeries, hsplit, Finset.sum_insert hnot, hsum, firstViolation_boundary]
        ring
      rw [rectangleSeries_step, ihs, ihr (s + 1), hv,
        show staircaseSeries (r + 1) (s + 1) =
          staircaseSeries (r + 1) s + triangularQBinomial (r + 1) (s + 1) from
            Finset.sum_range_succ _ _]
      by_cases h : r < s
      · rw [triangularQBinomial_outside _ _ (by omega), ite_eq_left h]
        ring
      · rw [triangularQBinomial_step r (s + 1) (by omega), ite_eq_right h]
        ring

/-- **Triangular $q$-binomial coefficients via Gaussian binomials.** For natural numbers $r$ and
$s$ with $1 \le r$ and $s \le r$, the triangular $q$-binomial coefficient $t[r, s]$ satisfies
$$
t[r, s] = q^s \binom{r + s - 1}{s}_q - q^{s+1} \sum_{i=2}^{s} t[i - 1, i - 1] \,
q^{i(r - i)} \binom{r + 1 + s - 2i}{s - i}_q
$$
in $\mathbb{Z}[[q]]$, where $\binom{M}{k}_q$ denotes the Gaussian binomial coefficient.

In the range $s \le r$ every exponent and binomial index above is a natural number; for $s > r$
one has $t[r, s] = 0$.

Source: Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer
Partitions*, INTEGERS 24 (2024), Article A56, Proposition 4, eq. (12)
(`integers-2024-A56-prop-4`). -/
public theorem triangularQBinomial_eq_gaussBinom_sub {r s : ℕ} (hr : 1 ≤ r)
    (hs : s ≤ r) :
    triangularQBinomial r s =
      X ^ s * MathlibExt.gaussBinom X (r + s - 1) s -
        X ^ (s + 1) * ∑ i ∈ Finset.Icc 2 s, triangularQBinomial (i - 1) (i - 1) *
          X ^ (i * (r - i)) * MathlibExt.gaussBinom X (r + 1 + s - 2 * i) (s - i) := by
  cases r with
  | zero => omega
  | succ r =>
    have hcut : violationSeries r s = ∑ i ∈ Finset.Icc 2 s, firstViolation r s i := by
      symm
      apply Finset.sum_subset
      · intro i hi
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hs⟩
      · intro i hi his
        have h : ¬ i ≤ s := fun h => his (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, h⟩)
        simp [firstViolation, h]
    have hcorr : (X : ℤ⟦X⟧) ^ s * violationSeries r s =
        X ^ (s + 1) * ∑ i ∈ Finset.Icc 2 s, triangularQBinomial (i - 1) (i - 1) *
          X ^ (i * (r + 1 - i)) * MathlibExt.gaussBinom X (r + 1 + 1 + s - 2 * i) (s - i) := by
      rw [hcut, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have his := (Finset.mem_Icc.mp hi).2
      have htop : (r + 2 - i) + (s - i) = r + 1 + 1 + s - 2 * i := by omega
      rw [firstViolation, ite_eq_left his, rectangleSeries, htop, pow_add, pow_one, pow_succ]
      ring
    rw [triangularQBinomial_step r s hs, show r + 1 + s - 1 = r + s by omega]
    change X ^ s * staircaseSeries r s = X ^ s * rectangleSeries r s - _
    rw [rectangleSeries_eq_staircase_add_violation, mul_add, ← hcorr, add_sub_cancel_right]

end

end MetaMathlibExt
