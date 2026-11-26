/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic.LinearCombination

/-!
# Combinations without specified separations

For forbidden differences 1 and 4, the next membership bit depends only on the last four
bits. The eight reachable windows give a system of linear equations for the generating series.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Restricted combinations.** For a finite set $Q$ of natural numbers and $n, k \ge 0$, the
restricted combinations are the $k$-element subsets $s$ of $\{1, \dots, n\}$ such that
$b - a \notin Q$ for all $a, b \in s$ with $a < b$. Since only distinct elements are compared,
whether $0 \in Q$ makes no difference.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinations (Q : Finset ℕ) (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 1 n).powersetCard k).filter fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q

/-- **Number of restricted combinations.** For a finite set $Q$ of natural numbers and natural
numbers $n$ and $k$, $S^Q_{n,k}$ is the number of $k$-subsets of $\{1, \dots, n\}$ in which no
two distinct elements differ by an element of $Q$.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationCount (Q : Finset ℕ) (n k : ℕ) : ℕ :=
  (restrictedCombinations Q n k).card

/-- **Number of subsets avoiding a set of differences.** For a finite set $Q$ of natural numbers
and $n \ge 0$, $S^Q_n$ is the number of subsets of $\{1, \dots, n\}$ in which no two distinct
elements differ by an element of $Q$. That is, $S^Q_n = \sum_{k=0}^{n} S^Q_{n,k}$, where
$S^Q_{n,k}$ is the number of such subsets with $k$ elements.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Section 1. -/
public def restrictedCombinationTotal (Q : Finset ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), restrictedCombinationCount Q n k

end

namespace OneFour

/-- The four preceding membership bits, oldest first. -/
private structure Window where
  first : Bool
  second : Bool
  third : Bool
  fourth : Bool

private def Window.shift (w : Window) (b : Bool) : Window :=
  ⟨w.second, w.third, w.fourth, b⟩

private def Window.allows (w : Window) (b : Bool) : Bool :=
  !b || (!w.first && !w.fourth)

private def zeroWindow : Window := ⟨false, false, false, false⟩

private def Separated (s : Finset ℕ) : Prop :=
  ∀ a ∈ s, a + 1 ∉ s ∧ a + 4 ∉ s

private instance (s : Finset ℕ) : Decidable (Separated s) :=
  inferInstanceAs (Decidable (∀ a ∈ s, a + 1 ∉ s ∧ a + 4 ∉ s))

private theorem separated_iff (s : Finset ℕ) :
    Separated s ↔ ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ ({1, 4} : Finset ℕ) := by
  simp only [Separated, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h a ha b hb hab hd
    rcases hd with hd | hd
    · exact (h a ha).1 (by rwa [show a + 1 = b by omega])
    · exact (h a ha).2 (by rwa [show a + 4 = b by omega])
  · intro h a ha
    exact ⟨fun hb => h a ha _ hb (by omega) (Or.inl (by omega)),
      fun hb => h a ha _ hb (by omega) (Or.inr (by omega))⟩

/-- A subset of the suffix is indicated by its occupied positions, numbered from 1.
The four implications rule out conflicts across the boundary with the preceding window. -/
private def Compatible (w : Window) (s : Finset ℕ) : Prop :=
  Separated s ∧ (w.first = true → 1 ∉ s) ∧ (w.second = true → 2 ∉ s) ∧
    (w.third = true → 3 ∉ s) ∧ (w.fourth = true → 1 ∉ s ∧ 4 ∉ s)

private instance (w : Window) (s : Finset ℕ) : Decidable (Compatible w s) := by
  unfold Compatible
  infer_instance

private def words (w : Window) (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (Compatible w)

private theorem mem_words {w : Window} {n : ℕ} {s : Finset ℕ} :
    s ∈ words w n ↔ s ⊆ Finset.Icc 1 n ∧ Compatible w s := by
  simp only [words, Finset.mem_filter, Finset.mem_powerset]

private theorem total_eq_card_words (n : ℕ) :
    restrictedCombinationTotal {1, 4} n = (words zeroWindow n).card := by
  unfold restrictedCombinationTotal restrictedCombinationCount
  have hcard : (↑(words zeroWindow n) : Set (Finset ℕ)).MapsTo
      Finset.card (Finset.range (n + 1)) := by
    intro s hs
    have hle := Finset.card_le_card (mem_words.mp hs).1
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hle
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hcard]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  ext s
  simp only [restrictedCombinations, Finset.mem_filter, Finset.mem_powersetCard, mem_words,
    Compatible, zeroWindow, Bool.false_eq_true, false_implies, and_true, separated_iff]
  tauto

private def succEmbedding : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

/-- Prepend a bit and shift all occupied suffix positions by one. -/
private def prepend (b : Bool) (s : Finset ℕ) : Finset ℕ :=
  if b then insert 1 (s.map succEmbedding) else s.map succEmbedding

private theorem mem_prepend {b : Bool} {s : Finset ℕ} {a : ℕ} :
    a ∈ prepend b s ↔ (a = 1 ∧ b = true) ∨ ∃ i ∈ s, a = i + 1 := by
  cases b <;> simp [prepend, succEmbedding, Finset.mem_map, eq_comm]

private theorem one_mem_prepend {b : Bool} {s : Finset ℕ} (hs : 0 ∉ s) :
    1 ∈ prepend b s ↔ b = true := by
  simp [mem_prepend, hs]

private theorem succ_mem_prepend {b : Bool} {s : Finset ℕ} {a : ℕ} (ha : 0 < a) :
    a + 1 ∈ prepend b s ↔ a ∈ s := by
  simp [mem_prepend, Nat.ne_of_gt ha]

private theorem separated_prepend {b : Bool} {s : Finset ℕ} (hs : 0 ∉ s) :
    Separated (prepend b s) ↔ Separated s ∧ (b = true → 1 ∉ s ∧ 4 ∉ s) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a ha
      have ha' : 0 < a := Nat.pos_of_ne_zero (fun he => hs (he ▸ ha))
      have hh := h (a + 1) ((succ_mem_prepend ha').2 ha)
      exact ⟨fun ha₁ => hh.1 ((succ_mem_prepend (by omega)).2 ha₁),
        fun ha₄ => hh.2 (by simpa [Nat.add_right_comm a 4 1] using
          (succ_mem_prepend (by omega)).2 ha₄)⟩
    · intro hb
      have hh := h 1 ((one_mem_prepend hs).2 hb)
      exact ⟨fun h1 => hh.1 ((succ_mem_prepend (by decide : 0 < 1)).2 h1),
        fun h4 => hh.2 ((succ_mem_prepend (by decide : 0 < 4)).2 h4)⟩
  · rintro ⟨h, hfirst⟩ a ha
    rcases mem_prepend.mp ha with ⟨rfl, hb⟩ | ⟨i, hi, rfl⟩
    · exact ⟨fun h1 => (hfirst hb).1 ((succ_mem_prepend (by decide : 0 < 1)).1 h1),
        fun h4 => (hfirst hb).2 ((succ_mem_prepend (by decide : 0 < 4)).1 h4)⟩
    · have hh := h i hi
      exact ⟨fun h1 => hh.1 ((succ_mem_prepend (by omega)).1 h1),
        fun h4 => hh.2 ((succ_mem_prepend (by omega)).1
          (by simpa [Nat.add_right_comm i 4 1] using h4))⟩

private theorem compatible_prepend {w : Window} {b : Bool} {s : Finset ℕ} (hs : 0 ∉ s) :
    Compatible w (prepend b s) ↔ w.allows b = true ∧ Compatible (w.shift b) s := by
  cases b <;> obtain ⟨a, c, d, e⟩ := w <;> cases a <;> cases e <;>
    simp [Compatible, Window.allows, Window.shift, separated_prepend hs, one_mem_prepend hs,
      succ_mem_prepend (by decide : 0 < 1), succ_mem_prepend (by decide : 0 < 2),
      succ_mem_prepend (by decide : 0 < 3), and_assoc, and_left_comm, and_comm]

private theorem prepend_subset {b : Bool} {s : Finset ℕ} {n : ℕ}
    (hs : s ⊆ Finset.Icc 1 n) : prepend b s ⊆ Finset.Icc 1 (n + 1) := by
  intro a ha
  rcases mem_prepend.mp ha with ⟨rfl, _⟩ | ⟨i, hi, rfl⟩
  · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  · have := Finset.mem_Icc.mp (hs hi)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

private theorem recover_prepend {b : Bool} {t : Finset ℕ} {n : ℕ}
    (ht : t ⊆ Finset.Icc 1 (n + 1)) (hb : 1 ∈ t ↔ b = true) :
    ∃ s ⊆ Finset.Icc 1 n, prepend b s = t := by
  let s := (t.erase 1).preimage succEmbedding succEmbedding.injective.injOn
  have hs (i : ℕ) : i ∈ s ↔ i + 1 ≠ 1 ∧ i + 1 ∈ t := by
    rw [Finset.mem_preimage, Finset.mem_erase]
    rfl
  refine ⟨s, ?_, ?_⟩
  · intro i hi
    obtain ⟨hne, hmem⟩ := (hs i).1 hi
    have := Finset.mem_Icc.mp (ht hmem)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · ext a
    simp only [mem_prepend, hs]
    constructor
    · rintro (⟨rfl, h⟩ | ⟨i, ⟨_, hi⟩, rfl⟩)
      · exact hb.2 h
      · exact hi
    · intro ha
      by_cases he : a = 1
      · exact Or.inl ⟨he, hb.1 (he ▸ ha)⟩
      · have := (Finset.mem_Icc.mp (ht ha)).1
        exact Or.inr ⟨a - 1, ⟨by omega, by rwa [show a - 1 + 1 = a by omega]⟩, by omega⟩

private theorem card_words_filter (w : Window) (n : ℕ) (b : Bool) :
    ((words w (n + 1)).filter fun s => (1 ∈ s ↔ b = true)).card =
      if w.allows b then (words (w.shift b) n).card else 0 := by
  by_cases hb : w.allows b = true
  · rw [ite_eq_left hb]
    symm
    refine Finset.card_nbij (prepend b) ?_ ?_ ?_
    · intro s hs
      obtain ⟨hs, hc⟩ := mem_words.mp hs
      have h0 : 0 ∉ s := fun h => by simpa using (Finset.mem_Icc.mp (hs h)).1
      exact Finset.mem_filter.mpr
        ⟨mem_words.mpr ⟨prepend_subset hs, (compatible_prepend h0).2 ⟨hb, hc⟩⟩,
          one_mem_prepend h0⟩
    · intro s hs t ht he
      have h0s : 0 ∉ s := fun h => by simpa using (Finset.mem_Icc.mp ((mem_words.mp hs).1 h)).1
      have h0t : 0 ∉ t := fun h => by simpa using (Finset.mem_Icc.mp ((mem_words.mp ht).1 h)).1
      ext a
      by_cases ha : a = 0
      · simp [ha, h0s, h0t]
      · have hpos := Nat.pos_of_ne_zero ha
        rw [← succ_mem_prepend (b := b) hpos, he, succ_mem_prepend hpos]
    · intro t ht
      obtain ⟨ht, hbit⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht, hc⟩ := mem_words.mp ht
      obtain ⟨s, hs, rfl⟩ := recover_prepend ht hbit
      have h0 : 0 ∉ s := fun h => by simpa using (Finset.mem_Icc.mp (hs h)).1
      exact ⟨s, mem_words.mpr ⟨hs, ((compatible_prepend h0).1 hc).2⟩, rfl⟩
  · rw [ite_eq_right hb, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht, hbit⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht, hc⟩ := mem_words.mp ht
    obtain ⟨s, hs, rfl⟩ := recover_prepend ht hbit
    have h0 : 0 ∉ s := fun h => by simpa using (Finset.mem_Icc.mp (hs h)).1
    exact hb ((compatible_prepend h0).1 hc).1

private theorem card_words_succ (w : Window) (n : ℕ) :
    (words w (n + 1)).card = (words (w.shift false) n).card +
      if w.allows true then (words (w.shift true) n).card else 0 := by
  have hfalse : ((words w (n + 1)).filter fun s => 1 ∉ s).card =
      (words (w.shift false) n).card := by
    simpa [Window.allows] using card_words_filter w n false
  have htrue : ((words w (n + 1)).filter fun s => 1 ∈ s).card =
      if w.allows true then (words (w.shift true) n).card else 0 := by
    simpa using card_words_filter w n true
  rw [← hfalse, ← htrue]
  simpa only [add_comm] using
    (Finset.card_filter_add_card_filter_not (s := words w (n + 1)) (fun s => 1 ∈ s)).symm

private theorem card_words_zero (w : Window) : (words w 0).card = 1 := by
  have h : Compatible w ∅ := by simp [Compatible, Separated]
  simp [words, Finset.filter_singleton, h]

open PowerSeries in
private noncomputable def series (w : Window) : PowerSeries ℤ :=
  mk fun n => ((words w n).card : ℤ)

open PowerSeries in
private theorem series_eq (w : Window) :
    series w = 1 + X * (series (w.shift false) +
      if w.allows true then series (w.shift true) else 0) := by
  ext n
  cases n with
  | zero => simp [series, card_words_zero]
  | succ n =>
    simp only [map_add, coeff_one, Nat.succ_ne_zero, ite_false, zero_add, coeff_succ_X_mul,
      series, coeff_mk, card_words_succ, Nat.cast_add]
    split <;> simp_all

end OneFour

open OneFour in
/-- **Generating function for subsets avoiding differences 1 and 4.** Let $S^{\{1,4\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $4$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,
$$\Bigl(\sum_{n \ge 0} S^{\{1,4\}}_n x^n\Bigr)(1 - x - x^3 + x^4 - 2x^5 + x^6 - x^7) =
1 + x + x^2 + x^3 + 2x^4 + x^6.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,4\}}_n x^n$ as a quotient of the two
polynomials, with the denominator cleared.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Proposition 9. -/
public theorem restrictedCombinationTotal_one_four_genFun :
    PowerSeries.mk (fun n => (restrictedCombinationTotal {1, 4} n : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5 +
          PowerSeries.X ^ 6 - PowerSeries.X ^ 7) =
      1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 +
        PowerSeries.X ^ 6 := by
  simp_rw [total_eq_card_words]
  let x : PowerSeries ℤ := PowerSeries.X
  change series zeroWindow * (1 - x - x ^ 3 + x ^ 4 - 2 * x ^ 5 + x ^ 6 - x ^ 7) =
    1 + x + x ^ 2 + x ^ 3 + 2 * x ^ 4 + x ^ 6
  -- The empty window and the seven other windows without adjacent true bits.
  have h0000 := series_eq ⟨false, false, false, false⟩
  have h0001 := series_eq ⟨false, false, false, true⟩
  have h0010 := series_eq ⟨false, false, true, false⟩
  have h0100 := series_eq ⟨false, true, false, false⟩
  have h0101 := series_eq ⟨false, true, false, true⟩
  have h1000 := series_eq ⟨true, false, false, false⟩
  have h1001 := series_eq ⟨true, false, false, true⟩
  have h1010 := series_eq ⟨true, false, true, false⟩
  simp only [Window.shift, Window.allows, Bool.not_true, Bool.not_false, Bool.false_or,
    Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_true, ite_false, add_zero] at *
  -- Eliminate the seven nonempty windows from their transfer equations.
  unfold zeroWindow
  linear_combination (1 - x ^ 3 - x ^ 5) * h0000 + (x - x ^ 4 - x ^ 6) * h0001 +
    x ^ 2 * h0010 + (x ^ 3 + x ^ 5) * h0100 + x ^ 3 * h0101 +
    (x ^ 4 + x ^ 6) * h1000 + (x ^ 4 + x ^ 6) * h1001 + x ^ 4 * h1010

end MetaMathlibExt
