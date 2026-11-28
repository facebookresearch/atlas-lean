/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RestrictedCombinations
public import MathlibExt.Combinatorics.Enumerative.SubwordShiftSet
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.LinearCombination

/-!
# Bivariate enumeration of combinations with well-based forbidden differences

For a finite set `Q` of positive forbidden differences satisfying the well-based split condition,
the count by board length and subset size has the rational bivariate generating function of
Allen's Corollary 24, including when `Q` is empty. The proof sorts subsets by their last occupied
position. For a nonempty allowed subset, a new largest element can be inserted exactly when its
gap from the previous largest element is allowed: the split condition ensures that the longer
gaps to earlier elements are then allowed too.

## References

* Michael A. Allen, *Connections Between Combinations Without Specified Separations and
  Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
  Sequences 28 (2025), Article 25.3.7, Section 5.1, Corollary 24 (equation (12), p. 22).
* Sergey Kitaev, *Independent Sets on Path-Schemes*, Journal of Integer Sequences 9 (2006),
  Article 06.2.2, Theorem 2 and its proof (the univariate formula and the reduction to
  consecutive gaps).
* Michael A. Allen, *Combinations without specified separations*, Communications in
  Combinatorics and Optimization 11(2) (2026), 695–711, Corollary 1 (the earlier
  univariate formula via tilings).
-/

namespace MetaMathlibExt

open Finset PowerSeries

local notation "Y" => (Polynomial.X : Polynomial ℤ)

private def boards (Q : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun s => ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q

private theorem mem_boards {Q s : Finset ℕ} {n : ℕ} :
    s ∈ boards Q n ↔ s ⊆ Icc 1 n ∧ ∀ a ∈ s, ∀ b ∈ s, a < b → b - a ∉ Q := by
  simp only [boards, mem_filter, mem_powerset]

private def endings (Q : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  (boards Q n).filter (n ∈ ·)

private noncomputable def weight (S : Finset (Finset ℕ)) : Polynomial ℤ :=
  ∑ s ∈ S, Y ^ s.card

private theorem sup_le_of_mem_boards {Q s : Finset ℕ} {n : ℕ} (hs : s ∈ boards Q n) :
    s.sup id ≤ n :=
  Finset.sup_le fun _ ha => (mem_Icc.mp ((mem_boards.mp hs).1 ha)).2

private theorem sup_eq_zero_iff_of_mem_boards {Q s : Finset ℕ} {n : ℕ} (hs : s ∈ boards Q n) :
    s.sup id = 0 ↔ s = ∅ := by
  refine ⟨fun h => eq_empty_iff_forall_notMem.mpr fun a ha => ?_, fun h => by simp [h]⟩
  have h₁ := (mem_Icc.mp ((mem_boards.mp hs).1 ha)).1
  have h₂ : a ≤ s.sup id := Finset.le_sup (f := id) ha
  omega

private theorem boards_zero (Q : Finset ℕ) : boards Q 0 = {∅} := by
  ext s
  rw [mem_boards, mem_singleton, Icc_eq_empty_of_lt (by decide : 0 < 1), subset_empty]
  exact ⟨And.left, fun h => ⟨h, by simp [h]⟩⟩

private theorem endings_zero (Q : Finset ℕ) : endings Q 0 = ∅ := by
  simp [endings, boards_zero]

private theorem weight_boards_succ (Q : Finset ℕ) (n : ℕ) :
    weight (boards Q (n + 1)) = weight (boards Q n) + weight (endings Q (n + 1)) := by
  have hfilter : (boards Q (n + 1)).filter (fun s => n + 1 ∉ s) = boards Q n := by
    ext s
    simp only [mem_filter, mem_boards]
    constructor
    · rintro ⟨⟨hsub, hsep⟩, hlast⟩
      refine ⟨fun a ha => ?_, hsep⟩
      have h := mem_Icc.mp (hsub ha)
      have hne : a ≠ n + 1 := fun e => hlast (e ▸ ha)
      exact mem_Icc.mpr ⟨h.1, by omega⟩
    · rintro ⟨hsub, hsep⟩
      refine ⟨⟨fun a ha => ?_, hsep⟩, fun h => ?_⟩
      · obtain ⟨h₁, h₂⟩ := mem_Icc.mp (hsub ha)
        exact mem_Icc.mpr ⟨h₁, by omega⟩
      · exact (Nat.not_succ_le_self n) (mem_Icc.mp (hsub h)).2
  unfold weight endings
  rw [← hfilter]
  exact (sum_filter_add_sum_filter_not (boards Q (n + 1)) (fun s => n + 1 ∈ s) _).symm.trans
    (add_comm _ _)

-- The only gap that must be checked on insertion is the gap from the old maximum.
private theorem separated_insert_iff {Q s : Finset ℕ} {n : ℕ} (hQ : IsWellBased Q)
    (hs : s ∈ boards Q n) :
    (∀ a ∈ insert (n + 1) s, ∀ b ∈ insert (n + 1) s, a < b → b - a ∉ Q) ↔
      s.sup id = 0 ∨ n + 1 - s.sup id ∉ Q := by
  by_cases he : s = ∅
  · simp [he]
  obtain ⟨p, hp, heq⟩ := s.exists_mem_eq_sup (nonempty_iff_ne_empty.mpr he) id
  have hb (a : ℕ) (ha : a ∈ s) : a ≤ n := (mem_Icc.mp ((mem_boards.mp hs).1 ha)).2
  have hp₁ := (mem_Icc.mp ((mem_boards.mp hs).1 hp)).1
  rw [heq]
  simp only [id_eq, show p ≠ 0 by omega, false_or]
  have hp₂ := hb p hp
  refine ⟨fun h => h p (mem_insert_of_mem hp) (n + 1) (mem_insert_self _ _) (by omega),
    fun h a ha b hb' hab => ?_⟩
  rcases mem_insert.mp ha with rfl | ha
  · rcases mem_insert.mp hb' with rfl | hb'
    · omega
    · have := hb b hb'
      omega
  rcases mem_insert.mp hb' with rfl | hb'
  · have hap : a ≤ p := by simpa only [heq, id_eq] using (Finset.le_sup (f := id) ha)
    rcases lt_or_eq_of_le hap with hlt | rfl
    · have hprev := (mem_boards.mp hs).2 a ha p hp hlt
      rw [show n + 1 - a = (p - a) + (n + 1 - p) by omega]
      exact hQ.add_notMem (by omega) (by omega) hprev h
    · exact h
  · exact (mem_boards.mp hs).2 a ha b hb' hab

private theorem endings_succ_eq_image {Q : Finset ℕ} (hQ : IsWellBased Q) (n : ℕ) :
    endings Q (n + 1) = ((boards Q n).filter
      (fun s => s.sup id = 0 ∨ n + 1 - s.sup id ∉ Q)).image (insert (n + 1)) := by
  ext t
  simp only [endings, mem_filter, mem_image]
  constructor
  · rintro ⟨ht, hlast⟩
    have hsub : t.erase (n + 1) ⊆ Icc 1 n := by
      intro a ha
      obtain ⟨hne, ha⟩ := mem_erase.mp ha
      have h := mem_Icc.mp ((mem_boards.mp ht).1 ha)
      exact mem_Icc.mpr ⟨h.1, by omega⟩
    have hsep : ∀ a ∈ t.erase (n + 1), ∀ b ∈ t.erase (n + 1), a < b → b - a ∉ Q :=
      fun a ha b hb => (mem_boards.mp ht).2 a (mem_of_mem_erase ha) b (mem_of_mem_erase hb)
    have hs := mem_boards.mpr ⟨hsub, hsep⟩
    refine ⟨_, ⟨hs, (separated_insert_iff hQ hs).mp ?_⟩, insert_erase hlast⟩
    rw [insert_erase hlast]
    exact (mem_boards.mp ht).2
  · rintro ⟨s, ⟨hs, hgap⟩, rfl⟩
    refine ⟨mem_boards.mpr ⟨?_, (separated_insert_iff hQ hs).mpr hgap⟩, mem_insert_self _ _⟩
    rw [insert_subset_iff]
    exact ⟨by simp, fun a ha =>
      let h := mem_Icc.mp ((mem_boards.mp hs).1 ha)
      mem_Icc.mpr ⟨h.1, Nat.le_succ_of_le h.2⟩⟩

-- A positive maximum `p` specifies the same subsets on any board at least that long.
private theorem boards_filter_sup {Q : Finset ℕ} {n p : ℕ} (hp : p ≤ n) (hp₀ : p ≠ 0) :
    (boards Q n).filter (fun s => s.sup id = p) = endings Q p := by
  ext s
  simp only [endings, mem_filter]
  constructor
  · rintro ⟨hs, hsup⟩
    have hne : s.Nonempty := nonempty_iff_ne_empty.mpr fun he => hp₀ (by simpa [he] using hsup.symm)
    obtain ⟨a, ha, heq⟩ := s.exists_mem_eq_sup hne id
    refine ⟨mem_boards.mpr ⟨fun b hb => ?_, (mem_boards.mp hs).2⟩, ?_⟩
    · exact mem_Icc.mpr ⟨(mem_Icc.mp ((mem_boards.mp hs).1 hb)).1,
        hsup ▸ Finset.le_sup (f := id) hb⟩
    · rwa [← hsup, heq]
  · rintro ⟨hs, hmem⟩
    refine ⟨mem_boards.mpr ⟨fun a ha => ?_, (mem_boards.mp hs).2⟩,
      (sup_le_of_mem_boards hs).antisymm (Finset.le_sup (f := id) hmem)⟩
    obtain ⟨h₁, h₂⟩ := mem_Icc.mp ((mem_boards.mp hs).1 ha)
    exact mem_Icc.mpr ⟨h₁, h₂.trans hp⟩

private theorem weight_endings_succ {Q : Finset ℕ} (hQ : IsWellBased Q) (n : ℕ) :
    weight (endings Q (n + 1)) = Y * (1 + ∑ p ∈ range (n + 1),
      if n + 1 - p ∈ Q then 0 else weight (endings Q p)) := by
  classical
  let U := (boards Q n).filter (fun s => s.sup id = 0 ∨ n + 1 - s.sup id ∉ Q)
  have htop {s : Finset ℕ} (hs : s ∈ U) : n + 1 ∉ s := fun h =>
    (Nat.not_succ_le_self n) (mem_Icc.mp ((mem_boards.mp (mem_filter.mp hs).1).1 h)).2
  have hins : Set.InjOn (insert (n + 1)) (U : Set (Finset ℕ)) := by
    intro s hs t ht h
    have h' := congrArg (fun u : Finset ℕ => u.erase (n + 1)) h
    simpa only [erase_insert (htop hs), erase_insert (htop ht)] using h'
  have hmaps (s : Finset ℕ) (hs : s ∈ U) : s.sup id ∈ range (n + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (sup_le_of_mem_boards (mem_filter.mp hs).1))
  rw [endings_succ_eq_image hQ, weight, sum_image hins]
  change (∑ s ∈ U, Y ^ (insert (n + 1) s).card) = _
  calc
    _ = ∑ s ∈ U, Y * Y ^ s.card :=
      sum_congr rfl fun s hs => by rw [card_insert_of_notMem (htop hs), pow_succ']
    _ = _ := by
      rw [← mul_sum, ← sum_fiberwise_of_maps_to hmaps]
      congr 1
      have hfiber (p : ℕ) (hp : p ∈ range (n + 1)) :
          (∑ s ∈ U.filter (fun s => s.sup id = p), Y ^ s.card) =
            (if p = 0 then 1 else 0) +
              if n + 1 - p ∈ Q then 0 else weight (endings Q p) := by
        by_cases hp₀ : p = 0
        · subst p
          have h : U.filter (fun s => s.sup id = 0) = {∅} := by
            ext s
            simp only [U, mem_filter, mem_singleton]
            exact ⟨fun hs => (sup_eq_zero_iff_of_mem_boards hs.1.1).mp hs.2, fun hs => by
              subst s
              simp [mem_boards]⟩
          rw [h]
          simp [endings_zero, weight]
        · have h' : U.filter (fun s => s.sup id = p) =
              (endings Q p).filter (fun _ => n + 1 - p ∉ Q) := by
            rw [← boards_filter_sup (Nat.le_of_lt_succ (mem_range.mp hp)) hp₀]
            ext s
            simp only [U, mem_filter]
            constructor
            · rintro ⟨⟨hs, hgap⟩, he⟩
              refine ⟨⟨hs, he⟩, ?_⟩
              simpa only [he, hp₀, false_or] using hgap
            · rintro ⟨⟨hs, he⟩, hgap⟩
              exact ⟨⟨hs, Or.inr (he.symm ▸ hgap)⟩, he⟩
          by_cases hgap : n + 1 - p ∈ Q <;> simp [h', hp₀, hgap, weight]
      rw [sum_congr rfl hfiber, sum_add_distrib]
      simp

private noncomputable def allowedGaps (Q : Finset ℕ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun d => if d = 0 ∨ d ∈ Q then 0 else 1

private theorem allowedGaps_eq {Q : Finset ℕ} (hQ0 : 0 ∉ Q) :
    allowedGaps Q = X * PowerSeries.mk (fun _ => 1) - ∑ q ∈ Q, X ^ q := by
  apply PowerSeries.ext
  intro d
  simp only [allowedGaps, coeff_mk, map_sub, map_sum, coeff_X_pow]
  cases d with
  | zero => simp [hQ0]
  | succ d =>
    rw [coeff_succ_X_mul, coeff_mk]
    by_cases hd : d + 1 ∈ Q <;> simp [hd]

private theorem endingSeries_eq {Q : Finset ℕ} (hQ : IsWellBased Q) :
    PowerSeries.mk (fun n => weight (endings Q n)) = C Y *
      (X * PowerSeries.mk (fun _ => 1) +
        PowerSeries.mk (fun n => weight (endings Q n)) * allowedGaps Q) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [allowedGaps, endings_zero, weight, coeff_mul]
  | succ n =>
    rw [coeff_C_mul, map_add, coeff_succ_X_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_mk, allowedGaps]
    rw [sum_range_succ, weight_endings_succ hQ]
    simp only [Nat.sub_self, true_or, ite_true, mul_zero, add_zero]
    congr 2
    apply sum_congr rfl
    intro p hp
    have hp₀ : n + 1 - p ≠ 0 := by have := mem_range.mp hp; omega
    by_cases h : n + 1 - p ∈ Q <;> simp [hp₀, h]

/-- **Bivariate generating function for well-based forbidden differences.** Let $Q$ be a finite
set of positive integers that is well based, and write $S^Q_{n,k}$ for the number of $k$-subsets
of $\{1, \dots, n\}$ in which no two elements differ by an element of $Q$. In the ring
$\mathbb{Z}[y][[x]]$ of formal power series in $x$ with coefficients in $\mathbb{Z}[y]$, let
$g(x, y) = \sum_{n \ge 0} \sum_{k=0}^{n} S^Q_{n,k} \, y^k x^n$ and
$c = 1 + \sum_{q \in Q} x^q y$. Then $g(x, y) \, \bigl((1 - x) \, c - x y\bigr) = c$; since
$(1 - x) c - x y$ has constant term $1$, this says $g = c / ((1 - x) c - x y)$.

The empty set counts as well based, so the case $Q = \emptyset$, where $g = 1/(1 - x - xy)$,
is included.

Source: Michael A. Allen, *Connections Between Combinations Without Specified Separations and
Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer
Sequences 28 (2025), Article 25.3.7, Corollary 24. -/
public theorem restrictedCombination_bivariate_genFun_of_isWellBased
    (Q : Finset ℕ) (hQ0 : 0 ∉ Q) (hQ : IsWellBased Q) :
    PowerSeries.mk (fun n => ∑ k ∈ Finset.range (n + 1),
        (restrictedCombinationCount Q n k : Polynomial ℤ) * Polynomial.X ^ k) *
        ((1 - PowerSeries.X) *
            (1 + ∑ qi ∈ Q, PowerSeries.X ^ qi * PowerSeries.C Polynomial.X) -
          PowerSeries.X * PowerSeries.C Polynomial.X) =
      1 + ∑ qi ∈ Q, PowerSeries.X ^ qi * PowerSeries.C Polynomial.X := by
  let G := PowerSeries.mk (fun n => weight (boards Q n))
  let E := PowerSeries.mk (fun n => weight (endings Q n))
  let T : PowerSeries (Polynomial ℤ) := PowerSeries.mk (fun _ => 1)
  let U : PowerSeries (Polynomial ℤ) := ∑ q ∈ Q, X ^ q
  let A := allowedGaps Q
  have hG : G * (1 - X) = 1 + E := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [G, E, mul_sub, boards_zero, endings_zero, weight]
    | succ n =>
      simp [G, E, mul_sub, coeff_succ_mul_X, coeff_one, weight_boards_succ]
  have hT : (1 - X) * T = 1 := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [T, sub_mul]
    | succ n => simp [T, sub_mul, coeff_succ_X_mul, coeff_one]
  have hA : A = X * T - U := allowedGaps_eq hQ0
  have hE : E = C Y * (X * T + E * A) := endingSeries_eq hQ
  have hden : (1 - X) * (1 + U * C Y) - X * C Y = (1 - X) * (1 - C Y * A) := by
    rw [hA]
    linear_combination X * C Y * hT
  simp_rw [sum_restrictedCombinationCount_mul]
  change G * ((1 - X) * (1 + ∑ qi ∈ Q, X ^ qi * C Y) - X * C Y) = _
  rw [← sum_mul]
  change G * ((1 - X) * (1 + U * C Y) - X * C Y) = 1 + U * C Y
  rw [hden, ← mul_assoc, hG]
  linear_combination hE - C Y * hA

end MetaMathlibExt
