/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MonochromaticLinearEquations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting solutions of linear equations in boxes

Helpers shared by the uncommonness proofs in `MathlibExt.Combinatorics.MonochromaticLinearEquations`
(`Recolouring` and `NoCancelingPartition`): the solutions of `∑ i, a i * x i = 0` in the box
`[1, n]^k`, monochromatic tuples, solutions with repeated coordinates and their count, a lower
bound on the number of solutions, and uncommonness restated with these counts.
-/

@[expose] public section

namespace MetaMathlibExt
namespace isUncommonOverIntegers_of_two

open Finset Filter

/-- The solutions of `∑ i, a i * x i = 0` with every coordinate in `[1, n]`. -/
def solutions {k : ℕ} (a : Fin k → ℤ) (n : ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ => Icc (1 : ℤ) n).filter (fun x => ∑ i, a i * x i = 0)

/-- Membership in `solutions a n`. -/
lemma mem_solutions {k n : ℕ} {a x : Fin k → ℤ} :
    x ∈ solutions a n ↔ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧ ∑ i, a i * x i = 0 := by
  simp [solutions]

/-- The tuple `x` is monochromatic under the colouring `χ`. -/
abbrev mono {k r : ℕ} (χ : ℤ → Fin r) (x : Fin k → ℤ) : Prop :=
  ∀ i j, χ (x i) = χ (x j)

open Classical in
/-- The tuples of `s` with two equal coordinates. -/
noncomputable def repeats {k : ℕ} (s : Finset (Fin k → ℤ)) :=
  s.filter fun x => ¬ Function.Injective x

/-- At most `k ^ 2 * n ^ (k - 2)` solutions have two equal coordinates: when two entries coincide,
dropping one of them and any third entry determines the tuple. -/
lemma repeats_le {k : ℕ} (hk : 3 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0) (n : ℕ) :
    (repeats (solutions a n)).card ≤ k ^ 2 * n ^ (k - 2) := by
  classical
  let s := solutions a n
  let pairs := (univ : Finset (Fin k × Fin k)).filter fun p => p.1 ≠ p.2
  let diag (p : Fin k × Fin k) := s.filter fun x => x p.1 = x p.2
  have cover : repeats s ⊆ pairs.biUnion diag := by
    intro x hx
    obtain ⟨hxs, h⟩ := mem_filter.mp hx
    simp only [Function.Injective, not_forall, exists_prop] at h
    obtain ⟨i, j, he, hij⟩ := h
    exact mem_biUnion.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hij⟩, mem_filter.mpr ⟨hxs, he⟩⟩
  have bound (p) (hp : p ∈ pairs) : (diag p).card ≤ n ^ (k - 2) := by
    obtain ⟨i, j⟩ := p
    have hij : i ≠ j := (mem_filter.mp hp).2
    have hex : ∃ l : Fin k, l ∉ ({i, j} : Finset _) := by
      by_contra! h
      have hle := card_le_card (show univ ⊆ ({i, j} : Finset _) from fun l _ => h l)
      simp [hij] at hle
      omega
    obtain ⟨l, hl⟩ := hex
    simp only [mem_insert, mem_singleton, not_or] at hl
    let keep := (univ.erase j).erase l
    have hkeep : keep.card = k - 2 := by
      simp [keep, card_erase_of_mem, hl.2, Nat.sub_sub]
    let box := Fintype.piFinset fun _ : keep => Icc (1 : ℤ) n
    have hcard : box.card = n ^ (k - 2) := by
      simp [box, Fintype.card_piFinset, Int.card_Icc, hkeep]
    rw [← hcard]
    apply card_le_card_of_injOn (fun (x : Fin k → ℤ) (t : keep) => x t)
    · intro x hx
      exact Fintype.mem_piFinset.mpr fun t => mem_Icc.mpr
        ((mem_solutions.mp (mem_filter.mp hx).1).1 t)
    · intro x hx y hy hxy
      obtain ⟨hxs, hxij⟩ := mem_filter.mp hx
      obtain ⟨hys, hyij⟩ := mem_filter.mp hy
      have heq (t : Fin k) (ht : t ≠ l) (ht' : t ≠ j) : x t = y t :=
        congrFun hxy ⟨t, by simp [keep, ht, ht']⟩
      have hout (t : Fin k) (ht : t ≠ l) : x t = y t := by
        by_cases ht' : t = j
        · subst t
          exact hxij.symm.trans ((heq i (Ne.symm hl.1) hij).trans hyij)
        · exact heq t ht ht'
      have hrest : ∑ t ∈ univ.erase l, a t * x t = ∑ t ∈ univ.erase l, a t * y t :=
        sum_congr rfl fun t ht => by rw [hout t (mem_erase.mp ht).1]
      have he := (mem_solutions.mp hxs).2.trans (mem_solutions.mp hys).2.symm
      rw [← sum_erase_add _ _ (mem_univ l), ← sum_erase_add _ (fun t => a t * y t) (mem_univ l),
        hrest] at he
      funext t
      by_cases ht : t = l
      · subst t
        exact mul_left_cancel₀ (ha _) (add_left_cancel he)
      · exact hout t ht
  calc
    _ ≤ _ := card_le_card cover
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, n ^ (k - 2) := sum_le_sum bound
    _ ≤ _ := by
      simp only [sum_const, smul_eq_mul]
      apply Nat.mul_le_mul_right
      simpa [sq] using (card_filter_le univ (fun p : Fin k × Fin k => p.1 ≠ p.2))

/-- An equation with a positive solution has at least `m ^ d` solutions in the box of side
`C * m`, for some `C > 0`: perturb the last coordinates of a large multiple of the positive
solution independently. -/
lemma many_solutions {d : ℕ} (a b : Fin (d + 1) → ℤ)
    (hd : 0 < d) (ha : a 0 ≠ 0) (hb : ∀ i, 0 < b i) (he : ∑ i, a i * b i = 0) :
    ∃ C : ℕ, 0 < C ∧ ∀ m : ℕ, m ^ d ≤ (solutions a (C * m)).card := by
  classical
  let B : ℕ := (∑ i, (a i).natAbs) + 1
  let C : ℕ := B * ((∑ i, (b i).natAbs) + 1)
  refine ⟨C, by dsimp [C, B]; positivity, ?_⟩
  intro m
  let box := Fintype.piFinset fun _ : Fin d => Icc (1 : ℤ) m
  have hc : box.card = m ^ d := by simp [box, Fintype.card_piFinset, Int.card_Icc]
  rw [← hc]
  let shift (u : Fin d → ℤ) := ∑ i, a i.succ * u i
  let f (u : Fin d → ℤ) : Fin (d + 1) → ℤ :=
    Fin.cons (B * (m : ℤ) * b 0 - shift u) fun i => B * (m : ℤ) * b i.succ + a 0 * u i
  apply card_le_card_of_injOn f
  · intro u hu
    have hu' (i) := mem_Icc.mp ((Fintype.mem_piFinset.mp hu) i)
    have hab (i) : |a i| ≤ (B : ℤ) - 1 := by
      dsimp [B]
      simp only [add_sub_cancel_right, Nat.cast_sum, Int.natCast_natAbs]
      exact single_le_sum (fun j _ => abs_nonneg (a j)) (mem_univ i)
    have hshift : |shift u| ≤ ((B : ℤ) - 1) * m := by
      calc
        _ ≤ ∑ i, |a i.succ * u i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |a i.succ| * m := sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (by linarith [(hu' i).1] : 0 ≤ u i)]
          exact mul_le_mul_of_nonneg_left (hu' i).2 (abs_nonneg _)
        _ ≤ _ := by
          rw [← sum_mul]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simp [B, Fin.sum_univ_succ]
    have inside (i) (z : ℤ) (hz : |z| ≤ ((B : ℤ) - 1) * m) (hm : 0 < m) :
        1 ≤ B * (m : ℤ) * b i + z ∧ B * (m : ℤ) * b i + z ≤ ↑(C * m) := by
      have hbi : |b i| ≤ ∑ j, |b j| := single_le_sum (fun j _ => abs_nonneg (b j)) (mem_univ i)
      rw [abs_of_pos (hb i)] at hbi
      have hBm : 0 ≤ B * (m : ℤ) := by positivity
      have hlow := mul_le_mul_of_nonneg_left (show 1 ≤ b i from hb i) hBm
      have hupp := mul_le_mul_of_nonneg_left hbi hBm
      simp only [C, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sum, Int.natCast_natAbs]
      obtain ⟨hzl, hzu⟩ := abs_le.mp hz
      constructor <;> nlinarith
    apply mem_solutions.mpr
    constructor
    · intro i
      have hm : 0 < m := by
        have := hu' ⟨0, hd⟩
        omega
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [f, sub_eq_add_neg] using inside 0 (-shift u) (by simpa using hshift) hm
      · apply inside
        · rw [abs_mul, abs_of_nonneg (by linarith [(hu' j).1] : 0 ≤ u j)]
          exact mul_le_mul (hab 0) (hu' j).2 (by linarith [(hu' j).1])
            (by linarith [hab 0, abs_nonneg (a 0)])
        · exact hm
    · rw [Fin.sum_univ_succ] at he ⊢
      simp only [f, Fin.cons_zero, Fin.cons_succ, mul_add, sum_add_distrib]
      simp_rw [show ∀ j : Fin d, a j.succ * (B * (m : ℤ) * b j.succ) =
        B * (m : ℤ) * (a j.succ * b j.succ) by intro j; ring,
        show ∀ j : Fin d, a j.succ * (a 0 * u j) = a 0 * (a j.succ * u j) by intro j; ring]
      simp only [← mul_sum, shift]
      linear_combination (B * (m : ℤ)) * he
  · intro u _ v _ h
    funext i
    exact mul_left_cancel₀ ha (add_left_cancel (congrFun h i.succ))

/-- Uncommonness over the integers, restated with `solutions` and `mono`. -/
lemma uncommon_iff {k r : ℕ} (a : Fin k → ℤ) :
    IsUncommonOverIntegers a r ↔ ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in atTop, ∃ χ : ℤ → Fin r,
      (r : ℝ) ^ (k - 1) * ((solutions a n).filter (mono χ)).card <
        (1 - ε) * (solutions a n).card := by
  simp only [IsUncommonOverIntegers, solutions, filter_filter, mono]

end isUncommonOverIntegers_of_two

end MetaMathlibExt
