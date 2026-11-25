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
# Extending uncommonness to more colours

`MetaMathlibExt.isUncommonOverIntegers_of_two` extends a two-colour deficit to every larger
number of colours. At each step we independently recolour each point with one new colour.
Solutions with repeated coordinates contribute a vanishing fraction of all solutions.
-/

namespace MetaMathlibExt
namespace isUncommonOverIntegers_of_two

open Finset Filter

private def solutions {k : ℕ} (a : Fin k → ℤ) (n : ℕ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ => Icc (1 : ℤ) n).filter (fun x => ∑ i, a i * x i = 0)

private lemma mem_solutions {k n : ℕ} {a x : Fin k → ℤ} :
    x ∈ solutions a n ↔ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧ ∑ i, a i * x i = 0 := by
  simp [solutions]

private abbrev mono {k r : ℕ} (χ : ℤ → Fin r) (x : Fin k → ℤ) : Prop :=
  ∀ i j, χ (x i) = χ (x j)

open Classical in
private noncomputable def repeats {k : ℕ} (s : Finset (Fin k → ℤ)) :=
  s.filter fun x => ¬ Function.Injective x

-- When two entries coincide, dropping one of them and any third entry determines the tuple.
private lemma repeats_le {k : ℕ} (hk : 3 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0) (n : ℕ) :
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

-- Perturb the last coordinates of a large multiple of a positive solution independently.
private lemma many_solutions {d : ℕ} (a b : Fin (d + 1) → ℤ)
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

-- On all sufficiently large intervals, collisions occupy an arbitrarily small fraction.
private lemma sparse_repeats {k : ℕ} (hk : 3 ≤ k) (a b : Fin k → ℤ) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, 0 < b i) (he : ∑ i, a i * b i = 0) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, q * (repeats (solutions a n)).card ≤ (solutions a n).card := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  obtain ⟨C, hC, hmany⟩ := many_solutions a b (by omega) (ha 0) hb he
  let K := q * (d + 2) ^ 2 * (2 * C) ^ d
  filter_upwards [eventually_ge_atTop (C * (K + 1))] with n hn
  let m := n / C
  have hKm : K + 1 ≤ m := (Nat.le_div_iff_mul_le hC).mpr (by simpa [Nat.mul_comm] using hn)
  have hn' : n ≤ 2 * C * m := by
    have hrem := Nat.mod_lt n hC
    have hdiv := Nat.mod_add_div n C
    have hCm : C ≤ C * m := by simpa using Nat.mul_le_mul_left C (show 1 ≤ m by omega)
    dsimp [m] at *
    rw [Nat.mul_assoc]
    omega
  have hcmp := repeats_le hk a ha n
  simp only [Nat.add_sub_cancel] at hcmp
  calc
    _ ≤ q * ((d + 2) ^ 2 * n ^ d) := Nat.mul_le_mul_left _ hcmp
    _ ≤ q * ((d + 2) ^ 2 * (2 * C * m) ^ d) := by gcongr
    _ = K * m ^ d := by simp [K, mul_pow, mul_assoc]
    _ ≤ m ^ (d + 1) := by rw [pow_succ']; gcongr; omega
    _ ≤ _ := (hmany m).trans (card_le_card fun x hx => by
      obtain ⟨hx, heq⟩ := mem_solutions.mp hx
      exact mem_solutions.mpr ⟨fun i => ⟨(hx i).1, (hx i).2.trans (by
        exact_mod_cast Nat.mul_div_le n C)⟩, heq⟩)

-- Count the random labels constrained to lie in A at k distinct vertices.
private lemma count_labels {V : Type*} [Fintype V] [DecidableEq V] {k R : ℕ} (x : Fin k → V)
    (hx : Function.Injective x) (A : Finset (Fin R)) :
    R ^ k * (univ.filter (fun w : V → Fin R => ∀ i, w (x i) ∈ A)).card =
      Fintype.card (V → Fin R) * A.card ^ k := by
  classical
  let t := univ.image x
  have ht : t.card = k := by simp [t, card_image_of_injective _ hx]
  let choices (v : V) := if v ∈ t then A else univ
  have heq : univ.filter (fun w : V → Fin R => ∀ i, w (x i) ∈ A) = Fintype.piFinset choices := by
    ext w
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v ∈ t
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
        simpa [choices, hv] using h i
      · simp [choices, hv]
    · intro h i
      simpa [choices, t] using h (x i)
  have hprod : (∏ v, (choices v).card) = R ^ (Fintype.card V - k) * A.card ^ k := by
    rw [← prod_sdiff (s₁ := t) (s₂ := univ) (by simp)]
    congr 1
    · calc
        _ = ∏ _v ∈ univ \ t, R := prod_congr rfl fun v hv => by simp [choices, (mem_sdiff.mp hv).2]
        _ = _ := by simp [card_sdiff_of_subset, ht]
    · calc
        _ = ∏ _v ∈ t, A.card := prod_congr rfl fun v hv => by simp [choices, hv]
        _ = _ := by simp [ht]
  have hk : k ≤ Fintype.card V := by simpa using Fintype.card_le_of_injective x hx
  rw [heq, Fintype.card_piFinset, hprod, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hk]
  simp

-- Average over independent uniform labels. Label zero introduces the new colour.
private lemma recolour {k r n : ℕ} (a : Fin k → ℤ) (χ : ℤ → Fin r) :
    ∃ ψ : ℤ → Fin (r + 1), (r + 1) ^ k * ((solutions a n).filter (mono ψ)).card ≤
      r ^ k * ((solutions a n).filter (mono χ)).card + (solutions a n).card +
        (r + 1) ^ k * (repeats (solutions a n)).card := by
  classical
  let V := ↥(Icc (1 : ℤ) n)
  let W := V → Fin (r + 1)
  let s := solutions a n
  let R := r + 1
  let colour (w : W) (z : ℤ) : Fin (r + 1) :=
    if h : z ∈ Icc (1 : ℤ) n then
      if w ⟨z, h⟩ = 0 then Fin.last r else (χ z).castSucc
    else Fin.last r
  let bound (x : Fin k → ℤ) := (if mono χ x then r ^ k else 0) + 1 +
    (if Function.Injective x then 0 else R ^ k)
  -- A tuple of distinct points is monochromatic if all labels are zero, or if
  -- the tuple was already monochromatic and all labels are nonzero.
  have point (x) (hx : x ∈ s) :
      R ^ k * (univ.filter fun w : W => mono (colour w) x).card ≤ Fintype.card W * bound x := by
    by_cases hi : Function.Injective x
    · have hx' (i) : x i ∈ Icc (1 : ℤ) n := mem_Icc.mpr ((mem_solutions.mp hx).1 i)
      let y (i : Fin k) : V := ⟨x i, hx' i⟩
      have hy : Function.Injective y := fun _ _ h => hi (congrArg Subtype.val h)
      let fresh := univ.filter fun w : W => ∀ i, w (y i) ∈ ({0} : Finset _)
      let old := univ.filter fun w : W => ∀ i, w (y i) ∈ univ.erase 0
      have hf : R ^ k * fresh.card = Fintype.card W := by
        simpa only [R, fresh, card_singleton, one_pow, mul_one] using
          count_labels y hy ({0} : Finset (Fin (r + 1)))
      have ho : R ^ k * old.card = Fintype.card W * r ^ k := by
        have hcard : (univ.erase (0 : Fin (r + 1))).card = r := by simp
        simpa only [R, old, hcard] using count_labels y hy (univ.erase (0 : Fin (r + 1)))
      have cover : (univ.filter fun w : W => mono (colour w) x) ⊆
          fresh ∪ (if mono χ x then old else ∅) := by
        intro w hw
        have h := (mem_filter.mp hw).2
        by_cases hz : ∀ i, w (y i) = 0
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, by simpa using hz⟩)
        · obtain ⟨j, hj⟩ := not_forall.mp hz
          have hc (i) : colour w (x i) = if w (y i) = 0 then Fin.last r else (χ (x i)).castSucc :=
            dite_eq_left (hx' i)
          have hn (i) : w (y i) ≠ 0 := by
            intro he
            have hij := h i j
            rw [hc, hc, ite_eq_left he, ite_eq_right hj] at hij
            exact Fin.castSucc_ne_last _ hij.symm
          have hm : mono χ x := by
            intro i l
            have hil := h i l
            rw [hc, hc, ite_eq_right (hn i), ite_eq_right (hn l)] at hil
            exact Fin.castSucc_injective _ hil
          apply mem_union_right
          rw [ite_eq_left hm]
          exact mem_filter.mpr ⟨mem_univ _, fun i => mem_erase.mpr ⟨hn i, mem_univ _⟩⟩
      have hle := Nat.mul_le_mul_left (R ^ k) ((card_le_card cover).trans (card_union_le _ _))
      dsimp only [bound]
      rw [ite_eq_left hi]
      by_cases hm : mono χ x
      · rw [ite_eq_left hm] at hle ⊢
        simpa [mul_add, hf, ho, add_comm] using hle
      · rw [ite_eq_right hm] at hle ⊢
        simpa [hf] using hle
    · have hle : (univ.filter fun w : W => mono (colour w) x).card ≤ Fintype.card W :=
        card_le_univ _
      calc
        _ ≤ R ^ k * Fintype.card W := Nat.mul_le_mul_left _ hle
        _ ≤ _ := by rw [mul_comm]; apply Nat.mul_le_mul_left; simp [bound, hi]
  have sum_point := sum_le_sum point
  have swap : ∑ x ∈ s, (univ.filter fun w : W => mono (colour w) x).card =
      ∑ w : W, (s.filter (mono (colour w))).card := by
    simp_rw [card_filter]
    rw [sum_comm]
  have hsum : ∑ x ∈ s, bound x =
      r ^ k * (s.filter (mono χ)).card + s.card + R ^ k * (repeats s).card := by
    simp [bound, sum_add_distrib, sum_ite, repeats, mul_comm]
  rw [← mul_sum, swap, ← mul_sum, hsum] at sum_point
  by_contra! h
  have strict := sum_lt_sum_of_nonempty (univ_nonempty (α := W)) fun w _ => h (colour w)
  simp only [sum_const, card_univ, smul_eq_mul, ← mul_sum] at strict
  exact (not_lt_of_ge sum_point) strict

private lemma uncommon_iff {k r : ℕ} (a : Fin k → ℤ) :
    IsUncommonOverIntegers a r ↔ ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in atTop, ∃ χ : ℤ → Fin r,
      (r : ℝ) ^ (k - 1) * ((solutions a n).filter (mono χ)).card <
        (1 - ε) * (solutions a n).card := by
  simp only [IsUncommonOverIntegers, solutions, filter_filter, mono]

private lemma uncommon_succ {k r : ℕ} (hk : 3 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, a i ≠ 0)
    (hr : 0 < r) (h : IsUncommonOverIntegers a r) : IsUncommonOverIntegers a (r + 1) := by
  obtain ⟨ε, hε, hf⟩ := (uncommon_iff a).mp h
  have hpos : ∃ b : Fin k → ℤ, (∀ i, 0 < b i) ∧ ∑ i, a i * b i = 0 := by
    obtain ⟨n, χ, hn⟩ := hf.exists
    have hne : (solutions a n).Nonempty := by
      by_contra! h
      simp [h] at hn
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, fun i => ((mem_solutions.mp hb).1 i).1, (mem_solutions.mp hb).2⟩
  obtain ⟨b, hb, he⟩ := hpos
  let R : ℝ := r + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let δ : ℝ := r * ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨q, hq⟩ := exists_nat_ge (R ^ k / δ)
  apply (uncommon_iff a).mpr
  refine ⟨δ / R, div_pos hδ hR, ?_⟩
  apply (hf.and_eventually (sparse_repeats hk a b ha hb he q)).mono
  rintro n ⟨⟨χ, hχ⟩, hs⟩
  obtain ⟨ψ, hψ⟩ := recolour a χ (n := n)
  refine ⟨ψ, ?_⟩
  let S : ℝ := (solutions a n).card
  let D : ℝ := (repeats (solutions a n)).card
  let M (s : ℕ) (c : ℤ → Fin s) : ℝ := ((solutions a n).filter (mono c)).card
  have hs' : q * D ≤ S := by dsimp [D, S]; exact_mod_cast hs
  have hψ' : R ^ k * M _ ψ ≤ (r : ℝ) ^ k * M _ χ + S + R ^ k * D := by
    dsimp only [R, M, S, D]
    exact_mod_cast hψ
  have hD : R ^ k * D ≤ δ * S := calc
    _ ≤ (q * δ) * D :=
      mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp hq) (by dsimp [D]; positivity)
    _ = δ * (q * D) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs' hδ.le
  change (r : ℝ) ^ (k - 1) * M _ χ < (1 - ε) * S at hχ
  have hp (t : ℝ) : t ^ k = t * t ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
  simp only [Nat.cast_add, Nat.cast_one]
  change R ^ (k - 1) * M _ ψ < (1 - δ / R) * S
  apply lt_of_mul_lt_mul_left (a := R) _ hR.le
  have hmain := mul_lt_mul_of_pos_left hχ (show (0 : ℝ) < r by exact_mod_cast hr)
  rw [hp R, hp (r : ℝ)] at hψ'
  rw [hp R] at hD
  have hcancel : R * (1 - δ / R) = R - δ := by field_simp
  rw [← mul_assoc R _ S, hcancel]
  dsimp only [R, δ] at hψ' hD ⊢
  linarith only [hmain, hψ', hD]

end isUncommonOverIntegers_of_two

open isUncommonOverIntegers_of_two in
/-- **Two-colour uncommonness over the integers extends to more colours.** Let
$k \ge 3$ and let $a_1, \dots, a_k$ be nonzero integers. If the equation
$a_1x_1 + \cdots + a_kx_k = 0$ is $2$-uncommon over the integers, then it is $r$-uncommon
over the integers for every $r \ge 3$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Theorem 2 (`integers-2025-A88-thm-2`). -/
public theorem isUncommonOverIntegers_of_two (k : ℕ) (hk : 3 ≤ k) (a : Fin k → ℤ)
    (ha : ∀ i, a i ≠ 0) (h2 : IsUncommonOverIntegers a 2) (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverIntegers a r := by
  have extend (s : ℕ) (hs : 2 ≤ s) : IsUncommonOverIntegers a s := by
    induction s, hs using Nat.le_induction with
    | base => exact h2
    | succ s hs ih => exact uncommon_succ hk a ha (by omega) ih
  exact extend r (by omega)

end MetaMathlibExt
