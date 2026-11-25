/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Balog–Szemerédi–Gowers theorem

A finite set of integer vectors with large additive energy contains a large subset
with a small difference set. The proof counts popular sums and then popular differences.
-/

open Finset
open scoped Pointwise

namespace MathlibExt.Combinatorics.Additive.FreimanBSGWanted

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private def reps {α β : Type*} [DecidableEq β] (P : Finset α) (f : α → β) (v : β) : ℝ :=
  ((P.filter (fun p => f p = v)).card : ℝ)

private lemma sum_reps {α β : Type*} [DecidableEq β] (P : Finset α) (f : α → β)
    (T : Finset β) : ∑ v ∈ T, reps P f v = ((P.filter (fun p => f p ∈ T)).card : ℝ) := by
  unfold reps
  exact_mod_cast sum_card_fiberwise_eq_card_filter P T f

private lemma popular_bound {α β : Type*} [DecidableEq β] (P : Finset α) (f : α → β)
    (T : Finset β) (t : ℝ) (h : ∀ v ∈ T, t ≤ reps P f v) : t * T.card ≤ P.card := by
  calc
    t * T.card = ∑ _ ∈ T, t := by simp [mul_comm]
    _ ≤ ∑ v ∈ T, reps P f v := sum_le_sum h
    _ = _ := sum_reps P f T
    _ ≤ _ := by exact_mod_cast card_filter_le P _

private def neighbors (A S : Finset G) (x : G) := A.filter (fun y => x + y ∈ S)

-- Split the energy at multiplicity d|A|. The unpopular sums contribute at most d|A|³.
private lemma popular_sums (A : Finset G) (d : ℝ) (hd : 0 < d) (hA : 0 < (A.card : ℝ))
    (hE : 2 * d * (A.card : ℝ) ^ 3 ≤ A.addEnergy A) :
    ∃ S : Finset G, d * S.card ≤ A.card ∧
      d * (A.card : ℝ) ^ 2 ≤ ∑ x ∈ A, ((neighbors A S x).card : ℝ) := by
  classical
  let P := A ×ˢ A
  let f : G × G → G := fun p => p.1 + p.2
  let r := reps P f
  let S := (A + A).filter (fun s => d * A.card ≤ r s)
  have hr (s : G) : r s ≤ A.card := by
    apply Nat.cast_le.mpr
    apply card_le_card_of_injOn Prod.fst
    · exact fun p hp => (mem_product.mp (mem_filter.mp hp).1).1
    · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hq (rfl : a = a')
      have hp' : a + b = s := (mem_filter.mp hp).2
      have hq' : a + b' = s := (mem_filter.mp hq).2
      simp [add_left_cancel (hp'.trans hq'.symm)]
  have htotal : ∑ s ∈ A + A, r s = (A.card : ℝ) ^ 2 := by
    rw [show ∑ s ∈ A + A, r s = _ from sum_reps P f (A + A), filter_eq_self.mpr]
    · simp [P, sq]
    · intro p hp
      exact add_mem_add (mem_product.mp hp).1 (mem_product.mp hp).2
  have hpop := popular_bound P f S (d * A.card) fun _ h => (mem_filter.mp h).2
  simp only [P, card_product, Nat.cast_mul] at hpop
  refine ⟨S, (le_of_mul_le_mul_right (a := (A.card : ℝ)) ?_ hA), ?_⟩
  · linarith only [hpop]
  have hsq : (A.addEnergy A : ℝ) = ∑ s ∈ A + A, r s ^ 2 := by
    dsimp [r, reps, P, f]
    exact_mod_cast addEnergy_eq_sum_sq' A A
  have hpoint (s : G) (hs : s ∈ A + A) :
      r s ^ 2 ≤ d * A.card * r s + (if s ∈ S then r s else 0) * A.card := by
    have hnon : 0 ≤ r s := Nat.cast_nonneg _
    by_cases h : s ∈ S
    · simp only [h, ↓reduceIte]
      nlinarith [mul_nonneg (mul_nonneg hd.le hA.le) hnon, mul_le_mul_of_nonneg_left (hr s) hnon]
    · have hlt : r s < d * A.card := lt_of_not_ge fun H => h (mem_filter.mpr ⟨hs, H⟩)
      simp only [h, ↓reduceIte]
      nlinarith [mul_le_mul_of_nonneg_right hlt.le hnon]
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, ← mul_sum, ← sum_mul, ← sum_filter, htotal] at hsum
  have hfilter : (A + A).filter (fun s => s ∈ S) = S :=
    filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
  rw [hfilter, show ∑ s ∈ S, r s = _ from sum_reps P f S] at hsum
  have hedges : (P.filter (fun p => f p ∈ S)).card = ∑ x ∈ A, (neighbors A S x).card := by
    simp only [P, f, neighbors, card_eq_sum_ones, sum_filter, sum_product]
  rw [hedges, Nat.cast_sum] at hsum
  rw [hsq] at hE
  apply le_of_mul_le_mul_right (a := (A.card : ℝ)) _ hA
  linarith only [hE, hsum]

private def diffReps (S : Finset G) := reps (S ×ˢ S) (fun p => p.1 - p.2)

private def badCount (B D : Finset G) (y : G) : ℝ :=
  ((B.filter (fun z => y - z ∉ D)).card : ℝ)

private lemma card_filter_real {α : Type*} (A : Finset α) (p : α → Prop) [DecidablePred p] :
    ((A.filter p).card : ℝ) = ∑ x ∈ A, if p x then 1 else 0 := by
  rw [← sum_filter]
  simp

-- A pair with an unpopular difference has few common neighbors. Sum first over such pairs.
private lemma bad_triples (A S D : Finset G) (t : ℝ) (ht : 0 ≤ t)
    (hD : ∀ y ∈ A, ∀ z ∈ A, y - z ∉ D → diffReps S (y - z) ≤ t) :
    ∑ x ∈ A, ∑ y ∈ neighbors A S x, badCount (neighbors A S x) D y ≤ t * A.card ^ 2 := by
  classical
  let triple (x y z : G) : ℝ := if x + y ∈ S ∧ x + z ∈ S ∧ y - z ∉ D then 1 else 0
  have hpair (y z : G) (hy : y ∈ A) (hz : z ∈ A) : ∑ x ∈ A, triple x y z ≤ t := by
    by_cases hd : y - z ∈ D
    · simpa [triple, hd] using ht
    · apply le_trans _ (hD y hy z hz hd)
      simp only [triple, hd, not_false_eq_true, and_true, ← card_filter_real]
      apply Nat.cast_le.mpr
      apply card_le_card_of_injOn (fun x => (x + y, x + z))
      · intro x hx
        obtain ⟨hxy, hxz⟩ := (mem_filter.mp hx).2
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hxy, hxz⟩, by simp⟩
      · intro x _ x' _ he
        exact add_right_cancel (congrArg Prod.fst he : x + y = x' + y)
  have hcenter (x : G) :
      ∑ y ∈ neighbors A S x, badCount (neighbors A S x) D y =
        ∑ y ∈ A, ∑ z ∈ A, triple x y z := by
    simp only [neighbors, badCount, card_filter_real, sum_filter]
    apply sum_congr rfl
    intro y _
    by_cases h : x + y ∈ S
    · simp only [h, ↓reduceIte, triple, ite_and]
    · simp [triple, h]
  calc
    _ = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ A, triple x y z := sum_congr rfl (fun x _ => hcenter x)
    _ = ∑ y ∈ A, ∑ z ∈ A, ∑ x ∈ A, triple x y z := by
      rw [sum_comm]
      exact sum_congr rfl (fun _ _ => sum_comm)
    _ ≤ ∑ y ∈ A, ∑ _z ∈ A, t := sum_le_sum fun y hy => sum_le_sum fun z hz => hpair y z hy hz
    _ = _ := by simp; ring

-- Delete vertices having too many bad partners in their neighborhood, then average over centers.
private lemma select_neighborhood (A S D : Finset G) (d : ℝ) (hd : 0 < d)
    (hA : A.Nonempty) (he : d * (A.card : ℝ) ^ 2 ≤ ∑ x ∈ A, ((neighbors A S x).card : ℝ))
    (hbad : ∑ x ∈ A, ∑ y ∈ neighbors A S x, badCount (neighbors A S x) D y ≤
      (d ^ 2 * A.card / 16) * A.card ^ 2) :
    ∃ B ⊆ A, ∃ U ⊆ B, d * A.card / 2 ≤ U.card ∧
      ∀ y ∈ U, badCount B D y ≤ d * A.card / 8 := by
  classical
  let k := d * A.card / 8
  let B := neighbors A S
  let U (x : G) := (B x).filter (fun y => badCount (B x) D y ≤ k)
  have hk : 0 < k := by dsimp [k]; positivity [hA.card_pos]
  have hclean (x : G) :
      k * (B x).card - ∑ y ∈ B x, badCount (B x) D y ≤ k * (U x).card := by
    calc
      _ = ∑ y ∈ B x, (k - badCount (B x) D y) := by simp [sum_sub_distrib, mul_comm]
      _ ≤ ∑ y ∈ B x, if badCount (B x) D y ≤ k then k else 0 := by
        apply sum_le_sum
        intro y _
        split_ifs with h
        · exact sub_le_self _ (Nat.cast_nonneg _)
        · linarith
      _ = _ := by rw [← sum_filter]; simp [U, mul_comm]
  have hsum := sum_le_sum (s := A) fun x _ => hclean x
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum] at hsum
  have hsize : ∑ _x ∈ A, d * A.card / 2 ≤ ∑ x ∈ A, ((U x).card : ℝ) := by
    apply le_of_mul_le_mul_left (a := k) _ hk
    apply le_trans _ hsum
    have hw := mul_le_mul_of_nonneg_left he hk.le
    dsimp only [B, k] at *
    simp only [sum_const, nsmul_eq_mul]
    linarith only [hw, hbad]
  obtain ⟨x, _, hx⟩ := exists_le_of_sum_le hA hsize
  exact ⟨B x, filter_subset _ _, U x, filter_subset _ _, hx, fun _ h => (mem_filter.mp h).2⟩

-- Each difference in U - U has many representations in D - D, one for each common good partner.
private lemma differences_bound (B U D : Finset G) (k : ℝ) (hB : 4 * k ≤ B.card)
    (hU : ∀ u ∈ U, badCount B D u ≤ k) :
    2 * k * (U - U).card ≤ (D.card : ℝ) ^ 2 := by
  classical
  have hrep (w : G) (hw : w ∈ U - U) : 2 * k ≤ diffReps D w := by
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_sub.mp hw
    let good := B.filter (fun z => u - z ∈ D ∧ v - z ∈ D)
    have hcover : (B.card : ℝ) ≤ badCount B D u + badCount B D v + good.card := by
      simp only [badCount, good, card_filter_real, ← sum_add_distrib]
      calc
        _ = ∑ _z ∈ B, (1 : ℝ) := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro z _
          by_cases hu' : u - z ∈ D <;> by_cases hv' : v - z ∈ D <;> simp [hu', hv']
    have hgood : 2 * k ≤ good.card := by linarith [hU u hu, hU v hv]
    apply hgood.trans
    apply Nat.cast_le.mpr
    apply card_le_card_of_injOn (fun z => (u - z, v - z))
    · intro z hz
      exact mem_filter.mpr ⟨mem_product.mpr (mem_filter.mp hz).2, by simp⟩
    · intro z _ z' _ he
      exact sub_right_inj.mp (congrArg Prod.fst he : u - z = u - z')
  simpa [sq] using popular_bound (D ×ˢ D) (fun p => p.1 - p.2) (U - U) (2 * k) hrep

private lemma extract_subset (A : Finset G) (d : ℝ) (hd : 0 < d) (hA : A.Nonempty)
    (hE : 2 * d * (A.card : ℝ) ^ 3 ≤ A.addEnergy A) :
    d ≤ 1 ∧ ∃ U ⊆ A, d * A.card / 2 ≤ U.card ∧
      ((U - U).card : ℝ) ≤ 1024 * A.card / d ^ 9 := by
  classical
  have hm : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  obtain ⟨S, hS, he⟩ := popular_sums A d hd hm hE
  have hfull : ∑ x ∈ A, ((neighbors A S x).card : ℝ) ≤ ∑ _x ∈ A, (A.card : ℝ) :=
    sum_le_sum fun _ _ => Nat.cast_le.mpr (card_filter_le ..)
  have hd1 : d ≤ 1 := by
    apply le_of_mul_le_mul_right (a := (A.card : ℝ) ^ 2) _ (sq_pos_of_pos hm)
    simpa [sq] using he.trans hfull
  let t := d ^ 2 * A.card / 16
  have ht : 0 < t := by dsimp [t]; positivity
  let D := (A - A).filter (fun v => t ≤ diffReps S v)
  have hD : t * D.card ≤ (S.card : ℝ) ^ 2 := by
    simpa [sq] using popular_bound (S ×ˢ S) (fun p => p.1 - p.2) D t
      (fun _ h => (mem_filter.mp h).2)
  have hbad := bad_triples A S D t ht.le (by
    intro y hy z hz h
    exact le_of_not_ge fun hle => h (mem_filter.mpr ⟨sub_mem_sub hy hz, hle⟩))
  obtain ⟨B, hBA, U, hUB, hsize, hgood⟩ := select_neighborhood A S D d hd hA he hbad
  refine ⟨hd1, U, hUB.trans hBA, hsize, ?_⟩
  have hB : 4 * (d * A.card / 8) ≤ B.card := by
    linarith only [hsize, (Nat.cast_le (α := ℝ)).mpr (card_le_card hUB)]
  have hdiff := differences_bound B U D (d * A.card / 8) hB hgood
  have hs : (S.card : ℝ) ≤ A.card / d := (le_div_iff₀ hd).mpr (by linarith only [hS])
  have hdc : (D.card : ℝ) ≤ 16 * A.card / d ^ 4 := by
    apply le_of_mul_le_mul_left (a := t) _ ht
    calc
      _ ≤ (S.card : ℝ) ^ 2 := hD
      _ ≤ (A.card / d : ℝ) ^ 2 := by gcongr
      _ = t * (16 * A.card / d ^ 4) := by dsimp [t]; field_simp
  apply le_of_mul_le_mul_left (a := 2 * (d * A.card / 8)) _ (by positivity)
  calc
    _ ≤ (D.card : ℝ) ^ 2 := hdiff
    _ ≤ (16 * A.card / d ^ 4 : ℝ) ^ 2 := by gcongr
    _ = _ := by field_simp; ring

/-- **Balog–Szemerédi–Gowers theorem.** Let `A ⊆ ℤⁿ` have `m` elements and additive energy
`E(A) ≥ c₀ m³` with `c₀ > 0`. Then some `A'' ⊆ A` has `|A''| ≥ 2^{-20} c₀^{12} m` and
`|A'' - A''| ≤ 2^{38} c₀^{-24} m`: Proposition 7.3 of Gowers [G01], with these explicit
constants. Gowers writes the hypothesis as `‖A * A‖₂² = #{(a, b, c, d) ∈ A⁴ : a - b = c - d}`,
which is Mathlib's `Finset.addEnergy A A` (it counts the quadruples `((a₁, a₂), (b₁, b₂))` with
`a₁ + b₁ = a₂ + b₂`, a relabelling of `a - b = c - d`). Balog and Szemerédi proved the
qualitative version with the regularity lemma; the polynomial bounds are Gowers's. -/
public theorem balog_szemeredi_gowers (n : ℕ) (A : Finset (Fin n → ℤ)) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hE : c₀ * (A.card : ℝ) ^ 3 ≤ (Finset.addEnergy A A : ℝ)) :
    ∃ A'' ⊆ A, (2 : ℝ)⁻¹ ^ 20 * c₀ ^ 12 * A.card ≤ A''.card ∧
      ((A'' - A'').card : ℝ) ≤ 2 ^ 38 * c₀⁻¹ ^ 24 * A.card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨∅, by simp, by simp, by simp⟩
  let d := c₀ / 2
  have hd : 0 < d := half_pos hc₀
  have hc : c₀ = 2 * d := by dsimp [d]; ring
  obtain ⟨hd1, U, hUA, hsize, hdiff⟩ := extract_subset A d hd hA (by rwa [← hc])
  refine ⟨U, hUA, le_trans ?_ hsize, hdiff.trans ?_⟩
  · have hp : d ^ 12 ≤ d ^ 1 := pow_le_pow_of_le_one hd.le hd1 (by decide)
    rw [hc, mul_pow]
    norm_num at hp ⊢
    linarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) A.card),
      mul_nonneg hd.le (Nat.cast_nonneg (α := ℝ) A.card)]
  · have hp : d ^ 24 ≤ d ^ 9 := pow_le_pow_of_le_one hd.le hd1 (by decide)
    have hi : (d⁻¹) ^ 9 ≤ (d⁻¹) ^ 24 := by
      simpa only [inv_pow] using inv_anti₀ (pow_pos hd 24) hp
    calc
      1024 * A.card / d ^ 9 = 1024 * d⁻¹ ^ 9 * A.card := by rw [div_eq_mul_inv, inv_pow]; ring
      _ ≤ 16384 * d⁻¹ ^ 24 * A.card := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (by norm_num1) hi (by positivity) (by norm_num1)) (Nat.cast_nonneg _)
      _ = _ := by rw [hc, mul_inv_rev, mul_pow]; ring

end MathlibExt.Combinatorics.Additive.FreimanBSGWanted
