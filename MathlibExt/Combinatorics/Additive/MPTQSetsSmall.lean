/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.MPTQSets
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# MPTQ sets with at most four elements

No set of at most four real numbers is an MPTQ set. Order the elements by absolute value. Either
the set is symmetric, that is $c / a \in A$ for every $a \in A$ and some $c \neq 0$, so that
$A \cdot A = c \cdot (A / A)$, or the products, counted with the coincidences that hold, are at
most as many as some explicitly distinct quotients: $1$, $-1$ when the set contains a pair
$\pm u$, quotients of absolute value greater than $1$, and their inverses.

## Main results

- `MetaMathlibExt.not_isMPTQSet_of_card_le_four`: no MPTQ set has at most four elements.
- `MetaMathlibExt.five_le_card_of_isMPTQSet_of_neg`: every MPTQ set with a negative element has
  at least five elements.
-/

namespace MetaMathlibExt

open Pointwise

/-! ### Two ways to rule out the MPTQ property -/

-- A symmetric set satisfies `A * A ⊆ c * (A / A)`.
private theorem not_isMPTQSet_of_div_mem {A : Finset ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ a ∈ A, c / a ∈ A) : ¬ IsMPTQSet A := by
  refine fun hA => hA.2.not_ge ?_
  calc (A * A).card ≤ ((A / A).image (c * ·)).card := by
        refine Finset.card_le_card fun p hp => ?_
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hp
        refine Finset.mem_image.mpr ⟨a / (c / b), Finset.div_mem_div ha (h b hb), ?_⟩
        field_simp
    _ ≤ (A / A).card := Finset.card_image_le

-- At most `n` products, against the distinct quotients in `E`, of absolute value `1`, in `S`, of
-- absolute value greater than `1`, and the inverses of those in `S`.
private theorem not_isMPTQSet_of_lists {A : Finset ℝ} {n : ℕ} (E S : List ℝ)
    (hM : (A * A).card ≤ n) (hE : E.Nodup) (hE1 : ∀ e ∈ E, |e| = 1)
    (hEmem : ∀ e ∈ E, e ∈ A / A) (hS : S.Nodup) (hS1 : ∀ q ∈ S, 1 < |q|)
    (hSmem : ∀ q ∈ S, q ∈ A / A) (hlen : n ≤ E.length + 2 * S.length) : ¬ IsMPTQSet A := by
  refine fun hA => hA.2.not_ge ?_
  have hne : ∀ x ∈ S ++ S.map (·⁻¹), |x| ≠ 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hS1 x hx).ne'
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      rw [abs_inv]
      exact (inv_lt_one_of_one_lt₀ (hS1 q hq)).ne
  have hnd : (E ++ (S ++ S.map (·⁻¹))).Nodup := by
    refine List.nodup_append.mpr ⟨hE, List.nodup_append.mpr ⟨hS, hS.map inv_injective, ?_⟩,
      fun e he x hx hex => hne x hx (hex ▸ hE1 e he)⟩
    intro x hx y hy hxy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    have := hS1 x hx
    rw [hxy, abs_inv] at this
    exact (inv_lt_one_of_one_lt₀ (hS1 q hq)).not_gt this
  have hsub : (E ++ (S ++ S.map (·⁻¹))).toFinset ⊆ A / A := by
    intro q hq
    rcases List.mem_append.mp (List.mem_toFinset.mp hq) with hq | hq
    · exact hEmem q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hSmem q hq
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_div.mp (hSmem r hr)
      exact Finset.mem_div.mpr ⟨b, hb, a, ha, (inv_div a b).symm⟩
  calc (A * A).card ≤ E.length + 2 * S.length := hM.trans hlen
    _ = (E ++ (S ++ S.map (·⁻¹))).toFinset.card := by
        rw [List.toFinset_card_of_nodup hnd]; simp; omega
    _ ≤ (A / A).card := Finset.card_le_card hsub

-- The same, with `E = [1]`.
private theorem not_isMPTQSet_of_list_one {A : Finset ℝ} {n : ℕ} {a : ℝ} (S : List ℝ)
    (ha : a ≠ 0) (haA : a ∈ A) (hM : (A * A).card ≤ n) (hS : S.Nodup) (hS1 : ∀ q ∈ S, 1 < |q|)
    (hSmem : ∀ q ∈ S, q ∈ A / A) (hlen : n ≤ 2 * S.length + 1) : ¬ IsMPTQSet A :=
  not_isMPTQSet_of_lists [1] S hM (by simp) (by simp)
    (by simpa using Finset.mem_div.mpr ⟨a, haA, a, haA, div_self ha⟩) hS hS1 hSmem
    (by simp; omega)

-- The same, with `E = [1, -1]` for a set containing `u` and `-u`.
private theorem not_isMPTQSet_of_list_neg_one {A : Finset ℝ} {n : ℕ} {u : ℝ} (S : List ℝ)
    (hu : u ≠ 0) (huA : u ∈ A) (hnA : -u ∈ A) (hM : (A * A).card ≤ n) (hS : S.Nodup)
    (hS1 : ∀ q ∈ S, 1 < |q|) (hSmem : ∀ q ∈ S, q ∈ A / A) (hlen : n ≤ 2 * S.length + 2) :
    ¬ IsMPTQSet A := by
  refine not_isMPTQSet_of_lists [1, -1] S hM (by norm_num) (by simp) ?_ hS hS1 hSmem
    (by simp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl)
  · exact Finset.mem_div.mpr ⟨u, huA, u, huA, div_self hu⟩
  · exact Finset.mem_div.mpr ⟨u, huA, -u, hnA, by field_simp⟩

/-! ### Counting products and comparing quotients -/

private theorem mul_subset_three (a b c : ℝ) :
    ({a, b, c} : Finset ℝ) * {a, b, c} ⊆ [a * a, a * b, a * c, b * b, b * c, c * c].toFinset := by
  intro p hp
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
  rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl <;> simp [mul_comm]

private theorem mul_subset_four (a b c d : ℝ) :
    ({a, b, c, d} : Finset ℝ) * {a, b, c, d} ⊆
      [a * a, a * b, a * c, a * d, b * b, b * c, b * d, c * c, c * d, d * d].toFinset := by
  intro p hp
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_mul.mp hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
  rcases hy with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
    simp [mul_comm]

private theorem card_mul_le_six (a b c : ℝ) : (({a, b, c} : Finset ℝ) * {a, b, c}).card ≤ 6 :=
  (Finset.card_le_card (mul_subset_three a b c)).trans (List.toFinset_card_le _)

private theorem card_mul_le_ten (a b c d : ℝ) :
    (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤ 10 :=
  (Finset.card_le_card (mul_subset_four a b c d)).trans (List.toFinset_card_le _)

private theorem one_lt_abs_div {x y : ℝ} (hy : y ≠ 0) (h : |y| < |x|) : 1 < |x / y| := by
  rwa [abs_div, one_lt_div (abs_pos.mpr hy)]

private theorem abs_div_lt_abs_div_left {x y z : ℝ} (hz : z ≠ 0) (h : |x| < |y|) :
    |x / z| < |y / z| := by
  rw [abs_div, abs_div]
  exact div_lt_div_of_pos_right h (abs_pos.mpr hz)

private theorem abs_div_lt_abs_div_right {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : |y| < |z|) :
    |x / z| < |x / y| := by
  rw [abs_div, abs_div]
  exact div_lt_div_of_pos_left (abs_pos.mpr hx) (abs_pos.mpr hy) h

private theorem ne_of_abs_lt {x y : ℝ} (h : |x| < |y|) : x ≠ y := fun e => h.ne (congrArg _ e)

private theorem ne_neg_of_ne_zero {x : ℝ} (h : x ≠ 0) : x ≠ -x := fun e => h (by linarith)

private theorem ne_zero_of_abs_lt {x y : ℝ} (h : |x| < |y|) : y ≠ 0 :=
  abs_pos.mp ((abs_nonneg x).trans_lt h)

/-! ### Three elements -/

private theorem not_isMPTQSet_three_pair_low {u v : ℝ} (hu : u ≠ 0) (huv : |u| < |v|) :
    ¬ IsMPTQSet ({u, -u, v} : Finset ℝ) := by
  have hv : v ≠ 0 := ne_zero_of_abs_lt huv
  refine not_isMPTQSet_of_list_neg_one [v / u, -(v / u)] hu (by simp) (by simp)
    (card_mul_le_six u (-u) v) ?_ ?_ ?_ (by simp)
  · simpa using ne_neg_of_ne_zero (div_ne_zero hv hu)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl) <;> (try rw [abs_neg]) <;> exact one_lt_abs_div hu huv
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    · exact Finset.mem_div.mpr ⟨v, by simp, u, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨v, by simp, -u, by simp, div_neg v⟩

private theorem not_isMPTQSet_three_pair_high {a x : ℝ} (ha : a ≠ 0) (hax : |a| < |x|) :
    ¬ IsMPTQSet ({a, x, -x} : Finset ℝ) := by
  have hx : x ≠ 0 := ne_zero_of_abs_lt hax
  refine not_isMPTQSet_of_list_neg_one [x / a, -(x / a)] hx (by simp) (by simp)
    (card_mul_le_six a x (-x)) ?_ ?_ ?_ (by simp)
  · simpa using ne_neg_of_ne_zero (div_ne_zero hx ha)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl) <;> (try rw [abs_neg]) <;> exact one_lt_abs_div ha hax
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    · exact Finset.mem_div.mpr ⟨x, by simp, a, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨-x, by simp, a, by simp, neg_div a x⟩

private theorem not_isMPTQSet_three_lt {a b c : ℝ} (ha : a ≠ 0) (hab : |a| < |b|)
    (hbc : |b| < |c|) : ¬ IsMPTQSet ({a, b, c} : Finset ℝ) := by
  have hb : b ≠ 0 := ne_zero_of_abs_lt hab
  have hc : c ≠ 0 := ne_zero_of_abs_lt hbc
  by_cases h : a * c = b * b
  · refine not_isMPTQSet_of_div_mem (mul_ne_zero hb hb) ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl | rfl)
    · right; right; field_simp; linear_combination -h
    · right; left; field_simp
    · left; field_simp; linear_combination -h
  refine not_isMPTQSet_of_list_one [b / a, c / a, c / b] ha (by simp) (card_mul_le_six a b c) ?_
    ?_ ?_ (by simp)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ne_of_abs_lt (abs_div_lt_abs_div_left ha hbc), ?_⟩,
      (ne_of_abs_lt (abs_div_lt_abs_div_right hc ha hab)).symm, by simp⟩
    intro e
    rw [div_eq_div_iff ha hb] at e
    exact h (by linear_combination -e)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl)
    exacts [one_lt_abs_div ha hab, one_lt_abs_div ha (hab.trans hbc), one_lt_abs_div hb hbc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl) <;> exact Finset.div_mem_div (by simp) (by simp)

private theorem not_isMPTQSet_three_sorted {a b c : ℝ} (ha : a ≠ 0) (hab' : a ≠ b) (hac' : a ≠ c)
    (hbc' : b ≠ c) (hab : |a| ≤ |b|) (hbc : |b| ≤ |c|) :
    ¬ IsMPTQSet ({a, b, c} : Finset ℝ) := by
  rcases hab.lt_or_eq with hab | hab
  · rcases hbc.lt_or_eq with hbc | hbc
    · exact not_isMPTQSet_three_lt ha hab hbc
    · obtain rfl : b = -c := (abs_eq_abs.mp hbc).resolve_left hbc'
      rw [abs_neg] at hab
      rw [show ({a, -c, c} : Finset ℝ) = {a, c, -c} by ext; simp; tauto]
      exact not_isMPTQSet_three_pair_high ha hab
  · obtain rfl : a = -b := (abs_eq_abs.mp hab).resolve_left hab'
    have hbc : |b| < |c| := hbc.lt_of_ne fun e =>
      hac' (by rw [(abs_eq_abs.mp e).resolve_left hbc', neg_neg])
    rw [Finset.insert_comm]
    exact not_isMPTQSet_three_pair_low (neg_ne_zero.mp ha) hbc

/-! ### Four elements, two of them opposite -/

private theorem not_isMPTQSet_four_pairs {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    ¬ IsMPTQSet ({a, -a, c, -c} : Finset ℝ) := by
  refine not_isMPTQSet_of_div_mem (mul_ne_zero ha hc) ?_
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl)
  · right; right; left; field_simp
  · right; right; right; field_simp
  · left; field_simp
  · right; left; field_simp

private theorem not_isMPTQSet_four_pair_low {u v w : ℝ} (hu : u ≠ 0) (huv : |u| < |v|)
    (hvw : |v| < |w|) : ¬ IsMPTQSet ({u, -u, v, w} : Finset ℝ) := by
  have hv : v ≠ 0 := ne_zero_of_abs_lt huv
  have hw : w ≠ 0 := ne_zero_of_abs_lt hvw
  have h := abs_div_lt_abs_div_left hu hvw
  refine not_isMPTQSet_of_list_neg_one [v / u, -(v / u), w / u, -(w / u)] hu (by simp)
    (by simp) (card_mul_le_ten u (-u) v w) ?_ ?_ ?_ (by simp)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ne_neg_of_ne_zero (div_ne_zero hv hu), ne_of_abs_lt h,
      ne_of_abs_lt (by rwa [abs_neg])⟩, ⟨ne_of_abs_lt (by rwa [abs_neg]),
      ne_of_abs_lt (by rwa [abs_neg, abs_neg])⟩, ne_neg_of_ne_zero (div_ne_zero hw hu), by simp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl) <;> (try rw [abs_neg])
    exacts [one_lt_abs_div hu huv, one_lt_abs_div hu huv, one_lt_abs_div hu (huv.trans hvw),
      one_lt_abs_div hu (huv.trans hvw)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl)
    · exact Finset.mem_div.mpr ⟨v, by simp, u, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨v, by simp, -u, by simp, div_neg v⟩
    · exact Finset.mem_div.mpr ⟨w, by simp, u, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨w, by simp, -u, by simp, div_neg w⟩

private theorem not_isMPTQSet_four_pair_high {a b x : ℝ} (ha : a ≠ 0) (hab : |a| < |b|)
    (hbx : |b| < |x|) : ¬ IsMPTQSet ({a, b, x, -x} : Finset ℝ) := by
  have hb : b ≠ 0 := ne_zero_of_abs_lt hab
  have hx : x ≠ 0 := ne_zero_of_abs_lt hbx
  have h := abs_div_lt_abs_div_right hx ha hab
  refine not_isMPTQSet_of_list_neg_one [x / a, -(x / a), x / b, -(x / b)] hx (by simp)
    (by simp) (card_mul_le_ten a b x (-x)) ?_ ?_ ?_ (by simp)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ne_neg_of_ne_zero (div_ne_zero hx ha), (ne_of_abs_lt h).symm,
      (ne_of_abs_lt (by rwa [abs_neg])).symm⟩, ⟨(ne_of_abs_lt (by rwa [abs_neg])).symm,
      (ne_of_abs_lt (by rwa [abs_neg, abs_neg])).symm⟩, ne_neg_of_ne_zero (div_ne_zero hx hb),
      by simp⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl) <;> (try rw [abs_neg])
    exacts [one_lt_abs_div ha (hab.trans hbx), one_lt_abs_div ha (hab.trans hbx),
      one_lt_abs_div hb hbx, one_lt_abs_div hb hbx]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl)
    · exact Finset.mem_div.mpr ⟨x, by simp, a, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨-x, by simp, a, by simp, neg_div a x⟩
    · exact Finset.mem_div.mpr ⟨x, by simp, b, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨-x, by simp, b, by simp, neg_div b x⟩

private theorem not_isMPTQSet_four_pair_mid {a u d : ℝ} (ha : a ≠ 0) (hau : |a| < |u|)
    (hud : |u| < |d|) : ¬ IsMPTQSet ({a, u, -u, d} : Finset ℝ) := by
  have hu : u ≠ 0 := ne_zero_of_abs_lt hau
  have hd : d ≠ 0 := ne_zero_of_abs_lt hud
  by_cases h : a * d = u * u ∨ a * d = -(u * u)
  · refine not_isMPTQSet_of_div_mem (mul_ne_zero ha hd) ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl | rfl | rfl)
    · right; right; right; field_simp
    · rcases h with h | h
      · right; left; field_simp; linear_combination h
      · right; right; left; field_simp; linear_combination h
    · rcases h with h | h
      · right; right; left; field_simp; linear_combination -h
      · right; left; field_simp; linear_combination -h
    · left; field_simp
  rw [not_or] at h
  refine not_isMPTQSet_of_list_neg_one [u / a, -(u / a), d / u, -(d / u)] hu (by simp)
    (by simp) (card_mul_le_ten a u (-u) d) ?_ ?_ ?_ (by simp)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ne_neg_of_ne_zero (div_ne_zero hu ha), ?_, ?_⟩, ⟨?_, ?_⟩,
      ne_neg_of_ne_zero (div_ne_zero hd hu), by simp⟩ <;> intro e <;> field_simp at e
    · exact h.1 (by linear_combination -e)
    · exact h.2 (by linear_combination e)
    · exact h.2 (by linear_combination -e)
    · exact h.1 (by linear_combination e)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl) <;> (try rw [abs_neg])
    exacts [one_lt_abs_div ha hau, one_lt_abs_div ha hau, one_lt_abs_div hu hud,
      one_lt_abs_div hu hud]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl)
    · exact Finset.mem_div.mpr ⟨u, by simp, a, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨-u, by simp, a, by simp, neg_div a u⟩
    · exact Finset.mem_div.mpr ⟨d, by simp, u, by simp, rfl⟩
    · exact Finset.mem_div.mpr ⟨d, by simp, -u, by simp, div_neg d⟩

/-! ### Four elements of distinct absolute values -/

-- One product coincidence `b * b = a * d`; the quotient `c / b` is not `b / a`.
private theorem not_isMPTQSet_four_lt_of_sq_left {a b c d : ℝ} (ha : a ≠ 0) (hab : |a| < |b|)
    (hbc : |b| < |c|) (hcd : |c| < |d|) (hb2 : b * b = a * d) :
    ¬ IsMPTQSet ({a, b, c, d} : Finset ℝ) := by
  have hb : b ≠ 0 := ne_zero_of_abs_lt hab
  have hc : c ≠ 0 := ne_zero_of_abs_lt hbc
  have hb3 : b * b ≠ a * c := by
    rw [hb2]; exact fun e => (ne_of_abs_lt hcd).symm (mul_left_cancel₀ ha e)
  have h1 := abs_div_lt_abs_div_left ha hbc
  have h2 := abs_div_lt_abs_div_left ha hcd
  have h3 := abs_div_lt_abs_div_right hc ha hab
  have hM : (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤ 9 := by
    refine (Finset.card_le_card ((mul_subset_four a b c d).trans ?_)).trans
      (List.toFinset_card_le [a * a, a * b, a * c, a * d, b * c, b * d, c * c, c * d, d * d])
    intro p hp
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hb2]
  refine not_isMPTQSet_of_list_one [b / a, c / a, d / a, c / b] ha (by simp) hM ?_ ?_ ?_
    (by simp)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ne_of_abs_lt h1, ne_of_abs_lt (h1.trans h2), ?_⟩,
      ⟨ne_of_abs_lt h2, (ne_of_abs_lt h3).symm⟩, (ne_of_abs_lt (h3.trans h2)).symm, by simp⟩
    intro e; rw [div_eq_div_iff ha hb] at e; exact hb3 (by linear_combination e)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl)
    exacts [one_lt_abs_div ha hab, one_lt_abs_div ha (hab.trans hbc),
      one_lt_abs_div ha ((hab.trans hbc).trans hcd), one_lt_abs_div hb hbc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl) <;> exact Finset.div_mem_div (by simp) (by simp)

-- One product coincidence `c * c = a * d`; the quotient `d / b` is neither `b / a` nor `c / a`.
private theorem not_isMPTQSet_four_lt_of_sq_right {a b c d : ℝ} (ha : a ≠ 0) (hab : |a| < |b|)
    (hbc : |b| < |c|) (hcd : |c| < |d|) (hR : a * d ≠ b * c) (hb2 : b * b ≠ a * d)
    (hc2 : c * c = a * d) : ¬ IsMPTQSet ({a, b, c, d} : Finset ℝ) := by
  have hb : b ≠ 0 := ne_zero_of_abs_lt hab
  have hd : d ≠ 0 := ne_zero_of_abs_lt (hbc.trans hcd)
  have h1 := abs_div_lt_abs_div_left ha hbc
  have h2 := abs_div_lt_abs_div_left ha hcd
  have h3 := abs_div_lt_abs_div_right hd ha hab
  have hM : (({a, b, c, d} : Finset ℝ) * {a, b, c, d}).card ≤ 9 := by
    refine (Finset.card_le_card ((mul_subset_four a b c d).trans ?_)).trans
      (List.toFinset_card_le [a * a, a * b, a * c, a * d, b * b, b * c, b * d, c * d, d * d])
    intro p hp
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hc2]
  refine not_isMPTQSet_of_list_one [b / a, c / a, d / a, d / b] ha (by simp) hM ?_ ?_ ?_
    (by simp)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ne_of_abs_lt h1, ne_of_abs_lt (h1.trans h2), ?_⟩,
      ⟨ne_of_abs_lt h2, ?_⟩, (ne_of_abs_lt h3).symm, by simp⟩
    · intro e; rw [div_eq_div_iff ha hb] at e; exact hb2 (by linear_combination e)
    · intro e; rw [div_eq_div_iff ha hb] at e; exact hR (by linear_combination -e)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl)
    exacts [one_lt_abs_div ha hab, one_lt_abs_div ha (hab.trans hbc),
      one_lt_abs_div ha ((hab.trans hbc).trans hcd), one_lt_abs_div hb (hbc.trans hcd)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl) <;> exact Finset.div_mem_div (by simp) (by simp)

-- No product coincidence: five quotients of absolute value greater than `1` are distinct.
private theorem not_isMPTQSet_four_lt_generic {a b c d : ℝ} (ha : a ≠ 0) (hab : |a| < |b|)
    (hbc : |b| < |c|) (hcd : |c| < |d|) (hR : a * d ≠ b * c) (hb2 : b * b ≠ a * d)
    (hc2 : c * c ≠ a * d) : ¬ IsMPTQSet ({a, b, c, d} : Finset ℝ) := by
  have hb : b ≠ 0 := ne_zero_of_abs_lt hab
  have hc : c ≠ 0 := ne_zero_of_abs_lt hbc
  have hd : d ≠ 0 := ne_zero_of_abs_lt hcd
  have h1 := abs_div_lt_abs_div_left ha hbc
  have h2 := abs_div_lt_abs_div_left ha hcd
  have h3 := abs_div_lt_abs_div_right hd ha hab
  have h4 := abs_div_lt_abs_div_right hd hb hbc
  refine not_isMPTQSet_of_list_one [b / a, c / a, d / a, d / b, d / c] ha (by simp)
    (card_mul_le_ten a b c d) ?_ ?_ ?_ (by simp)
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨ne_of_abs_lt h1, ne_of_abs_lt (h1.trans h2), ?_, ?_⟩,
      ⟨ne_of_abs_lt h2, ?_, ?_⟩, ⟨(ne_of_abs_lt h3).symm, (ne_of_abs_lt (h4.trans h3)).symm⟩,
      (ne_of_abs_lt h4).symm, by simp⟩
    · intro e; rw [div_eq_div_iff ha hb] at e; exact hb2 (by linear_combination e)
    · intro e; rw [div_eq_div_iff ha hc] at e; exact hR (by linear_combination -e)
    · intro e; rw [div_eq_div_iff ha hb] at e; exact hR (by linear_combination -e)
    · intro e; rw [div_eq_div_iff ha hc] at e; exact hc2 (by linear_combination e)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl)
    exacts [one_lt_abs_div ha hab, one_lt_abs_div ha (hab.trans hbc),
      one_lt_abs_div ha ((hab.trans hbc).trans hcd), one_lt_abs_div hb (hbc.trans hcd),
      one_lt_abs_div hc hcd]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl) <;> exact Finset.div_mem_div (by simp) (by simp)

private theorem not_isMPTQSet_four_lt {a b c d : ℝ} (ha : a ≠ 0) (hab : |a| < |b|)
    (hbc : |b| < |c|) (hcd : |c| < |d|) : ¬ IsMPTQSet ({a, b, c, d} : Finset ℝ) := by
  have hb : b ≠ 0 := ne_zero_of_abs_lt hab
  have hc : c ≠ 0 := ne_zero_of_abs_lt hbc
  have hd : d ≠ 0 := ne_zero_of_abs_lt hcd
  -- Of the pairings of four distinct products, only `a * d = b * c` can hold.
  by_cases hR : a * d = b * c
  · refine not_isMPTQSet_of_div_mem (mul_ne_zero ha hd) ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl | rfl | rfl)
    · right; right; right; field_simp
    · right; right; left; field_simp; linear_combination hR
    · right; left; field_simp; linear_combination hR
    · left; field_simp
  by_cases hb2 : b * b = a * d
  · exact not_isMPTQSet_four_lt_of_sq_left ha hab hbc hcd hb2
  by_cases hc2 : c * c = a * d
  · exact not_isMPTQSet_four_lt_of_sq_right ha hab hbc hcd hR hb2 hc2
  exact not_isMPTQSet_four_lt_generic ha hab hbc hcd hR hb2 hc2

private theorem not_isMPTQSet_four_sorted {a b c d : ℝ} (ha : a ≠ 0) (hab' : a ≠ b)
    (hac' : a ≠ c) (hbc' : b ≠ c) (hbd' : b ≠ d) (hcd' : c ≠ d) (hab : |a| ≤ |b|)
    (hbc : |b| ≤ |c|) (hcd : |c| ≤ |d|) : ¬ IsMPTQSet ({a, b, c, d} : Finset ℝ) := by
  rcases hab.lt_or_eq with hab | hab
  · rcases hbc.lt_or_eq with hbc | hbc
    · rcases hcd.lt_or_eq with hcd | hcd
      · exact not_isMPTQSet_four_lt ha hab hbc hcd
      · obtain rfl : c = -d := (abs_eq_abs.mp hcd).resolve_left hcd'
        rw [abs_neg] at hbc
        rw [show ({a, b, -d, d} : Finset ℝ) = {a, b, d, -d} by ext; simp; tauto]
        exact not_isMPTQSet_four_pair_high ha hab hbc
    · obtain rfl : b = -c := (abs_eq_abs.mp hbc).resolve_left hbc'
      rw [abs_neg] at hab
      have hcd : |c| < |d| := hcd.lt_of_ne fun e =>
        hbd' (by rw [(abs_eq_abs.mp e).resolve_left hcd', neg_neg])
      rw [show ({a, -c, c, d} : Finset ℝ) = {a, c, -c, d} by ext; simp; tauto]
      exact not_isMPTQSet_four_pair_mid ha hab hcd
  · obtain rfl : a = -b := (abs_eq_abs.mp hab).resolve_left hab'
    have hb : b ≠ 0 := neg_ne_zero.mp ha
    have hbc : |b| < |c| := hbc.lt_of_ne fun e =>
      hac' (by rw [(abs_eq_abs.mp e).resolve_left hbc', neg_neg])
    rcases hcd.lt_or_eq with hcd | hcd
    · rw [show ({-b, b, c, d} : Finset ℝ) = {b, -b, c, d} by ext; simp; tauto]
      exact not_isMPTQSet_four_pair_low hb hbc hcd
    · obtain rfl : c = -d := (abs_eq_abs.mp hcd).resolve_left hcd'
      rw [show ({-b, b, -d, d} : Finset ℝ) = {b, -b, d, -d} by ext; simp; tauto]
      exact not_isMPTQSet_four_pairs hb (neg_ne_zero.mp (ne_zero_of_abs_lt hbc))

/-! ### Listing a set by absolute value -/

private theorem exists_eq_pair_abs_le {B : Finset ℝ} (h : B.card = 2) :
    ∃ a b, B = {a, b} ∧ a ≠ b ∧ |a| ≤ |b| := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h
  rcases le_total |x| |y| with hle | hle
  · exact ⟨x, y, rfl, hxy, hle⟩
  · exact ⟨y, x, Finset.pair_comm x y, hxy.symm, hle⟩

private theorem exists_eq_triple_abs_le {B : Finset ℝ} (h : B.card = 3) :
    ∃ a b c, B = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ |a| ≤ |b| ∧ |b| ≤ |c| := by
  obtain ⟨c, hc, hmax⟩ := B.exists_max_image (|·|) (Finset.card_pos.mp (by omega))
  obtain ⟨a, b, hB, hab, hle⟩ := exists_eq_pair_abs_le (by rw [Finset.card_erase_of_mem hc, h])
  have ha : a ∈ B.erase c := by simp [hB]
  have hb : b ∈ B.erase c := by simp [hB]
  refine ⟨a, b, c, ?_, hab, Finset.ne_of_mem_erase ha, Finset.ne_of_mem_erase hb, hle,
    hmax b (Finset.mem_of_mem_erase hb)⟩
  rw [← Finset.insert_erase hc, hB]
  ext; simp; tauto

private theorem exists_eq_quadruple_abs_le {A : Finset ℝ} (h : A.card = 4) :
    ∃ a b c d, A = {a, b, c, d} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      |a| ≤ |b| ∧ |b| ≤ |c| ∧ |c| ≤ |d| := by
  obtain ⟨d, hd, hmax⟩ := A.exists_max_image (|·|) (Finset.card_pos.mp (by omega))
  obtain ⟨a, b, c, hB, hab, hac, hbc, hle, hle'⟩ :=
    exists_eq_triple_abs_le (by rw [Finset.card_erase_of_mem hd, h])
  have hb : b ∈ A.erase d := by simp [hB]
  have hc : c ∈ A.erase d := by simp [hB]
  refine ⟨a, b, c, d, ?_, hab, hac, hbc, Finset.ne_of_mem_erase hb, Finset.ne_of_mem_erase hc,
    hle, hle', hmax c (Finset.mem_of_mem_erase hc)⟩
  rw [← Finset.insert_erase hd, hB]
  ext; simp; tauto

/-! ### Main results -/

/-- **No MPTQ set has at most four elements.** If $A$ is a finite set of at most four real
numbers, then $A$ is not an MPTQ set.

The two bounds of the source, for sets of positive reals and for sets with a negative element,
together give this statement. The proof of the second bound, by Hùng Việt Chu, *On sets with more
products than quotients*, Rocky Mountain J. Math. 50 (2020), 499–512, treats every set of at
most four nonzero reals.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`).

Source: Hùng Việt Chu, *On sets with more products than quotients*, Rocky Mountain J. Math. 50
(2020), 499–512. -/
public theorem not_isMPTQSet_of_card_le_four {A : Finset ℝ} (hA : A.card ≤ 4) :
    ¬ IsMPTQSet A := by
  intro hM
  have hne {a : ℝ} (ha : a ∈ A) : a ≠ 0 := ne_of_mem_of_not_mem ha hM.1
  obtain h | h | h | h | h : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 ∨ A.card = 3 ∨ A.card = 4 := by
    omega
  · obtain rfl := Finset.card_eq_zero.mp h
    simp [IsMPTQSet] at hM
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact not_isMPTQSet_singleton a hM
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
    have ha : a ≠ 0 := hne (by simp)
    have hb : b ≠ 0 := hne (by simp)
    refine not_isMPTQSet_of_div_mem (mul_ne_zero ha hb) ?_ hM
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl)
    · right; field_simp
    · left; field_simp
  · obtain ⟨a, b, c, rfl, hab, hac, hbc, hle, hle'⟩ := exists_eq_triple_abs_le h
    exact not_isMPTQSet_three_sorted (hne (by simp)) hab hac hbc hle hle' hM
  · obtain ⟨a, b, c, d, rfl, hab, hac, hbc, hbd, hcd, hle, hle', hle''⟩ :=
      exists_eq_quadruple_abs_le h
    exact not_isMPTQSet_four_sorted (hne (by simp)) hab hac hbc hbd hcd hle hle' hle'' hM

-- The negative element is kept from the source's statement; the bound does not need it.
set_option linter.unusedVariables false in
/-- **Chu's bound for MPTQ sets with a negative element.** Every MPTQ set of real numbers that
contains a negative number has at least $5$ elements.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`). -/
public theorem five_le_card_of_isMPTQSet_of_neg {A : Finset ℝ} (hA : IsMPTQSet A)
    (hneg : ∃ a ∈ A, a < 0) : 5 ≤ A.card := by
  by_contra h
  exact not_isMPTQSet_of_card_le_four (by omega) hA

end MetaMathlibExt
