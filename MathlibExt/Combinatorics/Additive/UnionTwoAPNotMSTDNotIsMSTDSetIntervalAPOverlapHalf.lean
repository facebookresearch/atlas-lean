/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.IrrationalStepProgressions
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# An integer interval and a half-integer arithmetic progression
-/

namespace MetaMathlibExt

open scoped Pointwise

private theorem interval_coverage (N d : ℤ) (m : ℕ)
    (hd : d ≤ N) (q : ℤ) (hq : 0 ≤ q ∧ q ≤ N + m * d) :
    ∃ i j : ℤ, (0 ≤ i ∧ i ≤ N) ∧ (0 ≤ j ∧ j ≤ m) ∧ q = i + j * d := by
  induction m generalizing q with
  | zero =>
    refine ⟨q, 0, ?_, ?_, ?_⟩ <;> simp_all
  | succ m ih =>
    by_cases hq' : q ≤ N + m * d
    · obtain ⟨i, j, hi, hj, he⟩ := ih q ⟨hq.1, hq'⟩
      exact ⟨i, j, hi, ⟨hj.1, by exact_mod_cast (show j ≤ (m : ℤ) + 1 by omega)⟩, he⟩
    · refine ⟨q - (m + 1) * d, m + 1, ?_, ?_, ?_⟩
      · push_cast at hq ⊢
        rw [add_mul, one_mul] at hq ⊢
        omega
      · push_cast; omega
      · ring

private theorem shifted_union_card (N m d a : ℤ) :
    let E := Finset.Icc (-N) N ∪ (Finset.Icc (-m) m).image (fun k => k * d)
    let F := Finset.Icc 0 (2 * N) ∪
      (Finset.Icc 0 (2 * m)).image (fun k => a + k * d)
    (F.card : ℤ) ≤ E.card + |a + m * d - N| := by
  classical
  intro E F
  let r := a + m * d - N
  have hinj : Function.Injective (fun z : ℤ => z - (a + m * d)) := by
    intro i j h; exact sub_left_inj.mp h
  by_cases hr : 0 ≤ r
  · let B := Finset.Icc (-N - r) (-N - 1)
    have hsub : F.image (fun z => z - (a + m * d)) ⊆ E ∪ B := by
      intro z hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      rcases Finset.mem_union.mp hk with hk | hk
      · simp only [Finset.mem_Icc] at hk
        simp only [E, B, Finset.mem_union, Finset.mem_Icc]
        dsimp [r] at hr ⊢
        by_cases h : -N ≤ k - (a + m * d)
        · exact Or.inl (Or.inl ⟨h, by omega⟩)
        · exact Or.inr ⟨by omega, by omega⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨j - m, ?_, ?_⟩
        · simp only [Finset.mem_Icc] at hj ⊢; omega
        · ring
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hc
    have hu := Finset.card_union_le E B
    have hb : (B.card : ℤ) = r := by
      simp only [B, Int.card_Icc]
      omega
    rw [abs_of_nonneg hr]
    exact_mod_cast (show (F.card : ℤ) ≤ E.card + r by omega)
  · let B := Finset.Icc (N + 1) (N - r)
    have hsub : F.image (fun z => z - (a + m * d)) ⊆ E ∪ B := by
      intro z hz
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      rcases Finset.mem_union.mp hk with hk | hk
      · simp only [Finset.mem_Icc] at hk
        simp only [E, B, Finset.mem_union, Finset.mem_Icc]
        dsimp [r] at hr ⊢
        by_cases h : k - (a + m * d) ≤ N
        · exact Or.inl (Or.inl ⟨by omega, h⟩)
        · exact Or.inr ⟨by omega, by omega⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨j - m, ?_, ?_⟩
        · simp only [Finset.mem_Icc] at hj ⊢; omega
        · ring
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hc
    have hu := Finset.card_union_le E B
    have hb : (B.card : ℤ) = -r := by
      simp only [B, Int.card_Icc]
      omega
    rw [abs_of_nonpos (show r ≤ 0 by omega)]
    exact_mod_cast (show (F.card : ℤ) ≤ E.card - r by omega)

private def integerModel (N d s : ℤ) (m : ℕ) : Finset ℤ :=
  (Finset.Icc 0 N).image (fun i => 2 * i) ∪
    (Finset.Icc 0 (m : ℤ)).image (fun j => 2 * s + 1 + 2 * (j * d))

private theorem integerModel_card (N d s : ℤ) (m : ℕ) (hm : 0 ≤ (m : ℤ))
    (hd : 0 ≤ d) (hdN : d ≤ N) (hs : 0 ≤ s) (hsN : s < N) :
    let T := integerModel N d s m
    (T + T).card ≤ (T - T).card := by
  classical
  let T := integerModel N d s m
  change (T + T).card ≤ (T - T).card
  let t := (m : ℤ) * d
  let a := 2 * s + 1
  let E := Finset.Icc (-N) N ∪
    (Finset.Icc (-(m : ℤ)) (m : ℤ)).image (fun k => k * d)
  let F := Finset.Icc 0 (2 * N) ∪
    (Finset.Icc 0 (2 * (m : ℤ))).image (fun k => a + k * d)
  let C := Finset.Icc s (s + N + t)
  let h := max (s + t) (N - s - 1)
  let H := Finset.Icc (-h - 1) h
  have ht : 0 ≤ t := mul_nonneg hm hd
  have hinj₀ : Function.Injective (fun k : ℤ => 2 * k) := by
    intro i j hij; dsimp at hij; omega
  have hinj₁ : Function.Injective (fun k : ℤ => 2 * k + 1) := by
    intro i j hij; dsimp at hij; omega
  have hsum : T + T ⊆ F.image (fun k => 2 * k) ∪ C.image (fun k => 2 * k + 1) := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hz
    simp only [T, integerModel, Finset.mem_union, Finset.mem_image,
      Finset.mem_Icc] at hu hv
    rcases hu with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
      rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨i + j, ?_, by ring⟩
      exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨s + i + j * d, ?_, by ring⟩
      have hj₀ := mul_nonneg hj.1 hd
      have hj₁ := mul_le_mul_of_nonneg_right hj.2 hd
      exact Finset.mem_Icc.mpr ⟨by omega, by dsimp [C, t]; omega⟩
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨s + j + i * d, ?_, by ring⟩
      have hi₀ := mul_nonneg hi.1 hd
      have hi₁ := mul_le_mul_of_nonneg_right hi.2 hd
      exact Finset.mem_Icc.mpr ⟨by omega, by dsimp [C, t]; omega⟩
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨a + (i + j) * d, ?_, ?_⟩
      · apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨i + j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
      · dsimp [a]; ring
  have memI (i : ℤ) (hi : 0 ≤ i ∧ i ≤ N) : 2 * i ∈ T :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr hi, rfl⟩)
  have memP (j : ℤ) (hj : 0 ≤ j ∧ j ≤ m) : a + 2 * (j * d) ∈ T :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr hj, rfl⟩)
  have hdiff₀ : E.image (fun k => 2 * k) ⊆ T - T := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_union.mp hk with hk | hk
    · have hk' := Finset.mem_Icc.mp hk
      refine Finset.mem_sub.mpr ⟨_, memI (max k 0) ⟨by omega, by omega⟩,
        _, memI (max (-k) 0) ⟨by omega, by omega⟩, ?_⟩
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have hj' := Finset.mem_Icc.mp hj
      refine Finset.mem_sub.mpr ⟨_, memP (max j 0) ⟨by omega, by omega⟩,
        _, memP (max (-j) 0) ⟨by omega, by omega⟩, ?_⟩
      have he : max j 0 - max (-j) 0 = j := by omega
      linear_combination 2 * d * he
  have cross (k : ℤ) (hk : s - N ≤ k ∧ k ≤ s + t) : 2 * k + 1 ∈ T - T := by
    obtain ⟨i, j, hi, hj, he⟩ := interval_coverage N d m hdN
      (k - s + N) ⟨by omega, by dsimp [t] at hk; omega⟩
    refine Finset.mem_sub.mpr ⟨_, memP j hj, _, memI (N - i) ⟨by omega, by omega⟩, ?_⟩
    dsimp [a]
    linear_combination -2 * he
  have hdiff₁ : H.image (fun k => 2 * k + 1) ⊆ T - T := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hk' := Finset.mem_Icc.mp hk
    by_cases hc : s - N ≤ k ∧ k ≤ s + t
    · exact cross k hc
    · have hn : s - N ≤ -k - 1 ∧ -k - 1 ≤ s + t := by
        dsimp [H, h] at hk'
        omega
      obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_sub.mp (cross (-k - 1) hn)
      exact Finset.mem_sub.mpr ⟨v, hv, u, hu, by omega⟩
  have hdisj : Disjoint (E.image (fun k => 2 * k)) (H.image (fun k => 2 * k + 1)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz'
    omega
  have hsCard := Finset.card_le_card hsum
  have hsUnion := Finset.card_union_le (F.image (fun k => 2 * k))
    (C.image (fun k => 2 * k + 1))
  rw [Finset.card_image_of_injective _ hinj₀,
    Finset.card_image_of_injective _ hinj₁] at hsUnion
  have hdCard := Finset.card_le_card (Finset.union_subset hdiff₀ hdiff₁)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj₀,
    Finset.card_image_of_injective _ hinj₁] at hdCard
  have hF := shifted_union_card N (m : ℤ) d a
  change (F.card : ℤ) ≤ E.card + |a + t - N| at hF
  have hC : (C.card : ℤ) = N + t + 1 := by
    simp only [C, Int.card_Icc]; omega
  have hH : (H.card : ℤ) = N + t + 1 + |a + t - N| := by
    simp only [H, Int.card_Icc]
    dsimp [h, a]
    rw [abs_eq_max_neg]
    omega
  omega

private theorem int_interval_nat (n : ℕ) :
    Finset.Icc (0 : ℤ) ((n : ℤ) - 1) = (Finset.range n).image (fun i : ℕ => (i : ℤ)) := by
  ext i
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hi
    exact ⟨i.toNat, by omega, Int.toNat_of_nonneg hi.1⟩
  · rintro ⟨j, hj, rfl⟩
    omega

private noncomputable def evalHalf : ℤ →+ ℝ where
  toFun z := (z : ℝ) / 2
  map_zero' := by simp
  map_add' u v := by simp [Int.cast_add, add_div]

private theorem evalHalf_injective : Function.Injective evalHalf := by
  intro i j hij
  change (i : ℝ) / 2 = (j : ℝ) / 2 at hij
  have he : (i : ℝ) = j := by linarith
  exact_mod_cast he

private theorem image_integerModel (n m d s : ℕ) (x : ℝ) (hxs : x = s + 1 / 2) :
    (integerModel ((n : ℤ) - 1) d s m).image evalHalf =
      realIntervalSet n ∪ realAPSet x m (d : ℝ) := by
  classical
  have hmI : Finset.Icc (0 : ℤ) (m : ℤ) =
      (Finset.range (m + 1)).image (fun i : ℕ => (i : ℤ)) := by
    simpa using int_interval_nat (m + 1)
  rw [integerModel, Finset.image_union, int_interval_nat, hmI]
  simp only [Finset.image_image, Function.comp_def]
  congr 1
  · unfold realIntervalSet
    apply Finset.image_congr
    intro i hi
    change ((2 * (i : ℤ) : ℤ) : ℝ) / 2 = (i : ℝ)
    push_cast
    ring
  · unfold realAPSet
    apply Finset.image_congr
    intro i hi
    change ((2 * (s : ℤ) + 1 + 2 * ((i : ℤ) * (d : ℤ)) : ℤ) : ℝ) / 2 =
      x + (i : ℝ) * (d : ℝ)
    rw [hxs]
    push_cast
    ring

/-- **Interval plus integer-step progression with half-integer start is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. Let $n \ge 3$, $m \ge 2$, $s$ and $d$ be natural numbers with
$2 \le d \le n - 1$, and let $x = s + 1/2$. If $x < n - 1$, then $I_n \cup J(x, m, d)$ is not an
MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 16
(`integers-2026-A58-lem-16`). -/
public theorem not_isMSTDSet_intervalAP_overlap_half (n m d s : ℕ) (x : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd₁ : 2 ≤ d)
    (hd₂ : d ≤ n - 1) (hxs : x = s + 1 / 2) (hx : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ)) := by
  have hd : 0 ≤ (d : ℤ) := by omega
  have hdN : (d : ℤ) ≤ (n : ℤ) - 1 := by omega
  have hs : 0 ≤ (s : ℤ) := Int.natCast_nonneg s
  have hsN : (s : ℤ) < (n : ℤ) - 1 := by
    have hr : (s : ℝ) < (n : ℝ) - 1 := by rw [hxs] at hx; linarith
    exact_mod_cast hr
  have hbound := integerModel_card ((n : ℤ) - 1) d s m
    (by exact_mod_cast le_trans (Nat.zero_le 2) hm) hd hdN hs hsN
  have hSub (T : Finset ℤ) :
      T.image evalHalf - T.image evalHalf = (T - T).image evalHalf := by
    simp only [sub_eq_add_neg, Finset.image_add, Finset.image_neg]
  rw [IsMSTDSet, ← image_integerModel n m d s x hxs, ← Finset.image_add evalHalf,
    hSub, Finset.card_image_of_injective _ evalHalf_injective,
    Finset.card_image_of_injective _ evalHalf_injective, not_lt]
  exact hbound

end MetaMathlibExt
