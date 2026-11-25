/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.IrrationalStepProgressions
import Mathlib.Data.Int.Interval

/-!
# Arithmetic progressions with integer start and step

We compare sums and differences in the integer lattice. For a short step the
cross-differences fill an interval; for a long step they can be counted separately.
-/

namespace MetaMathlibExt

open scoped Pointwise

private theorem neg_mem_self_sub {A : Finset ℤ} {z : ℤ} (hz : z ∈ A - A) : -z ∈ A - A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  simpa only [neg_sub] using Finset.sub_mem_sub hb ha

private theorem card_add_le_card_sub_of_small_step {A : Finset ℤ} {n x m d : ℤ}
    (hx₀ : 0 ≤ x) (hx : x < n) (hd : d ≤ n)
    (hI : Finset.Ico 0 n ⊆ A) (hJ : ∀ i ∈ Finset.Icc 0 m, x + i * d ∈ A)
    (hm : 0 ≤ m)
    (hbound : ∀ a ∈ A, 0 ≤ a ∧ a ≤ max (n - 1) (x + m * d)) :
    (A + A).card ≤ (A - A).card := by
  let M := max (n - 1) (x + m * d)
  have hsum : A + A ⊆ Finset.Icc 0 (2 * M) := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
    exact Finset.mem_Icc.mpr ⟨add_nonneg (hbound _ ha).1 (hbound _ hb).1,
      by simpa only [two_mul] using add_le_add (hbound _ ha).2 (hbound _ hb).2⟩
  have covered (z : ℤ) (hz : 0 ≤ z) (i : ℕ) (hi : (i : ℤ) ≤ m)
      (hzi : z ≤ x + (i : ℤ) * d) : z ∈ A - A := by
    induction i with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero] at hzi
      have hstart := hJ 0 (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩)
      simp only [zero_mul, add_zero] at hstart
      exact Finset.mem_sub.mpr ⟨x, hstart, x - z,
        hI (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by omega⟩
    | succ i ih =>
      by_cases hprev : z ≤ x + (i : ℤ) * d
      · exact ih (by omega) hprev
      · let a := x + (i.succ : ℤ) * d
        have ha : a ∈ A := hJ i.succ (Finset.mem_Icc.mpr ⟨by omega, hi⟩)
        have hstep : a = x + (i : ℤ) * d + d := by
          simp only [a, Nat.cast_succ, add_mul, one_mul, add_assoc]
        exact Finset.mem_sub.mpr ⟨a, ha, a - z,
          hI (Finset.mem_Ico.mpr ⟨sub_nonneg.mpr hzi, by omega⟩), by omega⟩
  have hzero : (0 : ℤ) ∈ A := hI (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  have hpositive (z : ℤ) (hz : 0 ≤ z) (hzM : z ≤ M) : z ∈ A - A := by
    by_cases h : z ≤ n - 1
    · simpa only [sub_zero] using
        Finset.sub_mem_sub (hI (Finset.mem_Ico.mpr ⟨hz, by omega⟩)) hzero
    · have hm' := Int.toNat_of_nonneg hm
      apply covered z hz m.toNat (by omega)
      have h' : z ≤ x + m * d := by dsimp [M] at hzM; omega
      rwa [hm']
  have hdiff : Finset.Icc (-M) M ⊆ A - A := by
    intro z hz
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hz
    by_cases h : 0 ≤ z
    · exact hpositive z h hu
    · simpa only [neg_neg] using neg_mem_self_sub (hpositive (-z) (by omega) (by omega))
  calc
    (A + A).card ≤ (Finset.Icc 0 (2 * M)).card := Finset.card_le_card hsum
    _ = (Finset.Icc (-M) M).card := by simp only [Int.card_Icc]; omega
    _ ≤ (A - A).card := Finset.card_le_card hdiff

private theorem card_add_le_card_sub_of_large_step (n m : ℕ) (x d : ℤ)
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hx₀ : 0 ≤ x) (hd : (n : ℤ) < d) :
    let I := Finset.Ico (0 : ℤ) (n : ℤ)
    let B := (Finset.Icc (1 : ℤ) (m : ℤ)).image (fun i => x + i * d)
    ((I ∪ B) + (I ∪ B)).card ≤ ((I ∪ B) - (I ∪ B)).card := by
  dsimp only
  let I := Finset.Ico (0 : ℤ) (n : ℤ)
  let P := Finset.Icc (1 : ℤ) (m : ℤ)
  let B := P.image (fun i => x + i * d)
  let A := I ∪ B
  change (A + A).card ≤ (A - A).card
  have hI : I.card = n := by simp [I]
  have hP : P.card = m := by simp [P]
  have hII : (I + I).card ≤ 2 * n - 1 := by
    have hs : I + I ⊆ Finset.Icc 0 (2 * (n : ℤ) - 2) := by
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
      have ha' := Finset.mem_Ico.mp ha
      have hb' := Finset.mem_Ico.mp hb
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (Finset.card_le_card hs).trans (by simp only [Int.card_Icc]; omega)
  have hBI : (B + I).card ≤ m * n := by
    rw [← hI, ← hP]
    exact Finset.card_add_le.trans (Nat.mul_le_mul_right _ Finset.card_image_le)
  have hBB : (B + B).card ≤ 2 * m - 1 := by
    let C := Finset.Icc (2 : ℤ) (2 * (m : ℤ))
    have hs : B + B ⊆ C.image (fun i => 2 * x + i * d) := by
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      exact Finset.mem_image.mpr ⟨i + j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by
        rw [add_mul]; omega⟩
    calc
      (B + B).card ≤ C.card := (Finset.card_le_card hs).trans Finset.card_image_le
      _ = 2 * m - 1 := by simp only [C, Int.card_Icc]; omega
  have hsum : (A + A).card ≤ (2 * n - 1) + m * n + (2 * m - 1) := by
    have hcover : A + A ⊆ (I + I ∪ (B + I)) ∪ (B + B) := by
      change (I ∪ B) + (I ∪ B) ⊆ _
      rw [Finset.union_add, Finset.add_union, Finset.add_union, add_comm I B]
      exact Finset.union_subset
        (Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left)
          (Finset.subset_union_right.trans Finset.subset_union_left))
        (Finset.union_subset (Finset.subset_union_right.trans Finset.subset_union_left)
          Finset.subset_union_right)
    have h := Finset.card_le_card hcover
    have h₁ := Finset.card_union_le (I + I) (B + I)
    have h₂ := Finset.card_union_le (I + I ∪ (B + I)) (B + B)
    omega
  -- A difference from the positive-index tail determines both of its summands.
  let f : ℤ × ℤ → ℤ := fun (i, a) => x + i * d - a
  let D := (P ×ˢ I).image f
  have hDcard : D.card = m * n := by
    rw [Finset.card_image_of_injOn, Finset.card_product, hP, hI]
    rintro ⟨i, a⟩ hp ⟨j, b⟩ hq heq
    have ha := Finset.mem_Ico.mp (Finset.mem_product.mp hp).2
    have hb := Finset.mem_Ico.mp (Finset.mem_product.mp hq).2
    change x + i * d - a = x + j * d - b at heq
    have separated {u v : ℤ} (huv : u < v) : u * d + d ≤ v * d := by
      have h := mul_le_mul_of_nonneg_right (show u + 1 ≤ v by omega) (show 0 ≤ d by omega)
      simpa only [add_mul, one_mul] using h
    have hij : i = j := by
      rcases lt_trichotomy i j with hij | hij | hij
      · have := separated hij
        omega
      · exact hij
      · have := separated hij
        omega
    subst j
    exact Prod.ext rfl (by omega)
  have hDsub : D ⊆ A - A := by
    intro z hz
    obtain ⟨⟨i, a⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hi, ha⟩ := Finset.mem_product.mp hp
    exact Finset.sub_mem_sub (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
      (Finset.mem_union_left _ ha)
  have hDpos {z : ℤ} (hz : z ∈ D) : 2 ≤ z := by
    obtain ⟨⟨i, a⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hi, ha⟩ := Finset.mem_product.mp hp
    have hb := Finset.mem_Ico.mp ha
    have h := mul_le_mul_of_nonneg_right (Finset.mem_Icc.mp hi).1 (show 0 ≤ d by omega)
    simp only [one_mul] at h
    change 2 ≤ x + i * d - a
    omega
  let E := Finset.Icc (-1 : ℤ) 1
  have hEsub : E ⊆ A - A := by
    intro z hz
    have hz' := Finset.mem_Icc.mp hz
    have hA (a : ℤ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : a ∈ A :=
      Finset.mem_union_left _ (Finset.mem_Ico.mpr ⟨ha₀, by omega⟩)
    exact Finset.mem_sub.mpr ⟨max z 0, hA _ (by omega) (by omega),
      max (-z) 0, hA _ (by omega) (by omega), by omega⟩
  have hdisj₁ : Disjoint D (-D) := by
    rw [Finset.disjoint_left]
    intro z hz hnz
    have hp := hDpos hz
    have hm' := hDpos (Finset.mem_neg'.mp hnz)
    omega
  have hdisj₂ : Disjoint (D ∪ -D) E := by
    rw [Finset.disjoint_left]
    intro z hz he
    have he' := Finset.mem_Icc.mp he
    rcases Finset.mem_union.mp hz with hz | hz
    · have := hDpos hz
      omega
    · have := hDpos (Finset.mem_neg'.mp hz)
      omega
  have hdiff : m * n + m * n + 3 ≤ (A - A).card := by
    have hneg : -D ⊆ A - A := by
      intro z hz
      simpa only [neg_neg] using neg_mem_self_sub (hDsub (Finset.mem_neg'.mp hz))
    have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hDsub hneg) hEsub)
    rw [Finset.card_union_of_disjoint hdisj₂, Finset.card_union_of_disjoint hdisj₁,
      Finset.card_neg, hDcard] at h
    have hE : E.card = 3 := rfl
    rwa [hE] at h
  have hmn : (2 * n - 1) + m * n + (2 * m - 1) ≤ m * n + m * n + 3 := by
    have hsplit : m * n = 2 * n + (m - 2) * n := by
      calc
        m * n = (2 + (m - 2)) * n := by rw [Nat.add_sub_of_le hm]
        _ = _ := Nat.add_mul _ _ _
    have hmul := Nat.mul_le_mul_left (m - 2) (show 2 ≤ n by omega)
    omega
  exact hsum.trans (hmn.trans hdiff)

/-- **Interval plus integer progression starting inside the interval is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x \le n - 1$, the set
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 14
(`integers-2026-A58-lem-14`). -/
public theorem not_isMSTDSet_intervalAP_nat_of_le_sub_one (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx : x ≤ n - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) := by
  classical
  let I := Finset.Ico (0 : ℤ) (n : ℤ)
  let J := (Finset.Icc (0 : ℤ) (m : ℤ)).image (fun i => (x : ℤ) + i * (d : ℤ))
  let A := I ∪ J
  let c := Int.castAddHom ℝ
  have hI : I.image c = realIntervalSet n := by
    simp [I, c, Int.Ico_eq_finset_map, Finset.map_eq_image, Finset.image_image,
      Function.comp_def, realIntervalSet]
  have hJ : J.image c = realAPSet (x : ℝ) m (d : ℝ) := by
    simp [J, c, Int.Icc_eq_finset_map, Finset.map_eq_image, Finset.image_image,
      Function.comp_def, realAPSet, Int.toNat_add]
  rw [IsMSTDSet, ← hI, ← hJ, ← Finset.image_union]
  change ¬ (A.image c - A.image c).card < (A.image c + A.image c).card
  have hsub : A.image c - A.image c = (A - A).image c := by
    simp only [sub_eq_add_neg, Finset.image_add, Finset.image_neg]
  have hc : Function.Injective c := Int.cast_injective
  rw [hsub, ← Finset.image_add c,
    Finset.card_image_of_injective _ hc, Finset.card_image_of_injective _ hc, not_lt]
  by_cases hdn : d ≤ n
  · refine card_add_le_card_sub_of_small_step (x := (x : ℤ)) (m := (m : ℤ)) (d := (d : ℤ))
      (by omega) (by omega) (by omega) Finset.subset_union_left ?_ (by omega) ?_
    · intro i hi
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · have ha' := Finset.mem_Ico.mp ha
        exact ⟨ha'.1, le_max_of_le_left (by omega)⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨h₀, h₁⟩ := Finset.mem_Icc.mp hi
        have hid : i * (d : ℤ) ≤ (m : ℤ) * (d : ℤ) :=
          mul_le_mul_of_nonneg_right h₁ (by omega)
        exact ⟨add_nonneg (by omega) (mul_nonneg h₀ (by omega)), le_max_of_le_right (by omega)⟩
  · let B := (Finset.Icc (1 : ℤ) (m : ℤ)).image (fun i => (x : ℤ) + i * (d : ℤ))
    have hA : A = I ∪ B := by
      ext a
      simp only [A, J, B, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro (ha | ⟨i, ⟨h₀, h₁⟩, rfl⟩)
        · exact Or.inl ha
        · rcases (show i = 0 ∨ 1 ≤ i by omega) with rfl | hi
          · left
            simp only [zero_mul, add_zero]
            exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          · exact Or.inr ⟨i, ⟨hi, h₁⟩, rfl⟩
      · rintro (ha | ⟨i, ⟨h₀, h₁⟩, rfl⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨i, ⟨by omega, h₁⟩, rfl⟩
    rw [hA]
    exact card_add_le_card_sub_of_large_step n m x d hn hm (by omega) (by omega)

end MetaMathlibExt
