/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh
import Mathlib.Data.Set.Card
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-!
# Beatty's theorem and its converse

The converse counts the terms of each sequence below a positive integer cutoff. The resulting
ceiling identity determines the sum of the reciprocals and rules out rational slopes. The other
direction uses Mathlib's Rayleigh theorem for the symmetric difference of the two ranges.

## References

* Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*, INTEGERS **25**
  (2025), Article A104, pp. 1–19, Theorem 1 (Beatty–Rayleigh).
* Lord Rayleigh (J. W. Strutt), *The Theory of Sound*, 2nd ed., vol. I, Macmillan (1894),
  p. 123, for the implication from irrationality and the reciprocal identity to the partition.
* Samuel Beatty, Problem 3173, *American Mathematical Monthly* **33** (1926), p. 159.
  Solutions (printed as Problem 3177, referring back to 3173), *American Mathematical Monthly*
  **34** (1927), pp. 159–160. The converse uses the cutoff-counting idea from the joint solution
  of A. Ostrowski and J. Hyslop on p. 159.
-/

namespace MetaMathlibExt

open Set
open scoped symmDiff

private theorem beattySeq_pos_of_one_le {r : ℝ} (hr : 1 ≤ r) {k : ℤ} (hk : 0 < k) :
    0 < beattySeq r k := by
  rw [beattySeq, Int.floor_pos]
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 1 ≤ k by omega)) hr

private theorem beattySeq_strictMono_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    StrictMono (beattySeq r) := by
  intro i j hij
  have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
  have h : (i : ℝ) * r + 1 ≤ (j : ℝ) * r := calc
    (i : ℝ) * r + 1 ≤ ((i : ℝ) + 1) * r := by linarith only [hr]
    _ ≤ (j : ℝ) * r := mul_le_mul_of_nonneg_right hij' (by positivity)
  have hfloor := Int.floor_le_floor h
  rw [Int.floor_add_one] at hfloor
  simpa only [beattySeq] using (show ⌊(i : ℝ) * r⌋ < ⌊(j : ℝ) * r⌋ by omega)

private theorem one_le_of_beattySeq_subset {r : ℝ}
    (h : {beattySeq r k | k > 0} ⊆ {n : ℤ | 0 < n}) : 1 ≤ r := by
  have h₁ : 0 < beattySeq r 1 := h ⟨1, zero_lt_one, rfl⟩
  simpa only [beattySeq, Int.floor_pos, Int.cast_one, one_mul] using h₁

-- The index interval and the corresponding set of Beatty values have the same size.
private theorem beattySeq_ncard_Ioo {r : ℝ} (hr : 1 ≤ r) {t : ℤ} (ht : 0 < t) :
    ((Ioo 0 t ∩ {beattySeq r k | k > 0}).ncard : ℤ) = ⌈(t : ℝ) * r⁻¹⌉ - 1 := by
  have hr₀ : 0 < r := zero_lt_one.trans_le hr
  have hlt (k : ℤ) : beattySeq r k < t ↔ k < ⌈(t : ℝ) * r⁻¹⌉ := by
    rw [beattySeq, Int.floor_lt, Int.lt_ceil, ← div_eq_mul_inv, lt_div_iff₀ hr₀]
  have himage : beattySeq r '' Ioo (0 : ℤ) ⌈(t : ℝ) * r⁻¹⌉ =
      Ioo 0 t ∩ {beattySeq r k | k > 0} := by
    ext n
    constructor
    · rintro ⟨k, ⟨hk, hkt⟩, rfl⟩
      exact ⟨⟨beattySeq_pos_of_one_le hr hk, (hlt k).2 hkt⟩, ⟨k, hk, rfl⟩⟩
    · rintro ⟨⟨_, hnt⟩, k, hk, rfl⟩
      exact ⟨k, ⟨hk, (hlt k).1 hnt⟩, rfl⟩
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hceil : 0 < ⌈(t : ℝ) * r⁻¹⌉ := Int.ceil_pos.mpr (mul_pos ht' (inv_pos.mpr hr₀))
  rw [← himage, ncard_image_of_injective _ (beattySeq_strictMono_of_one_le hr).injective,
    ← Finset.coe_Ioo, ncard_coe_finset, Int.card_Ioo_of_lt _ _ hceil, sub_zero]

private theorem ceil_add_of_beatty_partition {α β : ℝ}
    (hdisj : Disjoint {beattySeq α k | k > 0} {beattySeq β k | k > 0})
    (hcover : {beattySeq α k | k > 0} ∪ {beattySeq β k | k > 0} = {n : ℤ | 0 < n})
    {t : ℤ} (ht : 0 < t) : ⌈(t : ℝ) * α⁻¹⌉ + ⌈(t : ℝ) * β⁻¹⌉ = t + 1 := by
  have hα := one_le_of_beattySeq_subset (hcover ▸ subset_union_left :
    {beattySeq α k | k > 0} ⊆ {n : ℤ | 0 < n})
  have hβ := one_le_of_beattySeq_subset (hcover ▸ subset_union_right :
    {beattySeq β k | k > 0} ⊆ {n : ℤ | 0 < n})
  let A := Ioo 0 t ∩ {beattySeq α k | k > 0}
  let B := Ioo 0 t ∩ {beattySeq β k | k > 0}
  have hfinite : (Ioo 0 t).Finite := finite_Ioo _ _
  have hunion : A ∪ B = Ioo 0 t := by
    dsimp only [A, B]
    rw [← inter_union_distrib_left, hcover]
    exact inter_eq_left.mpr (fun _ hn ↦ hn.1)
  have hcard : (Ioo 0 t).ncard = A.ncard + B.ncard := by
    rw [← hunion]
    exact ncard_union_eq (hdisj.mono inter_subset_right inter_subset_right)
      (hfinite.subset inter_subset_left) (hfinite.subset inter_subset_left)
  have hcard' : ((Ioo 0 t).ncard : ℤ) = (A.ncard : ℤ) + (B.ncard : ℤ) := by
    exact_mod_cast hcard
  dsimp only [A, B] at hcard'
  rw [beattySeq_ncard_Ioo hα ht, beattySeq_ncard_Ioo hβ ht,
    ← Finset.coe_Ioo, ncard_coe_finset, Int.card_Ioo_of_lt _ _ ht, sub_zero] at hcard'
  omega

private theorem inv_add_inv_of_ceil_add {α β : ℝ}
    (hceil : ∀ t : ℤ, 0 < t → ⌈(t : ℝ) * α⁻¹⌉ + ⌈(t : ℝ) * β⁻¹⌉ = t + 1) :
    α⁻¹ + β⁻¹ = 1 := by
  by_contra hne
  let δ := α⁻¹ + β⁻¹ - 1
  have hδ : 0 < |δ| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨t, ht⟩ := exists_int_gt (1 / |δ|)
  have ht' : 0 < t := by exact_mod_cast ((one_div_pos.mpr hδ).trans ht)
  have hsum : (⌈(t : ℝ) * α⁻¹⌉ : ℝ) + (⌈(t : ℝ) * β⁻¹⌉ : ℝ) = (t : ℝ) + 1 := by
    exact_mod_cast hceil t ht'
  have hlarge := (div_lt_iff₀ hδ).mp ht
  have hround : |(t : ℝ) * δ| ≤ 1 := by
    rw [abs_le, show (t : ℝ) * δ = (t : ℝ) * α⁻¹ + (t : ℝ) * β⁻¹ - t by
      simp only [δ, mul_sub, mul_add, mul_one]]
    constructor
    · linarith only [hsum, Int.ceil_lt_add_one ((t : ℝ) * α⁻¹),
        Int.ceil_lt_add_one ((t : ℝ) * β⁻¹)]
    · linarith only [hsum, Int.le_ceil ((t : ℝ) * α⁻¹), Int.le_ceil ((t : ℝ) * β⁻¹)]
  have ht₀ : (0 : ℝ) ≤ t := by exact_mod_cast ht'.le
  rw [abs_mul, abs_of_nonneg ht₀] at hround
  exact (not_lt_of_ge hround) hlarge

/-- **Beatty's theorem and its converse.** Let $\alpha$ and $\beta$ be positive real numbers. The
set of the numbers $\lfloor k\alpha\rfloor$ for positive integers $k$ and the set of the numbers
$\lfloor k\beta\rfloor$ for positive integers $k$ are disjoint and their union is the set of
positive integers if and only if $\alpha$ is irrational and $\alpha^{-1} + \beta^{-1} = 1$.

The hypothesis $\beta > 0$ cannot be dropped: for irrational $0 < \alpha < 1$ the number $\beta$
with $\alpha^{-1} + \beta^{-1} = 1$ is negative, and the two sets do not partition the positive
integers.

Source: Geremias Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104, Theorem 1 (Beatty–Rayleigh) (`integers-2025-A104-thm-1`). -/
public theorem beatty_complementary_iff_irrational_inv_add_inv {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    (Disjoint {beattySeq α k | k > 0} {beattySeq β k | k > 0} ∧
        {beattySeq α k | k > 0} ∪ {beattySeq β k | k > 0} = {n : ℤ | 0 < n}) ↔
      (Irrational α ∧ α⁻¹ + β⁻¹ = 1) := by
  constructor
  · rintro ⟨hdisj, hcover⟩
    have hceil (t : ℤ) (ht : 0 < t) := ceil_add_of_beatty_partition hdisj hcover ht
    have hsum := inv_add_inv_of_ceil_add hceil
    refine ⟨?_, hsum⟩
    -- At the denominator of a rational reciprocal, the first ceiling has no rounding error.
    suffices h : Irrational (α⁻¹) by simpa only [inv_inv] using h.inv
    rintro ⟨q, hq⟩
    have hden : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
    have hnum : (q.den : ℝ) * α⁻¹ = (q.num : ℝ) := by
      rw [← hq, Rat.cast_def, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr q.den_nz)]
    have hc : (⌈(q.den : ℝ) * α⁻¹⌉ : ℝ) + (⌈(q.den : ℝ) * β⁻¹⌉ : ℝ) =
        (q.den : ℝ) + 1 := by
      exact_mod_cast hceil (q.den : ℤ) hden
    have hmul := congrArg ((q.den : ℝ) * ·) hsum
    rw [mul_add, mul_one, hnum] at hmul
    rw [hnum, Int.ceil_intCast] at hc
    linarith only [hmul, hc, Int.ceil_lt_add_one ((q.den : ℝ) * β⁻¹)]
  · rintro ⟨hirr, hsum⟩
    have hα₁ : 1 < α := (inv_lt_one₀ hα).mp (by linarith only [hsum, inv_pos.mpr hβ])
    have hconj : α.HolderConjugate β := Real.holderConjugate_iff.mpr ⟨hα₁, hsum⟩
    have hdiff := hirr.beattySeq_symmDiff_beattySeq_pos hconj
    have hpos {r : ℝ} (hr : 1 ≤ r) : {beattySeq r k | k > 0} ⊆ {n : ℤ | 0 < n} := by
      rintro n ⟨k, hk, rfl⟩
      exact beattySeq_pos_of_one_le hr hk
    refine ⟨disjoint_left.mpr ?_, subset_antisymm
      (union_subset (hpos hα₁.le) (hpos hconj.symm.lt.le)) ?_⟩
    · intro n hnα hnβ
      have hn := hpos hα₁.le hnα
      rw [← hdiff, mem_symmDiff] at hn
      exact hn.elim (fun h ↦ h.2 hnβ) (fun h ↦ h.2 hnα)
    · rw [← hdiff]
      exact symmDiff_subset_union

end MetaMathlibExt
