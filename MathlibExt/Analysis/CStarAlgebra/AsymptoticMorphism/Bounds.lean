/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Unitization

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Order.LatticeIntervals
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Non-circular orbit boundedness and asymptotic contractivity

The first tail bound follows from a positive pair of actual image squares.
Small star errors are retained multiplied by the unknown image norms until
an elementary quadratic estimate bounds both images. Only then are the
errors made arbitrarily small. Stock unitization and zero-normalization
reduce arbitrary nonunital families to this argument.

The compact initial interval provides the global bound. No Cb/C0 quotient,
given orbit bound, linear slice, Source theorem or nontriviality premise is
used, and all norms and C-star orders are the actual stock dictionaries.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter

noncomputable section

namespace AsymptoticMorphism

universe uA uB

attribute [local instance]
  CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

section Unital

variable {A : Type uA} {B : Type uB}
variable [CStarAlgebra A] [CStarAlgebra B]

private theorem norm_gram_error_le (φ : AsymptoticMorphism A B)
    (t : AsymptoticTime) (a : A) :
    ‖star (φ t a) * φ t a - φ t (star a * a)‖ ≤
      ‖φ t (star a) - star (φ t a)‖ * ‖φ t a‖ +
        ‖φ t (star a * a) - φ t (star a) * φ t a‖ := by
  have heq :
      star (φ t a) * φ t a - φ t (star a * a) =
        (star (φ t a) - φ t (star a)) * φ t a +
          (φ t (star a) * φ t a - φ t (star a * a)) := by
    rw [sub_mul]
    abel
  rw [heq]
  calc
    ‖(star (φ t a) - φ t (star a)) * φ t a +
        (φ t (star a) * φ t a - φ t (star a * a))‖ ≤
      ‖(star (φ t a) - φ t (star a)) * φ t a‖ +
        ‖φ t (star a) * φ t a - φ t (star a * a)‖ := norm_add_le _ _
    _ ≤ ‖star (φ t a) - φ t (star a)‖ * ‖φ t a‖ +
        ‖φ t (star a) * φ t a - φ t (star a * a)‖ :=
      add_le_add (norm_mul_le _ _)
        (le_refl ‖φ t (star a) * φ t a - φ t (star a * a)‖)
    _ = _ := by
      rw [norm_sub_rev (star (φ t a)) (φ t (star a)),
        norm_sub_rev (φ t (star a) * φ t a) (φ t (star a * a))]

private theorem norm_square_pair_le (T S : B) :
    (max ‖T‖ ‖S‖) ^ 2 ≤ ‖star T * T + star S * S‖ := by
  have hT : ‖T‖ * ‖T‖ ≤ ‖star T * T + star S * S‖ := by
    have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (le_add_of_nonneg_right (star_mul_self_nonneg S))
      (star_mul_self_nonneg T)
    simpa only [CStarRing.norm_star_mul_self] using h
  have hS : ‖S‖ * ‖S‖ ≤ ‖star T * T + star S * S‖ := by
    have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (le_add_of_nonneg_left (star_mul_self_nonneg T))
      (star_mul_self_nonneg S)
    simpa only [CStarRing.norm_star_mul_self] using h
  rcases le_total ‖T‖ ‖S‖ with h | h
  · simpa only [max_eq_right h, pow_two] using hS
  · simpa only [max_eq_left h, pow_two] using hT

private theorem eventually_pair_estimate (φ : AsymptoticMorphism A B)
    (hunit : ∀ t : AsymptoticTime, φ t 1 = 1)
    (a x : A) (hax : star a * a + star x * x = 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t : AsymptoticTime in atTop,
      ‖(star (φ t a) * φ t a + star (φ t x) * φ t x) - 1‖ ≤
        3 * δ + δ * (‖φ t a‖ + ‖φ t x‖) := by
  have hsa : ∀ᶠ t : AsymptoticTime in atTop,
      ‖φ t (star a) - star (φ t a)‖ < δ := by
    simpa only [toFun_eq_coe, dist_zero_right] using
      Metric.tendsto_nhds.mp (φ.star_defect_tendsto a) δ hδ
  have hsx : ∀ᶠ t : AsymptoticTime in atTop,
      ‖φ t (star x) - star (φ t x)‖ < δ := by
    simpa only [toFun_eq_coe, dist_zero_right] using
      Metric.tendsto_nhds.mp (φ.star_defect_tendsto x) δ hδ
  have hma : ∀ᶠ t : AsymptoticTime in atTop,
      ‖φ t (star a * a) - φ t (star a) * φ t a‖ < δ := by
    simpa only [toFun_eq_coe, dist_zero_right] using
      Metric.tendsto_nhds.mp (φ.mul_defect_tendsto (star a) a) δ hδ
  have hmx : ∀ᶠ t : AsymptoticTime in atTop,
      ‖φ t (star x * x) - φ t (star x) * φ t x‖ < δ := by
    simpa only [toFun_eq_coe, dist_zero_right] using
      Metric.tendsto_nhds.mp (φ.mul_defect_tendsto (star x) x) δ hδ
  have hadd : ∀ᶠ t : AsymptoticTime in atTop,
      ‖φ t (star a * a + star x * x) -
        (φ t (star a * a) + φ t (star x * x))‖ < δ := by
    simpa only [toFun_eq_coe, dist_zero_right] using
      Metric.tendsto_nhds.mp (φ.add_defect_tendsto (star a * a) (star x * x)) δ hδ
  filter_upwards [hsa, hsx, hma, hmx, hadd] with t hsa hsx hma hmx hadd
  have heq :
      (star (φ t a) * φ t a + star (φ t x) * φ t x) - 1 =
        (star (φ t a) * φ t a - φ t (star a * a)) +
        (star (φ t x) * φ t x - φ t (star x * x)) +
        ((φ t (star a * a) + φ t (star x * x)) -
          φ t (star a * a + star x * x)) := by
    rw [hax, hunit t]
    abel
  rw [heq]
  calc
    ‖(star (φ t a) * φ t a - φ t (star a * a)) +
        (star (φ t x) * φ t x - φ t (star x * x)) +
        ((φ t (star a * a) + φ t (star x * x)) -
          φ t (star a * a + star x * x))‖ ≤
      (‖star (φ t a) * φ t a - φ t (star a * a)‖ +
        ‖star (φ t x) * φ t x - φ t (star x * x)‖) +
        ‖(φ t (star a * a) + φ t (star x * x)) -
          φ t (star a * a + star x * x)‖ :=
      (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _)
          (le_refl ‖(φ t (star a * a) + φ t (star x * x)) -
            φ t (star a * a + star x * x)‖))
    _ ≤
      (‖φ t (star a) - star (φ t a)‖ * ‖φ t a‖ +
        ‖φ t (star a * a) - φ t (star a) * φ t a‖) +
      (‖φ t (star x) - star (φ t x)‖ * ‖φ t x‖ +
        ‖φ t (star x * x) - φ t (star x) * φ t x‖) +
      ‖φ t (star a * a + star x * x) -
        (φ t (star a * a) + φ t (star x * x))‖ := by
      rw [norm_sub_rev (φ t (star a * a) + φ t (star x * x))
        (φ t (star a * a + star x * x))]
      exact add_le_add
        (add_le_add (norm_gram_error_le φ t a) (norm_gram_error_le φ t x))
        (le_refl ‖φ t (star a * a + star x * x) -
          (φ t (star a * a) + φ t (star x * x))‖)
    _ ≤ (δ * ‖φ t a‖ + δ) + (δ * ‖φ t x‖ + δ) + δ :=
      add_le_add
        (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_right hsa.le (norm_nonneg _)) hma.le)
          (add_le_add (mul_le_mul_of_nonneg_right hsx.le (norm_nonneg _)) hmx.le))
        hadd.le
    _ = _ := by ring

private theorem eventually_norm_lt_one_of_unital (φ : AsymptoticMorphism A B)
    (hunit : ∀ t : AsymptoticTime, φ t 1 = 1)
    (a : A) (ha : ‖a‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : AsymptoticTime in atTop, ‖φ t a‖ < 1 + ε := by
  have hle : star a * a ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a)).1 (by
      rw [CStarRing.norm_star_mul_self]
      simpa only [one_mul] using mul_self_le_mul_self (norm_nonneg a) ha)
  let x := CFC.sqrt (1 - star a * a)
  have hx : star x * x = 1 - star a * a := by
    rw [(CFC.sqrt_nonneg (1 - star a * a)).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hle)
  have hax : star a * a + star x * x = 1 := by
    rw [hx]
    abel
  have hone : ‖(1 : B)‖ ≤ 1 := by
    have heq : ‖(1 : B)‖ = ‖(1 : B)‖ * ‖(1 : B)‖ := by
      simpa only [star_one, one_mul] using
        (CStarRing.norm_star_mul_self (x := (1 : B)))
    by_contra hn
    have hgt : 1 < ‖(1 : B)‖ := lt_of_not_ge hn
    have hpos : 0 < ‖(1 : B)‖ := zero_lt_one.trans hgt
    have hm : ‖(1 : B)‖ < ‖(1 : B)‖ * ‖(1 : B)‖ := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hgt hpos
    exact (not_lt_of_ge heq.ge) hm
  have hcoarse : ∀ᶠ t : AsymptoticTime in atTop, ‖φ t a‖ ≤ 2 ∧ ‖φ t x‖ ≤ 2 := by
    filter_upwards [eventually_pair_estimate φ hunit a x hax (1 / 8) (by norm_num)]
      with t ht
    let M := max ‖φ t a‖ ‖φ t x‖
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (le_max_left _ _)
    have hsum : ‖φ t a‖ + ‖φ t x‖ ≤ M + M :=
      add_le_add (le_max_left _ _) (le_max_right _ _)
    have hupper : M * M ≤ 1 + 3 / 8 + M / 4 := by
      calc
        M * M ≤ ‖star (φ t a) * φ t a + star (φ t x) * φ t x‖ := by
          simpa only [M, pow_two] using norm_square_pair_le (φ t a) (φ t x)
        _ ≤ ‖(star (φ t a) * φ t a + star (φ t x) * φ t x) - 1‖ + ‖(1 : B)‖ := by
          simpa only [sub_add_cancel] using
            (norm_add_le
              ((star (φ t a) * φ t a + star (φ t x) * φ t x) - 1) (1 : B))
        _ ≤ 3 * (1 / 8) + (1 / 8) * (M + M) + 1 :=
          add_le_add
            (ht.trans (add_le_add (le_refl (3 * (1 / 8) : ℝ))
              (mul_le_mul_of_nonneg_left hsum
                (show (0 : ℝ) ≤ (1 / 8 : ℝ) from by norm_num)))) hone
        _ = _ := by ring
    have hM2 : M ≤ 2 := by
      by_contra hnot
      have hgt : 2 < M := lt_of_not_ge hnot
      have hmul : 2 * M ≤ M * M :=
        mul_le_mul_of_nonneg_right hgt.le hM0
      nlinarith [hupper, hmul]
    exact ⟨(le_max_left _ _).trans hM2, (le_max_right _ _).trans hM2⟩
  have hδ : 0 < ε / 7 := div_pos hε (by norm_num)
  filter_upwards [hcoarse, eventually_pair_estimate φ hunit a x hax (ε / 7) hδ]
    with t ht he
  have hupper : ‖φ t a‖ * ‖φ t a‖ ≤ 1 + ε := by
    calc
      ‖φ t a‖ * ‖φ t a‖ ≤ ‖star (φ t a) * φ t a + star (φ t x) * φ t x‖ := by
        have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
          (le_add_of_nonneg_right (star_mul_self_nonneg (φ t x)))
          (star_mul_self_nonneg (φ t a))
        simpa only [CStarRing.norm_star_mul_self] using h
      _ ≤ ‖(star (φ t a) * φ t a + star (φ t x) * φ t x) - 1‖ + ‖(1 : B)‖ := by
        simpa only [sub_add_cancel] using
          (norm_add_le
            ((star (φ t a) * φ t a + star (φ t x) * φ t x) - 1) (1 : B))
      _ ≤ 3 * (ε / 7) + (ε / 7) * (2 + 2) + 1 :=
        add_le_add
          (he.trans (add_le_add (le_refl (3 * (ε / 7)))
            (mul_le_mul_of_nonneg_left (add_le_add ht.1 ht.2) hδ.le))) hone
      _ = _ := by ring
  by_contra hnot
  have hgt : 1 + ε ≤ ‖φ t a‖ := le_of_not_gt hnot
  have hprod : (1 + ε) * (1 + ε) ≤ ‖φ t a‖ * ‖φ t a‖ :=
    mul_self_le_mul_self (by linarith) hgt
  nlinarith [hupper, hprod, sq_nonneg ε]

private theorem eventually_unital_norm_lt (φ : AsymptoticMorphism A B)
    (hunit : ∀ t : AsymptoticTime, φ t 1 = 1)
    (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : AsymptoticTime in atTop, ‖φ t a‖ < ‖a‖ + ε := by
  by_cases ha : a = 0
  · subst a
    simpa only [dist_zero_right, norm_zero, zero_add] using
      Metric.tendsto_nhds.mp φ.zero_tendsto ε hε
  let r := ‖a‖
  have hr : 0 < r := norm_pos_iff.mpr ha
  let b : A := ((r⁻¹ : ℝ) : ℂ) • a
  have hb : ‖b‖ ≤ 1 := by
    dsimp only [b]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹ * r ≤ 1
    exact (inv_mul_cancel₀ hr.ne').le
  have hbr : (r : ℂ) • b = a := by
    dsimp only [b]
    rw [smul_smul]
    have hc : (r : ℂ) * ((r⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one]
    rw [hc, one_smul]
  have hd : ∀ᶠ t : AsymptoticTime in atTop,
      ‖φ t a - (r : ℂ) • φ t b‖ < ε / 2 := by
    simpa only [toFun_eq_coe, hbr, dist_zero_right] using
      Metric.tendsto_nhds.mp (φ.smul_defect_tendsto (r : ℂ) b)
        (ε / 2) (half_pos hε)
  have hsmall := eventually_norm_lt_one_of_unital φ hunit b hb
    (ε / (2 * r)) (div_pos hε (mul_pos (by norm_num) hr))
  filter_upwards [hd, hsmall] with t hd ht
  have hn : ‖(r : ℂ) • φ t b‖ = r * ‖φ t b‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  calc
    ‖φ t a‖ ≤ ‖φ t a - (r : ℂ) • φ t b‖ + ‖(r : ℂ) • φ t b‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (φ t a - (r : ℂ) • φ t b) ((r : ℂ) • φ t b)
    _ < ε / 2 + r * (1 + ε / (2 * r)) :=
      add_lt_add hd (by rw [hn]; exact mul_lt_mul_of_pos_left ht hr)
    _ = ‖a‖ + ε := by
      have hc : r * (ε / (2 * r)) = ε / 2 := by
        field_simp [hr.ne']
      rw [mul_add, mul_one, hc]
      dsimp only [r]
      ring

end Unital

section Nonunital

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

private theorem eventually_raw_norm_lt (φ : AsymptoticMorphism A B)
    (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : AsymptoticTime in atTop, ‖φ t a‖ < ‖a‖ + ε := by
  have hu := eventually_unital_norm_lt (unitization (normalize φ))
    (unitization_normalize_one φ) (Unitization.inr a)
    (ε / 2) (half_pos hε)
  have hsmall : ∀ᶠ t : AsymptoticTime in atTop,
      ‖normalize φ t a‖ < ‖a‖ + ε / 2 := by
    simpa only [unitization_inr_apply, Unitization.norm_inr] using hu
  have hz : ∀ᶠ t : AsymptoticTime in atTop, ‖φ t 0‖ < ε / 2 := by
    simpa only [dist_zero_right] using
      Metric.tendsto_nhds.mp φ.zero_tendsto (ε / 2) (half_pos hε)
  filter_upwards [hsmall, hz] with t ht hz
  calc
    ‖φ t a‖ = ‖normalize φ t a + φ t 0‖ := by
      rw [normalize_apply, sub_add_cancel]
    _ ≤ ‖normalize φ t a‖ + ‖φ t 0‖ := norm_add_le _ _
    _ < (‖a‖ + ε / 2) + ε / 2 := add_lt_add ht hz
    _ = _ := by ring

/-- Every actual raw orbit is globally bounded and sharply asymptotically
contractive. These are conclusions, never additional raw-family fields. -/
theorem norm_bounded_and_eventually_contractive (φ : AsymptoticMorphism A B) (a : A) :
    (∃ C : ℝ, ∀ t : AsymptoticTime, ‖φ t a‖ ≤ C) ∧
      ∀ ε : ℝ, 0 < ε →
        Filter.Eventually (fun t : AsymptoticTime => ‖φ t a‖ < ‖a‖ + ε) Filter.atTop := by
  have hsharp := eventually_raw_norm_lt φ a
  refine ⟨?_, hsharp⟩
  let t0 : AsymptoticTime := ⟨1, le_rfl⟩
  let : Nonempty AsymptoticTime := ⟨t0⟩
  obtain ⟨T, hT⟩ := Filter.mem_atTop_sets.mp (hsharp 1 zero_lt_one)
  have hK : IsCompact (Set.Icc t0 T) := by
    apply Subtype.isCompact_iff.mpr
    have himage : Subtype.val '' (Set.Icc t0 T : Set AsymptoticTime) =
        Set.Icc (1 : ℝ) (T : ℝ) := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hs
        exact ⟨⟨s, hs.1⟩, hs, rfl⟩
    rw [himage]
    exact isCompact_Icc
  obtain ⟨C, hC⟩ := hK.bddAbove_image (φ.continuous_orbit a).norm.continuousOn
  refine ⟨max C (‖a‖ + 1), fun t => ?_⟩
  by_cases ht : t ≤ T
  · have htK : t ∈ Set.Icc t0 T := ⟨t.property, ht⟩
    exact (hC (Set.mem_image_of_mem (fun s : AsymptoticTime => ‖φ s a‖) htK)).trans
      (le_max_left _ _)
  · exact (hT t (le_of_not_ge ht)).le.trans (le_max_right _ _)

end Nonunital

end AsymptoticMorphism
