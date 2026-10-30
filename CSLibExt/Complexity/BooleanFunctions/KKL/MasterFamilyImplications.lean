/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapAtHalf
public import MathlibExt.Probability.Hypercontractivity.PBiasedTwoPoint
public import MathlibExt.Probability.Hypercontractivity.PBiasedConvexity

@[expose] public section

/-!
# The master family: chord bounds, the dead chord route, and the single-bit test

Chord bounds for convex majorants, the chord route shown dead (`mfp_chord_route_dead`,
`mfp_chord_gap_pos`: the chord gap is positive, so no chord bound closes the estimate),
and the single-bit test predicate `mfp_SingleBitQGt2` (true at `p = 1/2`, false at
`9/10`). `mfp_masterFamily` is the open residue `frh_openResidue`; it implies the KKL
log-gain, martingale hypercontractivity and the Kesten form.

## Main definitions

* `mfp_SingleBitQGt2`: the single-bit test predicate; true at `1/2`, false at `9/10`.
* `mfp_masterFamily`: the open residue (definitionally `frh_openResidue`).

## Main results

* `mfp_chord_route_dead`: the chord route cannot close.
* `mfp_kkl_logGain_of_masterFamily`, `mfp_martingaleHC_of_masterFamily`,
  `mfp_kesten_of_masterFamily`: the conditional chain from the master family.
-/

open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mfp_chord_bound {G : ℝ → ℝ} (hG : ConvexOn ℝ (Icc (0 : ℝ) 1) G) {u anc : ℝ}
    (ha0 : 0 < anc) (ha1 : anc ≤ 1) (hu0 : 0 ≤ u) (hua : u ≤ anc) :
    G u ≤ (1 - u / anc) * G 0 + (u / anc) * G anc := by
  have hmem0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hmema : anc ∈ Icc (0:ℝ) 1 := ⟨ha0.le, ha1⟩
  have hr0 : (0:ℝ) ≤ u / anc := by positivity
  have hr1 : u / anc ≤ 1 := by rw [div_le_one ha0]; exact hua
  have hkey := hG.2 hmem0 hmema (by linarith : (0:ℝ) ≤ 1 - u / anc) hr0
    (by ring : (1 - u / anc) + u / anc = 1)
  have heq : (1 - u / anc) • (0:ℝ) + (u / anc) • anc = u := by
    simp only [smul_eq_mul, mul_zero, zero_add]; field_simp
  rw [heq] at hkey
  simpa only [smul_eq_mul] using hkey

theorem mfp_L_chord_bound [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ((1 - u) + u * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  set Lf := fun v : ℝ => ∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - v) ^ (S.card - 1)
    * (ptn_coeff p f S) ^ 2 with hLf
  have hLconv : ConvexOn ℝ (Icc (0:ℝ) 1) Lf := cvg_L_convexOn p φ
  have hL0 : Lf 0 ≤ T := frh_at_zero hp0 hp1 φ
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hL1 : Lf 1 ≤ δ * T := by
    have hbnd := frh_endpoint_one hp0 hp1 φ
    rw [show δ ^ ((1:ℝ) / (2 - 1)) = δ by rw [show (1:ℝ)/(2-1) = 1 by norm_num, Real.rpow_one]] at hbnd
    exact hbnd
  have hchord := mfp_chord_bound hLconv (anc := 1) (by norm_num) (le_refl _) hu0 hu1
  rw [div_one] at hchord
  calc Lf u ≤ (1 - u) * Lf 0 + u * Lf 1 := hchord
    _ ≤ (1 - u) * T + u * (δ * T) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hL0 (by linarith)
        · exact mul_le_mul_of_nonneg_left hL1 hu0
    _ = ((1 - u) + u * δ) * T := by ring

/-- The chord route cannot close the estimate: the chord gap is positive. -/
theorem mfp_chord_route_dead {T : ℝ} (hT : 0 < T) :
    Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) * T
      < (1 - (1:ℝ) / 2) * T := by
  have hR : Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) = Real.exp (-1) := by
    rw [← Real.exp_mul]; congr 1; norm_num
  rw [hR]
  have hkey : Real.exp (-1) < 1 - (1:ℝ) / 2 := by
    rw [Real.exp_neg, show (1:ℝ) - 1 / 2 = (2:ℝ)⁻¹ by norm_num,
      inv_lt_inv₀ (by positivity) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  exact (mul_lt_mul_of_pos_right hkey hT)

theorem mfp_chord_gap_pos {T : ℝ} (hT : 0 < T) :
    0 < (1 - (1:ℝ) / 2) * T - Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) * T := by
  have := mfp_chord_route_dead hT
  linarith

/-- The single-bit test predicate: a one-coordinate estimate with exponent `q > 2`.
True at `p = 1/2`; false at `p = 9/10` (`mfp2_singleBit_q_gt_2_false`). -/
def mfp_SingleBitQGt2 (p : ℝ) : Prop :=
  ∀ u : ℝ, 0 < u → u < 1 → ∀ u₀ v₀ : ℝ,
    ((1 - p) * u₀ + p * v₀) ^ 2 + (1 - u) * (p * (1 - p)) * (u₀ - v₀) ^ 2
      ≤ ((1 - p) * |u₀| ^ (2 - u) + p * |v₀| ^ (2 - u)) ^ (2 / (2 - u))

theorem mfp_singleBit_q_gt_2_value : mfp_SingleBitQGt2 (1 / 2) := by
  intro u hu0 hu1 u₀ v₀
  set q : ℝ := 2 - u with hq
  have hq1 : 1 ≤ q := by rw [hq]; linarith
  have hq2 : q ≤ 2 := by rw [hq]; linarith
  have hval := pbt_two_point_value_of_core (p := 1 / 2) (q := q)
    (by norm_num) (by norm_num) hq1 hq2 (pcx_OneVarCore (by norm_num) (by norm_num) hq1 hq2)
    (by rw [show (1:ℝ) - 1/2 = 1/2 by norm_num]; exact pcx_OneVarCore (by norm_num) (by norm_num) hq1 hq2) u₀ v₀
  have hcoeff : (q - 1) * 4 * (1 / 2 : ℝ) ^ 2 * (1 - 1 / 2) ^ 2
      = (1 - u) * ((1 / 2 : ℝ) * (1 - 1 / 2)) := by rw [hq]; ring
  rw [hcoeff] at hval
  exact hval

theorem mfp_singleBit_route_dead {p : ℝ} (H : mfp_SingleBitQGt2 p)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (u₀ v₀ : ℝ) :
    ((1 - p) * u₀ + p * v₀) ^ 2 + (1 - u) * (p * (1 - p)) * (u₀ - v₀) ^ 2
      ≤ ((1 - p) * |u₀| ^ (2 - u) + p * |v₀| ^ (2 - u)) ^ (2 / (2 - u)) :=
  H u hu0 hu1 u₀ v₀

/-- The master family predicate: definitionally the open residue `frh_openResidue`. -/
def mfp_masterFamily (q : ℝ) : Prop := frh_openResidue q

theorem mfp_kkl_logGain_of_masterFamily {q : ℝ} (H : mfp_masterFamily q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  vgp2_kkl_logGain_of_master H hp hp1 φ

theorem mfp_martingaleHC_of_masterFamily {q : ℝ} (H : mfp_masterFamily q) :
    mxd_martingaleHC_statement q :=
  frh_martingaleHC_of_openResidue H

theorem mfp_kesten_of_masterFamily {q : ℝ} (H : mfp_masterFamily q)
    {p : ℝ} (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1) :
    KKLHypercontractive p 2 :=
  ptn_kklHC_of_rhoOptimise (mxd_rhoOptimise_of_martingaleHC (mfp_martingaleHC_of_masterFamily H)) hp hp1

theorem mfp_masterFamily_half [Nonempty ι] (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  hcq_smallDelta_p_half φ hu0 hu1

/-- The right-hand side `δ^{u/(2-u)} · totalInfl` of the master-family estimate is nonnegative. -/
theorem mfp_masterFamily_rhs_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool) (u : ℝ) :
    (0 : ℝ)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  apply mul_nonneg
  · exact Real.rpow_nonneg (kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _) _
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _

end StatMech.Probability
