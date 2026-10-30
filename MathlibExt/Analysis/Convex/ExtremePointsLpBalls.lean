/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Extreme points of the unit balls of finite `ℓ¹` and `ℓ^∞` spaces

The extreme points of the closed unit ball of the finite-dimensional space
`PiLp p (fun _ : ι => 𝕜)` are known for `1 < p < ∞` (the ball is strictly
convex, so the extreme points are exactly the unit sphere; see Mathlib's
`StrictConvexSpace.extremePoints_closedBall_eq_sphere`). The two endpoint
cases are not strictly convex, and their extreme points are different:

* for `p = 1`, the extreme points are the unit multiples of the coordinate
  vectors `PiLp.single 1 i c` with `‖c‖ = 1`;
* for `p = ∞`, the extreme points are the vectors all of whose coordinates
  have norm `1`.

This is a companion to the Hahn–Banach / separation material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HahnBanach.lean` and to the
Krein–Milman material (the extreme points here are the building blocks of
the balls, but no Krein–Milman argument is used). It is not one of the 72
v1 targets. The scalar field is `RCLike 𝕜`; the auxiliary instance below
says every `RCLike` field is strictly convex as a real normed space, which
is the strict-convexity input for the coordinatewise arguments.
-/

@[expose] public section

open Set Metric
open scoped ENNReal

namespace MathlibExt.Analysis.Convex.ExtremePointsLpBalls

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Every `RCLike` field is strictly convex as a real normed space: if
`‖x‖ = ‖y‖ = 1` and `‖x + y‖ = 2`, then `x = y`. The proof is the real /
imaginary part computation: `‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 +
2 (re x * re y + im x * im y)`, so the mixed term equals `1`, and then
`‖x - y‖ ^ 2 = 0`. -/
instance : StrictConvexSpace ℝ 𝕜 := by
  apply StrictConvexSpace.of_norm_add
  intro x y hx hy hxy
  have h1 : ‖x + y‖ ^ 2 = 4 := by rw [hxy]; norm_num
  have hx2 : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
  have hy2 : ‖y‖ ^ 2 = 1 := by rw [hy]; norm_num
  rw [RCLike.norm_sq_eq_def] at h1 hx2 hy2
  simp only [map_add] at h1
  have hdot : RCLike.re x * RCLike.re y + RCLike.im x * RCLike.im y = 1 := by
    linear_combination (h1 - hx2 - hy2) / 2
  have hd : x - y = 0 := by
    have h2 : ‖x - y‖ ^ 2 = 0 := by
      rw [RCLike.norm_sq_eq_def]
      simp only [map_sub]
      linear_combination hx2 + hy2 - 2 * hdot
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)
  exact (sub_eq_zero.mp hd) ▸ SameRay.refl x

/-- In a strictly convex scalar field, a convex combination of two unit
vectors of unit norm must have equal endpoints. -/
private theorem eq_of_norm_combo_eq_one {a b : 𝕜} {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (huv : u + v = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (h : ‖u • a + v • b‖ = 1) : a = b := by
  by_contra hne
  have hlt := norm_combo_lt_of_ne ha.le hb.le hne hu hv huv
  rw [h] at hlt
  exact lt_irrefl 1 hlt

/-- If a convex combination of two vectors of norm at most `1` has norm `1`,
then both vectors have norm `1`. -/
private theorem norm_eq_one_of_norm_combo_eq_one {a b : 𝕜} {u v : ℝ} (hu : 0 < u)
    (hv : 0 < v) (huv : u + v = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (h : ‖u • a + v • b‖ = 1) : ‖a‖ = 1 ∧ ‖b‖ = 1 := by
  have hle : ‖u • a + v • b‖ ≤ u * ‖a‖ + v * ‖b‖ := by
    calc ‖u • a + v • b‖ ≤ ‖u • a‖ + ‖v • b‖ := norm_add_le _ _
      _ = u * ‖a‖ + v * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hu.le, Real.norm_of_nonneg hv.le]
  have hle2 : u * ‖a‖ + v * ‖b‖ ≤ 1 := by
    calc u * ‖a‖ + v * ‖b‖ ≤ u * 1 + v * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left ha hu.le)
            (mul_le_mul_of_nonneg_left hb hv.le)
      _ = 1 := by rw [mul_one, mul_one, huv]
  have hEq : u * ‖a‖ + v * ‖b‖ = 1 := by linarith
  constructor
  · by_contra hne
    have hlt : ‖a‖ < 1 := lt_of_le_of_ne ha hne
    have h2 : u * ‖a‖ < u := by
      calc u * ‖a‖ < u * 1 := mul_lt_mul_of_pos_left hlt hu
        _ = u := mul_one u
    have h3 : v * ‖b‖ ≤ v := by
      calc v * ‖b‖ ≤ v * 1 := mul_le_mul_of_nonneg_left hb hv.le
        _ = v := mul_one v
    linarith
  · by_contra hne
    have hlt : ‖b‖ < 1 := lt_of_le_of_ne hb hne
    have h2 : v * ‖b‖ < v := by
      calc v * ‖b‖ < v * 1 := mul_lt_mul_of_pos_left hlt hv
        _ = v := mul_one v
    have h3 : u * ‖a‖ ≤ u := by
      calc u * ‖a‖ ≤ u * 1 := mul_le_mul_of_nonneg_left ha hu.le
        _ = u := mul_one u
    linarith

/-- The extreme points of the closed unit ball of `PiLp ∞ (fun _ : ι => 𝕜)`
are exactly the vectors all of whose coordinates have norm `1`. If some
coordinate has norm `< 1`, a small perturbation of that coordinate stays
in the ball and exhibits the point as a midpoint; conversely, a vector
with all coordinates of norm `1` that is a convex combination of two ball
points must agree with both of them coordinatewise, by strict convexity
of the scalar field. -/
theorem extremePoints_closedBall_piLp_top :
    (Metric.closedBall (0 : PiLp ∞ fun _ : ι => 𝕜) 1).extremePoints ℝ =
      {x | ∀ i, ‖x i‖ = 1} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    rw [mem_extremePoints_iff_left] at hx
    obtain ⟨hxball, hxext⟩ := hx
    have hxnorm : ‖x‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hxball
      exact hxball
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hj⟩ := hcon
    have hjle : ‖x j‖ ≤ 1 := le_trans (PiLp.norm_apply_le x j) hxnorm
    have hjlt : ‖x j‖ < 1 := lt_of_le_of_ne hjle hj
    set t : ℝ := (1 - ‖x j‖) / 2 with ht_def
    have ht : 0 < t := div_pos (by linarith) two_pos
    have hjt : ‖x j‖ + t < 1 := by rw [ht_def]; linarith
    set d : PiLp ∞ fun _ : ι => 𝕜 := PiLp.single ∞ j (t : 𝕜) with hd_def
    have hdj : d j = (t : 𝕜) := by rw [hd_def]; exact PiLp.single_eq_same (β := fun _ : ι => 𝕜) ∞ j (t : 𝕜)
    have hy : x + d ∈ Metric.closedBall (0 : PiLp ∞ fun _ : ι => 𝕜) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_ciSup]
      apply ciSup_le
      intro i
      by_cases hij : i = j
      · rw [hij, PiLp.add_apply, hdj]
        calc ‖x j + (t : 𝕜)‖ ≤ ‖x j‖ + ‖(t : 𝕜)‖ := norm_add_le _ _
          _ = ‖x j‖ + t := by rw [RCLike.norm_ofReal, abs_of_nonneg ht.le]
          _ ≤ 1 := hjt.le
      · have hdi : d i = 0 := PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) ∞ (Ne.symm hij) (t : 𝕜)
        rw [PiLp.add_apply, hdi, add_zero]
        exact le_trans (PiLp.norm_apply_le x i) hxnorm
    have hz : x - d ∈ Metric.closedBall (0 : PiLp ∞ fun _ : ι => 𝕜) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_ciSup]
      apply ciSup_le
      intro i
      by_cases hij : i = j
      · rw [hij, PiLp.sub_apply, hdj]
        calc ‖x j - (t : 𝕜)‖ ≤ ‖x j‖ + ‖(t : 𝕜)‖ := norm_sub_le _ _
          _ = ‖x j‖ + t := by rw [RCLike.norm_ofReal, abs_of_nonneg ht.le]
          _ ≤ 1 := hjt.le
      · have hdi : d i = 0 := PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) ∞ (Ne.symm hij) (t : 𝕜)
        rw [PiLp.sub_apply, hdi, sub_zero]
        exact le_trans (PiLp.norm_apply_le x i) hxnorm
    have hmem : x ∈ openSegment ℝ (x + d) (x - d) := mem_openSegment_add_sub x d
    have hEq := hxext (x + d) hy (x - d) hz hmem
    have hd0 : d = 0 := add_eq_left.mp hEq
    have h0 : (t : 𝕜) = 0 := by
      have h1 : d j = (0 : PiLp ∞ fun _ : ι => 𝕜) j := congrArg (fun w => w j) hd0
      rw [hdj] at h1
      simpa using h1
    exact (ne_of_gt ht) (RCLike.ofReal_eq_zero.mp h0)
  · intro hx
    rw [mem_extremePoints_iff_left]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_ciSup]
      simp only [hx, ciSup_const, le_refl]
    · intro y hy z hz hmem
      obtain ⟨a, b, ha, hb, hab, hxyz⟩ := hmem
      have hynorm : ‖y‖ ≤ 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        exact hy
      have hznorm : ‖z‖ ≤ 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact hz
      apply PiLp.ext
      intro i
      have hcoord : a • y i + b • z i = x i :=
        congrArg (fun w : PiLp ∞ fun _ : ι => 𝕜 => w i) hxyz
      have hynormi : ‖y i‖ ≤ 1 := le_trans (PiLp.norm_apply_le y i) hynorm
      have hznormi : ‖z i‖ ≤ 1 := le_trans (PiLp.norm_apply_le z i) hznorm
      have hnorm1 :=
        norm_eq_one_of_norm_combo_eq_one ha hb hab hynormi hznormi (by rw [hcoord, hx i])
      obtain ⟨hy1, hz1⟩ := hnorm1
      have hEq : y i = z i :=
        eq_of_norm_combo_eq_one ha hb hab hy1 hz1 (by rw [hcoord, hx i])
      rw [← hcoord, ← hEq, ← add_smul, hab, one_smul]

/-- The `ℓ¹` norm of `x` perturbed at two distinct coordinates, computed by
splitting the sum over the two coordinates and the rest. -/
private theorem norm_add_single_sub_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝕜 : Type*} [RCLike 𝕜] {i j : ι} (hij : i ≠ j)
    (x : PiLp 1 fun _ : ι => 𝕜) (a b : 𝕜) :
    ‖x + (PiLp.single 1 i a - PiLp.single 1 j b)‖ =
      ‖x‖ - ‖x i‖ - ‖x j‖ + ‖x i + a‖ + ‖x j - b‖ := by
  set d : PiLp 1 fun _ : ι => 𝕜 := PiLp.single 1 i a - PiLp.single 1 j b with hd_def
  have hsum : ∀ f : ι → ℝ,
      ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩), add_assoc]
  have h1 := hsum (fun k : ι => ‖(x + d) k‖)
  have h2 := hsum (fun k => ‖x k‖)
  have hi : (x + d) i = x i + a := by
    rw [hd_def, PiLp.add_apply, PiLp.sub_apply, PiLp.single_eq_same,
      PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 (Ne.symm hij) b, sub_zero]
  have hj : (x + d) j = x j - b := by
    rw [hd_def, PiLp.add_apply, PiLp.sub_apply,
      PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 hij a,
      PiLp.single_eq_same, zero_sub, sub_eq_add_neg]
  have hpt : ∀ k ∈ (Finset.univ.erase i).erase j,
      ‖(x + d) k‖ = ‖x k‖ := by
    intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkj, hki⟩ := hk
    rw [Finset.mem_erase] at hki
    obtain ⟨hki', -⟩ := hki
    have hk0 : (x + d) k = x k := by
      rw [hd_def, PiLp.add_apply, PiLp.sub_apply,
        PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 (Ne.symm hki') a,
        PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 (Ne.symm hkj) b, sub_zero, add_zero]
    rw [hk0]
  have hsum2 := Finset.sum_congr rfl (fun k hk => hpt k hk)
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1, h1, h2, hi, hj]
  linarith [hsum2]

/-- The extreme points of the closed unit ball of `PiLp 1 (fun _ : ι => 𝕜)`
are exactly the unit multiples of the coordinate vectors. The proof: an
extreme point must have norm `1` (otherwise a one-coordinate perturbation
stays in the ball and exhibits it as a midpoint), and it cannot have two
nonzero coordinates (otherwise mass can be transferred between them, in
the direction of the phases of the two coordinates, staying at norm `1`
on both sides). Conversely, a unit multiple of a coordinate vector is
extreme: a convex combination equalling it must have total norm `1`,
hence coordinatewise triangle equality, hence vanishing off the
coordinate, and strict convexity of the scalar field at the coordinate. -/
theorem extremePoints_closedBall_piLp_one :
    (Metric.closedBall (0 : PiLp 1 fun _ : ι => 𝕜) 1).extremePoints ℝ =
      {x | ∃ i, ∃ c : 𝕜, ‖c‖ = 1 ∧ x = PiLp.single 1 i c} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    rw [mem_extremePoints_iff_left] at hx
    obtain ⟨hxball, hxext⟩ := hx
    have hxnorm : ‖x‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hxball
      exact hxball
    have hnorm1 : ‖x‖ = 1 := by
      by_contra hne
      have hlt : ‖x‖ < 1 := lt_of_le_of_ne hxnorm hne
      obtain ⟨i₀⟩ := ‹Nonempty ι›
      set t : ℝ := (1 - ‖x‖) / 2 with ht_def
      have ht : 0 < t := div_pos (by linarith) two_pos
      set d : PiLp 1 fun _ : ι => 𝕜 := PiLp.single 1 i₀ (t : 𝕜) with hd_def
      have hnormd : ‖d‖ = t := by
        rw [hd_def, PiLp.norm_single 1 (fun _ : ι => 𝕜) i₀ (t : 𝕜), RCLike.norm_ofReal,
          abs_of_nonneg ht.le]
      have hy : x + d ∈ Metric.closedBall (0 : PiLp 1 fun _ : ι => 𝕜) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖x + d‖ ≤ ‖x‖ + ‖d‖ := norm_add_le _ _
          _ = ‖x‖ + t := by rw [hnormd]
          _ ≤ 1 := by rw [ht_def]; linarith
      have hz : x - d ∈ Metric.closedBall (0 : PiLp 1 fun _ : ι => 𝕜) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖x - d‖ ≤ ‖x‖ + ‖d‖ := norm_sub_le _ _
          _ = ‖x‖ + t := by rw [hnormd]
          _ ≤ 1 := by rw [ht_def]; linarith
      have hmem : x ∈ openSegment ℝ (x + d) (x - d) := mem_openSegment_add_sub x d
      have hEq := hxext (x + d) hy (x - d) hz hmem
      have hd0 : d = 0 := add_eq_left.mp hEq
      have h0 : (t : 𝕜) = 0 := by
        have h1 : d i₀ = (0 : PiLp 1 fun _ : ι => 𝕜) i₀ := congrArg (fun w => w i₀) hd0
        rw [PiLp.single_eq_same (β := fun _ : ι => 𝕜) 1 i₀ (t : 𝕜)] at h1
        simpa using h1
      exact (ne_of_gt ht) (RCLike.ofReal_eq_zero.mp h0)
    have hne_zero : ∃ i₀, x i₀ ≠ 0 := by
      by_contra h
      push Not at h
      have hx0 : x = 0 :=
        PiLp.ext fun i => by simp [h i]
      rw [hx0, norm_zero] at hnorm1
      exact zero_ne_one hnorm1
    obtain ⟨i₀, hi₀⟩ := hne_zero
    have hsupp : ∃ i, ∀ k, k ≠ i → x k = 0 := by
      by_contra h
      push Not at h
      obtain ⟨j, hji, hj⟩ := h i₀
      set δ : ℝ := min ‖x i₀‖ ‖x j‖ / 2 with hδ_def
      have hδpos : 0 < δ := by
        rw [hδ_def]
        exact div_pos (lt_min (norm_pos_iff.mpr hi₀) (norm_pos_iff.mpr hj)) two_pos
      have hδi : δ < ‖x i₀‖ := by
        rw [hδ_def]
        linarith [min_le_left ‖x i₀‖ ‖x j‖, norm_pos_iff.mpr hi₀]
      have hδj : δ < ‖x j‖ := by
        rw [hδ_def]
        linarith [min_le_right ‖x i₀‖ ‖x j‖, norm_pos_iff.mpr hj]
      set u_i : 𝕜 := (‖x i₀‖⁻¹ : ℝ) • x i₀ with hu_i_def
      set u_j : 𝕜 := (‖x j‖⁻¹ : ℝ) • x j with hu_j_def
      have hui : ‖x i₀‖ • u_i = x i₀ := by
        rw [hu_i_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hi₀), one_smul]
      have huj : ‖x j‖ • u_j = x j := by
        rw [hu_j_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hj), one_smul]
      have hnorm_ui : ‖u_i‖ = 1 := by
        rw [hu_i_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hi₀)]
      have hnorm_uj : ‖u_j‖ = 1 := by
        rw [hu_j_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hj)]
      set d : PiLp 1 fun _ : ι => 𝕜 :=
        PiLp.single 1 i₀ (δ • u_i) - PiLp.single 1 j (δ • u_j) with hd_def
      have hci : x i₀ + δ • u_i = (‖x i₀‖ + δ) • u_i := by
        conv_rhs => rw [add_smul]
        rw [hui]
      have hcj : x j - δ • u_j = (‖x j‖ - δ) • u_j := by
        conv_rhs => rw [sub_smul]
        rw [huj]
      have hmi : x i₀ - δ • u_i = (‖x i₀‖ - δ) • u_i := by
        conv_rhs => rw [sub_smul]
        rw [hui]
      have hmj : x j + δ • u_j = (‖x j‖ + δ) • u_j := by
        conv_rhs => rw [add_smul]
        rw [huj]
      have hnorm_ci : ‖x i₀ + δ • u_i‖ = ‖x i₀‖ + δ := by
        rw [hci, norm_smul, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hδpos.le),
          hnorm_ui, mul_one]
      have hnorm_cj : ‖x j - δ • u_j‖ = ‖x j‖ - δ := by
        rw [hcj, norm_smul, Real.norm_of_nonneg (by linarith), hnorm_uj, mul_one]
      have hnorm_mi : ‖x i₀ - δ • u_i‖ = ‖x i₀‖ - δ := by
        rw [hmi, norm_smul, Real.norm_of_nonneg (by linarith), hnorm_ui, mul_one]
      have hnorm_mj : ‖x j + δ • u_j‖ = ‖x j‖ + δ := by
        rw [hmj, norm_smul, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) hδpos.le),
          hnorm_uj, mul_one]
      have hnorm_pd : ‖x + d‖ = 1 := by
        rw [hd_def, norm_add_single_sub_single (Ne.symm hji) x (δ • u_i) (δ • u_j), hnorm_ci,
          hnorm_cj, hnorm1]
        ring
      have hnorm_md : ‖x - d‖ = 1 := by
        have hneg : x - d =
            x + (PiLp.single 1 j (δ • u_j) - PiLp.single 1 i₀ (δ • u_i)) := by
          rw [hd_def, sub_eq_add_neg, neg_sub]
        rw [hneg, norm_add_single_sub_single hji x (δ • u_j) (δ • u_i), hnorm_mj,
          hnorm_mi, hnorm1]
        ring
      have hyball : x + d ∈ Metric.closedBall (0 : PiLp 1 fun _ : ι => 𝕜) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, hnorm_pd]
      have hzball : x - d ∈ Metric.closedBall (0 : PiLp 1 fun _ : ι => 𝕜) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, hnorm_md]
      have hmem : x ∈ openSegment ℝ (x + d) (x - d) := mem_openSegment_add_sub x d
      have hEq := hxext (x + d) hyball (x - d) hzball hmem
      have hd0 : d = 0 := add_eq_left.mp hEq
      have hdi : d i₀ = δ • u_i := by
        rw [hd_def, PiLp.sub_apply, PiLp.single_eq_same,
          PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 hji (δ • u_j), sub_zero]
      have hne0 : δ • u_i ≠ 0 := by
        have hnorm : ‖δ • u_i‖ = δ := by
          rw [norm_smul, Real.norm_of_nonneg hδpos.le, hnorm_ui, mul_one]
        intro hzero
        rw [hzero, norm_zero] at hnorm
        exact (ne_of_gt hδpos) hnorm.symm
      have hcontra : δ • u_i = 0 := by
        rw [← hdi, hd0]
        exact PiLp.zero_apply (fun _ : ι => 𝕜) i₀
      exact hne0 hcontra
    obtain ⟨i, hsupp_i⟩ := hsupp
    have hx_eq : x = PiLp.single 1 i (x i) := by
      apply PiLp.ext
      intro k
      by_cases hki : k = i
      · subst hki
        rw [PiLp.single_eq_same]
      · rw [hsupp_i k hki, PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 (Ne.symm hki) (x i)]
    refine ⟨i, x i, ?_, ?_⟩
    · calc ‖x i‖ = ‖PiLp.single 1 i (x i)‖ := (PiLp.norm_single 1 (fun _ : ι => 𝕜) i (x i)).symm
        _ = ‖x‖ := by rw [hx_eq]
        _ = 1 := hnorm1
    · exact hx_eq

  · rintro ⟨i, c, hc, rfl⟩
    rw [mem_extremePoints_iff_left]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, PiLp.norm_single]
      exact hc.le
    · intro y hy z hz hmem
      obtain ⟨a, b, ha, hb, hab, hxyz⟩ := hmem
      have hynorm : ‖y‖ ≤ 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hy
        exact hy
      have hznorm : ‖z‖ ≤ 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact hz
      have hnorm1 : ‖y‖ = 1 ∧ ‖z‖ = 1 := by
        have hsum : ‖a • y + b • z‖ = 1 := by
          rw [hxyz, PiLp.norm_single]
          exact hc
        have hle : ‖a • y + b • z‖ ≤ a * ‖y‖ + b * ‖z‖ := by
          calc ‖a • y + b • z‖ ≤ ‖a • y‖ + ‖b • z‖ := norm_add_le _ _
            _ = a * ‖y‖ + b * ‖z‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le,
                Real.norm_of_nonneg hb.le]
        have hle2 : a * ‖y‖ + b * ‖z‖ ≤ 1 := by
          calc a * ‖y‖ + b * ‖z‖ ≤ a * 1 + b * 1 :=
                add_le_add (mul_le_mul_of_nonneg_left hynorm ha.le)
                  (mul_le_mul_of_nonneg_left hznorm hb.le)
            _ = 1 := by rw [mul_one, mul_one, hab]
        have hEq : a * ‖y‖ + b * ‖z‖ = 1 := by linarith
        constructor
        · by_contra hne
          have hlt : ‖y‖ < 1 := lt_of_le_of_ne hynorm hne
          have h2 : a * ‖y‖ < a := by
            calc a * ‖y‖ < a * 1 := mul_lt_mul_of_pos_left hlt ha
              _ = a := mul_one a
          have h3 : b * ‖z‖ ≤ b := by
            calc b * ‖z‖ ≤ b * 1 := mul_le_mul_of_nonneg_left hznorm hb.le
              _ = b := mul_one b
          linarith
        · by_contra hne
          have hlt : ‖z‖ < 1 := lt_of_le_of_ne hznorm hne
          have h2 : b * ‖z‖ < b := by
            calc b * ‖z‖ < b * 1 := mul_lt_mul_of_pos_left hlt hb
              _ = b := mul_one b
          have h3 : a * ‖y‖ ≤ a := by
            calc a * ‖y‖ ≤ a * 1 := mul_le_mul_of_nonneg_left hynorm ha.le
              _ = a := mul_one a
          linarith
      obtain ⟨hy1, hz1⟩ := hnorm1
      have hcoordEq : ∀ k, ‖a • y k + b • z k‖ = a * ‖y k‖ + b * ‖z k‖ := by
        have hle : ∀ k ∈ Finset.univ,
            ‖a • y k + b • z k‖ ≤ a * ‖y k‖ + b * ‖z k‖ := by
          intro k _
          calc ‖a • y k + b • z k‖ ≤ ‖a • y k‖ + ‖b • z k‖ := norm_add_le _ _
            _ = a * ‖y k‖ + b * ‖z k‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg ha.le,
                Real.norm_of_nonneg hb.le]
        have hsumEq : ∑ k, ‖a • y k + b • z k‖
            = ∑ k, (a * ‖y k‖ + b * ‖z k‖) := by
          have e1 : ∑ k, ‖a • y k + b • z k‖ = ‖a • y + b • z‖ := by
            rw [PiLp.norm_eq_of_L1]
            exact Finset.sum_congr rfl (fun k _ => rfl)
          have e2 : ∑ k, (a * ‖y k‖ + b * ‖z k‖) = a * ‖y‖ + b * ‖z‖ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              ← PiLp.norm_eq_of_L1, ← PiLp.norm_eq_of_L1]
          rw [e1, e2, hxyz, PiLp.norm_single, hc, hy1, hz1, mul_one, mul_one]
          exact hab.symm
        intro k
        exact (Finset.sum_eq_sum_iff_of_le hle).mp hsumEq k (Finset.mem_univ k)
      have hvanish : ∀ k, k ≠ i → y k = 0 ∧ z k = 0 := by
        intro k hki
        have hcoord : a • y k + b • z k = 0 := by
          have h2 := congrArg (fun w : PiLp 1 fun _ : ι => 𝕜 => w k) hxyz
          rw [PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 (Ne.symm hki) c] at h2
          exact h2
        have hEq := hcoordEq k
        rw [hcoord, norm_zero] at hEq
        have hyk : ‖y k‖ = 0 := by
          have h1 : a * ‖y k‖ = 0 := by
            have hnn1 : 0 ≤ a * ‖y k‖ := mul_nonneg ha.le (norm_nonneg _)
            have hnn2 : 0 ≤ b * ‖z k‖ := mul_nonneg hb.le (norm_nonneg _)
            linarith [hEq.symm]
          exact (mul_eq_zero.mp h1).resolve_left ha.ne'
        have hzk : ‖z k‖ = 0 := by
          have h1 : b * ‖z k‖ = 0 := by
            have hnn1 : 0 ≤ a * ‖y k‖ := mul_nonneg ha.le (norm_nonneg _)
            have hnn2 : 0 ≤ b * ‖z k‖ := mul_nonneg hb.le (norm_nonneg _)
            linarith [hEq.symm]
          exact (mul_eq_zero.mp h1).resolve_left hb.ne'
        exact ⟨norm_eq_zero.mp hyk, norm_eq_zero.mp hzk⟩
      have hcoordi : a • y i + b • z i = c := by
        have h2 := congrArg (fun w : PiLp 1 fun _ : ι => 𝕜 => w i) hxyz
        rw [PiLp.single_eq_same (β := fun _ : ι => 𝕜) 1 i c] at h2
        exact h2
      have hynormi : ‖y i‖ ≤ 1 := le_trans (PiLp.norm_apply_le y i) hy1.le
      have hznormi : ‖z i‖ ≤ 1 := le_trans (PiLp.norm_apply_le z i) hz1.le
      have hnorm1i :=
        norm_eq_one_of_norm_combo_eq_one ha hb hab hynormi hznormi (by rw [hcoordi, hc])
      obtain ⟨hyi1, hzi1⟩ := hnorm1i
      have hEqi : y i = z i :=
        eq_of_norm_combo_eq_one ha hb hab hyi1 hzi1 (by rw [hcoordi, hc])
      apply PiLp.ext
      intro k
      by_cases hki : k = i
      · subst hki
        rw [PiLp.single_eq_same]
        rw [← hEqi] at hcoordi
        rw [← add_smul, hab, one_smul] at hcoordi
        exact hcoordi
      · have h0 := (hvanish k hki).1
        rw [h0, PiLp.single_eq_of_ne' (β := fun _ : ι => 𝕜) 1 (Ne.symm hki) c]

end MathlibExt.Analysis.Convex.ExtremePointsLpBalls
