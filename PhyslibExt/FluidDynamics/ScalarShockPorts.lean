/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PhyslibExt.ContinuumMechanics.ControlVolumes

/-!
# Scalar shocks: jump relations for one-dimensional conservation laws

## i. Overview

Fields are time first, `u t x`. A scalar conservation law `u_t + f(u)_x = 0` is considered on
either side of a moving interface `x = s t`, with left state `uL` and right state `uR`; jumps are
right minus left, `[g] = g uR - g uL`. The results are model statements about fields with the
stated regularity; no existence of such solutions is asserted.

Part A proves the Rankine-Hugoniot equivalence from two classical sides. The equation holds
classically on each side of an interface that is differentiable at time `t` with speed `c` and
lies strictly inside a fixed interval `[a, b]`; each side field is only assumed regular on an open
set around its closed side slice, so its one-sided trace at the interface is a value of a
continuous field. Then the mass on `[a, b]` changes at the conservation rate
`f (uL t a) - f (uR t b)` exactly when `c * [u] = [f]` at the interface. The proof extends each
side field from its open set to the whole plane by composing with a time compression that is the
identity near `t` and a spatial clamp, applies the moving interface transport theorem
`ControlVolumes.movingJumpTransport` to the extensions, and turns the time-derivative integrals
into flux differences with the fundamental theorem of calculus and the side equations.

## ii. Key results

- `ScalarShock.conservation_iff_rankineHugoniot`: conservation on a fixed interval crossing the
  interface is equivalent to the Rankine-Hugoniot jump identity `c * (uR - uL) = f uR - f uL`.

## iii. Table of contents

- A. Rankine-Hugoniot from two classical sides

## iv. References

- `ControlVolumes.movingJumpTransport` (`PhyslibExt.ContinuumMechanics.ControlVolumes`).
-/

@[expose] public section

namespace ScalarShock

/-! ## A. Rankine-Hugoniot from two classical sides -/

/-- A closed box around a compact time slice inside an open set. -/
private lemma exists_box_subset {U : Set (ℝ × ℝ)} {t l r : ℝ} (hlr : l ≤ r)
    (hU : IsOpen U) (hK : ({t} : Set ℝ) ×ˢ Set.Icc l r ⊆ U) :
    ∃ δ > 0, ∀ τ x : ℝ, |τ - t| ≤ δ → l - δ ≤ x → x ≤ r + δ → (τ, x) ∈ U := by
  obtain ⟨δ, hδ, hsub⟩ :=
    (isCompact_singleton.prod isCompact_Icc).exists_cthickening_subset_open hU hK
  refine ⟨δ, hδ, fun τ x hτ hx1 hx2 => hsub ?_⟩
  refine Metric.mem_cthickening_of_dist_le (τ, x) (t, max l (min x r)) δ _
    ⟨Set.mem_singleton t, le_max_left _ _, max_le hlr (min_le_right _ _)⟩ ?_
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  refine max_le hτ ?_
  rcases le_total x l with h | h
  · rw [max_eq_left (le_trans (min_le_left _ _) h), abs_le]
    constructor <;> linarith
  · rcases le_total x r with h' | h'
    · rw [min_eq_left h', max_eq_right h, sub_self, abs_zero]
      exact hδ.le
    · rw [min_eq_right h', max_eq_right hlr, abs_le]
      constructor <;> linarith

/-- A `C¹` time compression: the identity near `t`, with all values within `δ` of `t`. -/
private lemma exists_timeMap (t δ : ℝ) (hδ : 0 < δ) :
    ∃ T k : ℝ → ℝ, Continuous k ∧ (∀ τ, HasDerivAt T (k τ) τ) ∧ (∀ τ, |T τ - t| ≤ δ) ∧
      ∀ τ, |τ - t| ≤ δ / 2 → T τ = τ ∧ k τ = 1 := by
  set k : ℝ → ℝ := fun z => max 0 (min 1 (2 - 2 * |z - t| / δ)) with hkdef
  have hk : Continuous k := by fun_prop
  have hk1 : ∀ z, |z - t| ≤ δ / 2 → k z = 1 := by
    intro z hz
    have h : 1 ≤ 2 - 2 * |z - t| / δ := by
      rw [le_sub_comm, div_le_iff₀ hδ]
      linarith
    simp only [hkdef, min_eq_left h, max_eq_right zero_le_one]
  have hk0 : ∀ z, δ ≤ |z - t| → k z = 0 := by
    intro z hz
    have h : 2 - 2 * |z - t| / δ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hδ]
      linarith
    simp only [hkdef]
    exact max_eq_left (le_trans (min_le_right _ _) h)
  have hkb : ∀ z, ‖k z‖ ≤ 1 := by
    intro z
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : (0 : ℝ) ≤ k z := le_max_left _ _
      linarith
    · exact max_le zero_le_one (min_le_left _ _)
  refine ⟨fun τ => t + ∫ z in t..τ, k z, k, hk, fun τ => ?_, fun τ => ?_, fun τ hτ => ?_⟩
  · exact ((hk.integral_hasStrictDerivAt t τ).hasDerivAt).const_add t
  · set m := max (t - δ) (min τ (t + δ)) with hm
    have hsplit : (∫ z in t..τ, k z) = (∫ z in t..m, k z) + ∫ z in m..τ, k z :=
      (intervalIntegral.integral_add_adjacent_intervals (hk.intervalIntegrable _ _)
        (hk.intervalIntegrable _ _)).symm
    have htail : (∫ z in m..τ, k z) = 0 := by
      rcases le_or_gt τ (t - δ) with h1 | h1
      · have hm' : m = t - δ := by rw [hm, min_eq_left (by linarith), max_eq_left h1]
        rw [hm', intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
        · simp
        · intro z hz
          rw [Set.uIcc_of_ge h1] at hz
          change k z = 0
          apply hk0
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hz.2])]
          linarith [hz.2]
      · rcases le_or_gt (t + δ) τ with h2 | h2
        · have hm' : m = t + δ := by rw [hm, min_eq_right h2, max_eq_right (by linarith)]
          rw [hm', intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
          · simp
          · intro z hz
            rw [Set.uIcc_of_le h2] at hz
            change k z = 0
            apply hk0
            rw [abs_of_nonneg (by linarith [hz.1])]
            linarith [hz.1]
        · have hm' : m = τ := by rw [hm, min_eq_left h2.le, max_eq_right h1.le]
          rw [hm', intervalIntegral.integral_same]
    have hmb : |m - t| ≤ δ := by
      rw [abs_le]
      constructor
      · have : t - δ ≤ m := le_max_left _ _
        linarith
      · have : m ≤ t + δ := max_le (by linarith) (min_le_right _ _)
        linarith
    have hhead : ‖∫ z in t..m, k z‖ ≤ 1 * |m - t| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun z _ => hkb z)
    change |t + (∫ z in t..τ, k z) - t| ≤ δ
    rw [add_sub_cancel_left, hsplit, htail, add_zero, ← Real.norm_eq_abs]
    linarith
  · refine ⟨?_, hk1 τ hτ⟩
    change t + (∫ z in t..τ, k z) = τ
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
    · simp
    · intro z hz
      exact hk1 z (le_trans (Set.abs_sub_left_of_mem_uIcc hz) hτ)

/-- Global extension of locally given side data by composing with a time compression `T`
and a continuous clamp `X` whose values keep `(T τ, X x)` inside the open set. -/
private lemma extension_props {U : Set (ℝ × ℝ)} {u v : ℝ → ℝ → ℝ} {T k X : ℝ → ℝ}
    (hju : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) U)
    (hvu : ∀ p ∈ U, HasDerivAt (fun τ : ℝ => u τ p.2) (v p.1 p.2) p.1)
    (hcv : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) U)
    (hk : Continuous k) (hT : ∀ τ, HasDerivAt T (k τ) τ) (hX : Continuous X)
    (hmem : ∀ τ x, (T τ, X x) ∈ U) :
    (Continuous fun p : ℝ × ℝ => u (T p.1) (X p.2)) ∧
      (∀ τ x : ℝ, HasDerivAt (fun σ : ℝ => u (T σ) (X x)) (k τ * v (T τ) (X x)) τ) ∧
      (Continuous fun p : ℝ × ℝ => k p.1 * v (T p.1) (X p.2)) := by
  have hTc : Continuous T := continuous_iff_continuousAt.2 fun τ => (hT τ).continuousAt
  have hmap : Continuous fun p : ℝ × ℝ => (T p.1, X p.2) :=
    (hTc.comp continuous_fst).prodMk (hX.comp continuous_snd)
  refine ⟨hju.comp_continuous hmap (fun p => hmem p.1 p.2), fun τ x => ?_,
    (hk.comp continuous_fst).mul (hcv.comp_continuous hmap (fun p => hmem p.1 p.2))⟩
  have h1 : HasDerivAt (fun σ : ℝ => u σ (X x)) (v (T τ) (X x)) (T τ) := hvu _ (hmem τ x)
  exact h1.scomp τ (hT τ)

/-- Rankine-Hugoniot from two classical sides.

A scalar conservation law `u_t + f(u)_x = 0` holds classically on each side
of an interface `x = s τ` that is differentiable at time `t` with speed `c`
and lies strictly inside the fixed interval `[a, b]`. The left state is a
field `uL` that is jointly continuous, with jointly continuous time partial
`vL`, on an open set `UL` containing the closed left slice `{t} × [a, s t]`
(a smooth neighbourhood reaching across the interface, so the one-sided
trace `uL t (s t)` is a value of a continuous field); symmetrically `uR`,
`vR` on `UR ⊇ {t} × [s t, b]`. At time `t` the spatial flux derivatives
`gL`, `gR` exist on the open side intervals, the flux composites are
continuous on the closed side intervals, and the side equations
`vL t x + gL x = 0`, `vR t x + gR x = 0` hold on the open side intervals.

Then the split mass on `[a, b]` changes at the conservation rate
`f (uL t a) - f (uR t b)` (flux in at `a` minus flux out at `b`) exactly
when the Rankine-Hugoniot jump identity
`c * (uR t (s t) - uL t (s t)) = f (uR t (s t)) - f (uL t (s t))` holds.
No existence of such solutions is asserted. -/
theorem conservation_iff_rankineHugoniot
    {f : ℝ → ℝ} {uL uR vL vR : ℝ → ℝ → ℝ} {gL gR : ℝ → ℝ}
    {s : ℝ → ℝ} {c a b t : ℝ} {UL UR : Set (ℝ × ℝ)}
    (hs : HasDerivAt s c t) (has : a < s t) (hsb : s t < b)
    (hUL : IsOpen UL) (hKL : ({t} : Set ℝ) ×ˢ Set.Icc a (s t) ⊆ UL)
    (hjL : ContinuousOn (fun p : ℝ × ℝ => uL p.1 p.2) UL)
    (hvL : ∀ p ∈ UL, HasDerivAt (fun τ : ℝ => uL τ p.2) (vL p.1 p.2) p.1)
    (hcvL : ContinuousOn (fun p : ℝ × ℝ => vL p.1 p.2) UL)
    (hfL : ContinuousOn (fun y : ℝ => f (uL t y)) (Set.Icc a (s t)))
    (hgL : ∀ x ∈ Set.Ioo a (s t), HasDerivAt (fun y : ℝ => f (uL t y)) (gL x) x)
    (hPDEL : ∀ x ∈ Set.Ioo a (s t), vL t x + gL x = 0)
    (hUR : IsOpen UR) (hKR : ({t} : Set ℝ) ×ˢ Set.Icc (s t) b ⊆ UR)
    (hjR : ContinuousOn (fun p : ℝ × ℝ => uR p.1 p.2) UR)
    (hvR : ∀ p ∈ UR, HasDerivAt (fun τ : ℝ => uR τ p.2) (vR p.1 p.2) p.1)
    (hcvR : ContinuousOn (fun p : ℝ × ℝ => vR p.1 p.2) UR)
    (hfR : ContinuousOn (fun y : ℝ => f (uR t y)) (Set.Icc (s t) b))
    (hgR : ∀ x ∈ Set.Ioo (s t) b, HasDerivAt (fun y : ℝ => f (uR t y)) (gR x) x)
    (hPDER : ∀ x ∈ Set.Ioo (s t) b, vR t x + gR x = 0) :
    HasDerivAt
        (fun τ : ℝ => (∫ x in a..s τ, uL τ x) + (∫ x in s τ..b, uR τ x))
        (f (uL t a) - f (uR t b)) t ↔
      c * (uR t (s t) - uL t (s t)) = f (uR t (s t)) - f (uL t (s t)) := by
  obtain ⟨δL, hδL, hboxL⟩ := exists_box_subset has.le hUL hKL
  obtain ⟨δR, hδR, hboxR⟩ := exists_box_subset hsb.le hUR hKR
  obtain ⟨T, k, hk, hT, hTb, hTid⟩ := exists_timeMap t (min δL δR) (lt_min hδL hδR)
  set δ := min δL δR with hδdef
  have hδ : 0 < δ := lt_min hδL hδR
  have hδL' : δ ≤ δL := min_le_left _ _
  have hδR' : δ ≤ δR := min_le_right _ _
  set XL : ℝ → ℝ := fun x => max (a - δ) (min x (s t + δ)) with hXL
  set XR : ℝ → ℝ := fun x => max (s t - δ) (min x (b + δ)) with hXR
  have hXLc : Continuous XL := by fun_prop
  have hXRc : Continuous XR := by fun_prop
  have hXL_id : ∀ x, a - δ ≤ x → x ≤ s t + δ → XL x = x := fun x h1 h2 => by
    simp only [hXL, min_eq_left h2, max_eq_right h1]
  have hXR_id : ∀ x, s t - δ ≤ x → x ≤ b + δ → XR x = x := fun x h1 h2 => by
    simp only [hXR, min_eq_left h2, max_eq_right h1]
  have hmemL : ∀ τ x, (T τ, XL x) ∈ UL := by
    intro τ x
    have h1 : a - δ ≤ XL x := le_max_left _ _
    have h2 : XL x ≤ s t + δ := max_le (by linarith) (min_le_right _ _)
    exact hboxL _ _ (le_trans (hTb τ) hδL') (by linarith) (by linarith)
  have hmemR : ∀ τ x, (T τ, XR x) ∈ UR := by
    intro τ x
    have h1 : s t - δ ≤ XR x := le_max_left _ _
    have h2 : XR x ≤ b + δ := max_le (by linarith) (min_le_right _ _)
    exact hboxR _ _ (le_trans (hTb τ) hδR') (by linarith) (by linarith)
  obtain ⟨hcuL, hduL, hcvL'⟩ := extension_props hjL hvL hcvL hk hT hXLc hmemL
  obtain ⟨hcuR, hduR, hcvR'⟩ := extension_props hjR hvR hcvR hk hT hXRc hmemR
  have hMJ : HasDerivAt
      (fun τ : ℝ => (∫ x in a..s τ, uL (T τ) (XL x)) + (∫ x in s τ..b, uR (T τ) (XR x)))
      ((∫ x in a..s t, k t * vL (T t) (XL x)) + (∫ x in s t..b, k t * vR (T t) (XR x)) +
        c * (uL (T t) (XL (s t)) - uR (T t) (XR (s t)))) t :=
    ControlVolumes.movingJumpTransport (uL := fun τ x => uL (T τ) (XL x))
      (uR := fun τ x => uR (T τ) (XR x))
      (vL := fun τ x => k τ * vL (T τ) (XL x)) (vR := fun τ x => k τ * vR (T τ) (XR x))
      (s' := fun _ => c) t hs hcuL hduL hcvL' hcuR hduR hcvR'
  have ht0 : |t - t| ≤ δ / 2 := by
    rw [sub_self, abs_zero]
    exact (half_pos hδ).le
  have hkt : k t = 1 := (hTid t ht0).2
  have hTt : T t = t := (hTid t ht0).1
  have hD : (∫ x in a..s t, k t * vL (T t) (XL x)) + (∫ x in s t..b, k t * vR (T t) (XR x)) +
        c * (uL (T t) (XL (s t)) - uR (T t) (XR (s t))) =
      (∫ x in a..s t, vL t x) + (∫ x in s t..b, vR t x) + c * (uL t (s t) - uR t (s t)) := by
    have e1 : (∫ x in a..s t, k t * vL (T t) (XL x)) = ∫ x in a..s t, vL t x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le has.le] at hx
      show k t * vL (T t) (XL x) = vL t x
      rw [hkt, hTt, one_mul, hXL_id x (by linarith [hx.1]) (by linarith [hx.2])]
    have e2 : (∫ x in s t..b, k t * vR (T t) (XR x)) = ∫ x in s t..b, vR t x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le hsb.le] at hx
      show k t * vR (T t) (XR x) = vR t x
      rw [hkt, hTt, one_mul, hXR_id x (by linarith [hx.1]) (by linarith [hx.2])]
    rw [e1, e2, hTt, hXL_id (s t) (by linarith) (by linarith),
      hXR_id (s t) (by linarith) (by linarith)]
  have hev : (fun τ : ℝ => (∫ x in a..s τ, uL τ x) + (∫ x in s τ..b, uR τ x)) =ᶠ[nhds t]
      (fun τ : ℝ => (∫ x in a..s τ, uL (T τ) (XL x)) + (∫ x in s τ..b, uR (T τ) (XR x))) := by
    have h1 : ∀ᶠ τ in nhds t, |τ - t| ≤ δ / 2 := by
      filter_upwards [Metric.closedBall_mem_nhds t (half_pos hδ)] with τ hτ
      rwa [Metric.mem_closedBall, Real.dist_eq] at hτ
    have h2 : ∀ᶠ τ in nhds t, |s τ - s t| ≤ δ := by
      filter_upwards [hs.continuousAt.preimage_mem_nhds
        (Metric.closedBall_mem_nhds (s t) hδ)] with τ hτ
      rwa [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] at hτ
    filter_upwards [h1, h2] with τ hτ1 hτ2
    have hTτ : T τ = τ := (hTid τ hτ1).1
    obtain ⟨hs1, hs2⟩ := abs_le.mp hτ2
    have eL : (∫ x in a..s τ, uL τ x) = ∫ x in a..s τ, uL (T τ) (XL x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      show uL τ x = uL (T τ) (XL x)
      rw [hTτ]
      rcases Set.mem_uIcc.mp hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · rw [hXL_id x (by linarith) (by linarith)]
      · rw [hXL_id x (by linarith) (by linarith)]
    have eR : (∫ x in s τ..b, uR τ x) = ∫ x in s τ..b, uR (T τ) (XR x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      show uR τ x = uR (T τ) (XR x)
      rw [hTτ]
      rcases Set.mem_uIcc.mp hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · rw [hXR_id x (by linarith) (by linarith)]
      · rw [hXR_id x (by linarith) (by linarith)]
    change (∫ x in a..s τ, uL τ x) + (∫ x in s τ..b, uR τ x) =
      (∫ x in a..s τ, uL (T τ) (XL x)) + (∫ x in s τ..b, uR (T τ) (XR x))
    rw [eL, eR]
  have hFL : (∫ x in a..s t, vL t x) = f (uL t a) - f (uL t (s t)) := by
    have hmaps : Set.MapsTo (fun x : ℝ => (t, x)) (Set.Icc a (s t)) UL :=
      fun x hx => hKL ⟨Set.mem_singleton t, hx⟩
    have hcont : ContinuousOn (fun x : ℝ => vL t x) (Set.Icc a (s t)) :=
      hcvL.comp (continuousOn_const.prodMk continuousOn_id) hmaps
    have hderiv : ∀ x ∈ Set.Ioo a (s t),
        HasDerivAt (fun y : ℝ => -f (uL t y)) (vL t x) x := by
      intro x hx
      have h := (hgL x hx).neg
      have hp := hPDEL x hx
      convert h using 1
      linarith
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le has.le hfL.neg hderiv
      (hcont.intervalIntegrable_of_Icc has.le)
    simp only [Pi.neg_apply] at h
    linarith [h]
  have hFR : (∫ x in s t..b, vR t x) = f (uR t (s t)) - f (uR t b) := by
    have hmaps : Set.MapsTo (fun x : ℝ => (t, x)) (Set.Icc (s t) b) UR :=
      fun x hx => hKR ⟨Set.mem_singleton t, hx⟩
    have hcont : ContinuousOn (fun x : ℝ => vR t x) (Set.Icc (s t) b) :=
      hcvR.comp (continuousOn_const.prodMk continuousOn_id) hmaps
    have hderiv : ∀ x ∈ Set.Ioo (s t) b,
        HasDerivAt (fun y : ℝ => -f (uR t y)) (vR t x) x := by
      intro x hx
      have h := (hgR x hx).neg
      have hp := hPDER x hx
      convert h using 1
      linarith
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsb.le hfR.neg hderiv
      (hcont.intervalIntegrable_of_Icc hsb.le)
    simp only [Pi.neg_apply] at h
    linarith [h]
  have hMD : HasDerivAt (fun τ : ℝ => (∫ x in a..s τ, uL τ x) + (∫ x in s τ..b, uR τ x))
      (f (uL t a) - f (uL t (s t)) + (f (uR t (s t)) - f (uR t b)) +
        c * (uL t (s t) - uR t (s t))) t := by
    have h := hMJ.congr_of_eventuallyEq hev
    rw [hD, hFL, hFR] at h
    exact h
  constructor
  · intro h
    have heq := h.unique hMD
    linear_combination heq
  · intro h
    exact hMD.congr_deriv (by linear_combination -h)

end ScalarShock
