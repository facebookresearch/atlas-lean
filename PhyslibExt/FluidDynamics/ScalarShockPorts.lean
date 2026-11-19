/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
import PhyslibExt.ContinuumMechanics.ControlVolumes
import Mathlib.Analysis.Calculus.Deriv.Mul

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

Part B evaluates the weak residual of the straight moving step, the field with the constant state
`uL` left of the line `x = c * t` and the constant state `uR` right of it. For a flux `f`, its weak
residual against a smooth test function `φ` vanishing outside a bounded rectangle is the plane
integral `∫∫ (u * φ_t + f u * φ_x)`, a plain Bochner integral; it equals
`-([f] - c * [u]) * ∫ φ (t, c * t) dt`. The proof splits each time slice at the interface, uses
the moving interface transport theorem `ControlVolumes.movingJumpTransport` for the
time-derivative terms and the fundamental theorem of calculus for the flux terms, and uses Fubini
to pass between the plane integral and iterated integrals. No divergence theorem across the
nonsmooth interface and no distribution space is used, and only a straight single shock is
treated.

## ii. Key results

- `ScalarShock.conservation_iff_rankineHugoniot`: conservation on a fixed interval crossing the
  interface is equivalent to the Rankine-Hugoniot jump identity `c * (uR - uL) = f uR - f uL`.
- `ScalarShock.movingStep` and `ScalarShock.weakResidual`: the straight moving step and the weak
  residual of a field against a test function.
- `ScalarShock.integrable_weakResidual_movingStep`: both integrals in the residual formula are
  genuine integrals.
- `ScalarShock.weakResidual_movingStep`: the residual of the moving step is
  `-((f uR - f uL) - c * (uR - uL)) * ∫ φ (t, c * t) dt`.
- `ScalarShock.weakResidual_movingStep_eq_zero_of_trace_eq_zero`: a test vanishing along the
  interface cannot detect the jump.
- `ScalarShock.burgers_step_two_zero_weakResidual`: for Burgers states `2 | 0` the residual
  vanishes at speed `1` and is `2 * ∫ φ (t, 0) dt` at the incorrect speed `0`.

## iii. Table of contents

- A. Rankine-Hugoniot from two classical sides
- B. Weak residual of a straight moving step

## iv. References

- L. C. Evans, *Partial Differential Equations*, 2nd ed., American Mathematical Society, 2010,
  §3.4.1 (shocks: the Rankine-Hugoniot condition for a curve of discontinuity separating smooth
  solutions of a scalar conservation law).
- R. J. LeVeque, *Finite Volume Methods for Hyperbolic Problems*, Cambridge University Press,
  2002, §11.8 (shock speed from the integral form of a scalar conservation law).
- `ControlVolumes.movingJumpTransport` (`PhyslibExt.ContinuumMechanics.ControlVolumes`).
- Mathlib's `MeasureTheory.integral_prod` (Fubini) and
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` (fundamental theorem of calculus).
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
This is the classical Rankine-Hugoniot condition for scalar conservation laws
(Evans, *Partial Differential Equations*, §3.4.1; LeVeque, *Finite Volume Methods
for Hyperbolic Problems*, §11.8). No existence of such solutions is asserted. -/
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


/-! ## B. Weak residual of a straight moving step -/

open scoped ContDiff

/-- Straight moving step, time first: the state `uL` where `x < c * t` and the
state `uR` where `c * t ≤ x`. The value on the line `x = c * t`, a null set of
the plane, does not affect any integral below. -/
noncomputable def movingStep (uL uR c : ℝ) (t x : ℝ) : ℝ :=
  if x < c * t then uL else uR

/-- Weak residual `∫∫ (u * φ_t + f u * φ_x)` over the whole `(t, x)` plane
(Lebesgue measure on `ℝ × ℝ`, time first) of a field `u` against a test function
whose time and space partial derivatives are `φt` and `φx`. This is a plain
Bochner integral; no distribution space is introduced. -/
noncomputable def weakResidual (f : ℝ → ℝ) (u φt φx : ℝ → ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, (u p.1 p.2 * φt p.1 p.2 + f (u p.1 p.2) * φx p.1 p.2)

/-! ### Auxiliary lemmas -/

private lemma phi_eq_zero_of_not_mem {T0 T1 X0 X1 : ℝ} {φ : ℝ → ℝ → ℝ}
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1)
    {t x : ℝ} (h : (t, x) ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) : φ t x = 0 := by
  by_contra hne
  exact h (hsupp hne)

private lemma partials_facts {T0 T1 X0 X1 : ℝ} {φ φt φx : ℝ → ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) :
    (Continuous fun p : ℝ × ℝ => φt p.1 p.2) ∧ (Continuous fun p : ℝ × ℝ => φx p.1 p.2) ∧
      ∀ t x : ℝ, (t, x) ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 → φt t x = 0 ∧ φx t x = 0 := by
  set Φ : ℝ × ℝ → ℝ := fun p => φ p.1 p.2
  have hdiff : Differentiable ℝ Φ := hφ.differentiable (by simp)
  have hcontD : Continuous (fderiv ℝ Φ) := hφ.continuous_fderiv (by simp)
  have hφt_eq : ∀ t x, φt t x = fderiv ℝ Φ (t, x) (1, 0) := by
    intro t x
    have hl : HasDerivAt (fun τ : ℝ => (τ, x)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have h1 : HasDerivAt (Φ ∘ fun τ : ℝ => (τ, x)) (fderiv ℝ Φ (t, x) (1, 0)) t :=
      (hdiff (t, x)).hasFDerivAt.comp_hasDerivAt t hl
    exact (hφt t x).unique h1
  have hφx_eq : ∀ t x, φx t x = fderiv ℝ Φ (t, x) (0, 1) := by
    intro t x
    have hl : HasDerivAt (fun y : ℝ => (t, y)) ((0 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
    have h1 : HasDerivAt (Φ ∘ fun y : ℝ => (t, y)) (fderiv ℝ Φ (t, x) (0, 1)) x :=
      (hdiff (t, x)).hasFDerivAt.comp_hasDerivAt x hl
    exact (hφx t x).unique h1
  have hzero : ∀ p ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1, fderiv ℝ Φ p = 0 := by
    intro p hp
    have hK : IsClosed (Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) := isClosed_Icc.prod isClosed_Icc
    have hev : Φ =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hp] with q hq
      by_contra hne
      exact hq (hsupp hne)
    rw [hev.fderiv_eq]
    simp
  refine ⟨?_, ?_, fun t x h => ⟨?_, ?_⟩⟩
  · simp only [hφt_eq]
    exact hcontD.clm_apply continuous_const
  · simp only [hφx_eq]
    exact hcontD.clm_apply continuous_const
  · rw [hφt_eq, hzero _ h]
    rfl
  · rw [hφx_eq, hzero _ h]
    rfl

private lemma movingStep_of_lt {uL uR c t x : ℝ} (h : x < c * t) :
    movingStep uL uR c t x = uL := by
  simp [movingStep, h]

private lemma movingStep_of_not_lt {uL uR c t x : ℝ} (h : ¬x < c * t) :
    movingStep uL uR c t x = uR := by
  simp [movingStep, h]

private lemma measurable_comp_movingStep (uL uR c : ℝ) (g : ℝ → ℝ) :
    Measurable fun p : ℝ × ℝ => g (movingStep uL uR c p.1 p.2) := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 < c * p.1} :=
    measurableSet_lt measurable_snd (measurable_const.mul measurable_fst)
  have heq : (fun p : ℝ × ℝ => g (movingStep uL uR c p.1 p.2)) =
      fun p => if p.2 < c * p.1 then g uL else g uR := by
    funext p
    unfold movingStep
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite hset measurable_const measurable_const

private lemma norm_comp_movingStep_le (uL uR c : ℝ) (g : ℝ → ℝ) (t x : ℝ) :
    ‖g (movingStep uL uR c t x)‖ ≤ max |g uL| |g uR| := by
  unfold movingStep
  split_ifs
  · rw [Real.norm_eq_abs]
    exact le_max_left _ _
  · rw [Real.norm_eq_abs]
    exact le_max_right _ _

private lemma integrable_comp_movingStep_mul (uL uR c : ℝ) (g : ℝ → ℝ)
    {ψ : ℝ × ℝ → ℝ} (hψ : MeasureTheory.Integrable ψ) :
    MeasureTheory.Integrable fun p : ℝ × ℝ => g (movingStep uL uR c p.1 p.2) * ψ p :=
  hψ.bdd_mul (measurable_comp_movingStep uL uR c g).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun p => norm_comp_movingStep_le uL uR c g p.1 p.2)

private lemma integrable_slice_comp_movingStep_mul (uL uR c t : ℝ) (g : ℝ → ℝ)
    {ψ : ℝ → ℝ} (hψ : MeasureTheory.Integrable ψ) :
    MeasureTheory.Integrable fun x : ℝ => g (movingStep uL uR c t x) * ψ x :=
  hψ.bdd_mul ((measurable_comp_movingStep uL uR c g).comp
      measurable_prodMk_left).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun x => norm_comp_movingStep_le uL uR c g t x)

private lemma integrable_of_continuous_of_zero {g : ℝ → ℝ} {A B : ℝ}
    (hg : Continuous g) (h0 : ∀ x, x ∉ Set.Icc A B → g x = 0) :
    MeasureTheory.Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.intro isCompact_Icc h0)

private lemma integrable_plane_of_continuous_of_zero {g : ℝ × ℝ → ℝ}
    {T0 T1 X0 X1 : ℝ} (hg : Continuous g)
    (h0 : ∀ p, p ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 → g p = 0) :
    MeasureTheory.Integrable g :=
  hg.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) h0)

private lemma integral_eq_intervalIntegral_of_zero {g : ℝ → ℝ} {A B X0 X1 : ℝ}
    (hAB : A ≤ B) (hA : A < X0) (hB : X1 < B)
    (hg0 : ∀ x, x ∉ Set.Icc X0 X1 → g x = 0) :
    ∫ x, g x = ∫ x in A..B, g x := by
  rw [intervalIntegral.integral_of_le hAB]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    fun x hx => hg0 x ?_).symm
  intro hx'
  exact hx ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

private lemma mem_uIoo_cases {a b x : ℝ} (hx : x ∈ Set.uIoo a b) :
    (a < x ∧ x < b) ∨ (b < x ∧ x < a) := by
  rcases le_total a b with h | h
  · rw [Set.uIoo_of_le h] at hx
    exact Or.inl hx
  · rw [Set.uIoo_of_ge h] at hx
    exact Or.inr hx

/-- One slice of the flux term: FTC on each side of the interface point `s`. -/
private lemma slice_integral_step_deriv {ψ ψ' g : ℝ → ℝ} {α β s X0 X1 : ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ0 : ∀ x, x ∉ Set.Icc X0 X1 → ψ x = 0)
    (hg : MeasureTheory.Integrable g) (hg0 : ∀ x, x ∉ Set.Icc X0 X1 → g x = 0)
    (hgl : ∀ x, x < s → g x = α * ψ' x) (hgr : ∀ x, s < x → g x = β * ψ' x) :
    ∫ x, g x = (α - β) * ψ s := by
  have hAs : min X0 s - 1 ≤ s := by linarith [min_le_right X0 s]
  have hsB : s ≤ max X1 s + 1 := by linarith [le_max_right X1 s]
  have hAX : min X0 s - 1 < X0 := by linarith [min_le_left X0 s]
  have hXB : X1 < max X1 s + 1 := by linarith [le_max_left X1 s]
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hψ x).continuousAt
  have hl : ∫ x in (min X0 s - 1)..s, g x = α * ψ s - α * ψ (min X0 s - 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun x => α * ψ x) hAs
      (continuous_const.mul hψc).continuousOn
      (fun x hx => by
        rw [hgl x hx.2]
        exact (hψ x).const_mul α)
      hg.intervalIntegrable
  have hr : ∫ x in s..(max X1 s + 1), g x = β * ψ (max X1 s + 1) - β * ψ s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun x => β * ψ x) hsB
      (continuous_const.mul hψc).continuousOn
      (fun x hx => by
        rw [hgr x hx.1]
        exact (hψ x).const_mul β)
      hg.intervalIntegrable
  have hψA : ψ (min X0 s - 1) = 0 := hψ0 _ fun h => by linarith [h.1]
  have hψB : ψ (max X1 s + 1) = 0 := hψ0 _ fun h => by linarith [h.2]
  rw [integral_eq_intervalIntegral_of_zero (hAs.trans hsB) hAX hXB hg0,
    ← intervalIntegral.integral_add_adjacent_intervals (b := s) hg.intervalIntegrable
      hg.intervalIntegrable, hl, hr, hψA, hψB]
  ring

/-- One slice of the time term: split at the interface point `s`. -/
private lemma slice_integral_step_split {h g : ℝ → ℝ} {α β s a b X0 X1 : ℝ}
    (hab : a ≤ b) (ha : a < X0) (hb : X1 < b)
    (hg : MeasureTheory.Integrable g) (hg0 : ∀ x, x ∉ Set.Icc X0 X1 → g x = 0)
    (hh0 : ∀ x, x ∉ Set.Icc X0 X1 → h x = 0)
    (hgl : ∀ x, x < s → g x = α * h x) (hgr : ∀ x, s < x → g x = β * h x) :
    (∫ x in a..s, α * h x) + (∫ x in s..b, β * h x) = ∫ x, g x := by
  rw [integral_eq_intervalIntegral_of_zero hab ha hb hg0,
    ← intervalIntegral.integral_add_adjacent_intervals (b := s) hg.intervalIntegrable
      hg.intervalIntegrable]
  congr 1
  · apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rcases mem_uIoo_cases hx with ⟨_, hxs⟩ | ⟨_, hxa⟩
    · exact (hgl x hxs).symm
    · have hx0 : x ∉ Set.Icc X0 X1 := fun hm => by linarith [hm.1]
      simp only [hh0 x hx0, hg0 x hx0, mul_zero]
  · apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rcases mem_uIoo_cases hx with ⟨hsx, _⟩ | ⟨hbx, _⟩
    · exact (hgr x hsx).symm
    · have hx0 : x ∉ Set.Icc X0 X1 := fun hm => by linarith [hm.2]
      simp only [hh0 x hx0, hg0 x hx0, mul_zero]

/-- Time term: moving-interval transport plus FTC in time, then Fubini. -/
private lemma time_part {uL uR c T0 T1 X0 X1 : ℝ} {φ φt : ℝ → ℝ → ℝ}
    (hφc : Continuous fun p : ℝ × ℝ => φ p.1 p.2)
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hct : Continuous fun p : ℝ × ℝ => φt p.1 p.2)
    (hφ0 : ∀ t x : ℝ, (t, x) ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 → φ t x = 0)
    (hφt0 : ∀ t x : ℝ, (t, x) ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 → φt t x = 0)
    (hU : MeasureTheory.Integrable fun p : ℝ × ℝ =>
      movingStep uL uR c p.1 p.2 * φt p.1 p.2) :
    ∫ p : ℝ × ℝ, movingStep uL uR c p.1 p.2 * φt p.1 p.2 =
      c * (uR - uL) * ∫ t : ℝ, φ t (c * t) := by
  obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b : ℝ, a ≤ b ∧ a < X0 ∧ X1 < b :=
    ⟨min X0 X1 - 1, max X0 X1 + 1, by linarith [min_le_left X0 X1, le_max_left X0 X1],
      by linarith [min_le_left X0 X1], by linarith [le_max_right X0 X1]⟩
  obtain ⟨A, B, hAB, hA, hB⟩ : ∃ A B : ℝ, A ≤ B ∧ A < T0 ∧ T1 < B :=
    ⟨min T0 T1 - 1, max T0 T1 + 1, by linarith [min_le_left T0 T1, le_max_left T0 T1],
      by linarith [min_le_left T0 T1], by linarith [le_max_right T0 T1]⟩
  have hsplit : ∀ τ : ℝ, (∫ x in a..c * τ, uL * φt τ x) + (∫ x in c * τ..b, uR * φt τ x) =
      ∫ x, movingStep uL uR c τ x * φt τ x := by
    intro τ
    have hcτ : Continuous fun x : ℝ => φt τ x :=
      hct.comp (continuous_const.prodMk continuous_id)
    have hint : MeasureTheory.Integrable fun x : ℝ => φt τ x :=
      integrable_of_continuous_of_zero (A := X0) (B := X1) hcτ
        fun x hx => hφt0 τ x fun h => hx h.2
    exact slice_integral_step_split (h := fun x => φt τ x) (α := uL) (β := uR) (s := c * τ)
      hab ha hb (integrable_slice_comp_movingStep_mul uL uR c τ (fun u => u) hint)
      (fun x hx => by rw [hφt0 τ x fun h => hx h.2, mul_zero])
      (fun x hx => hφt0 τ x fun h => hx h.2)
      (fun x hx => by rw [movingStep_of_lt hx])
      (fun x hx => by rw [movingStep_of_not_lt (not_lt.2 hx.le)])
  have hs : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => c * τ) ((fun _ : ℝ => c) τ) τ := fun τ => by
    simpa using (hasDerivAt_id τ).const_mul c
  have hMd : ∀ τ : ℝ, HasDerivAt
      (fun τ : ℝ => (∫ x in a..c * τ, uL * φ τ x) + (∫ x in c * τ..b, uR * φ τ x))
      ((∫ x in a..c * τ, uL * φt τ x) + (∫ x in c * τ..b, uR * φt τ x) +
        c * (uL * φ τ (c * τ) - uR * φ τ (c * τ))) τ := fun τ =>
    ControlVolumes.movingJumpTransport (uL := fun τ x => uL * φ τ x)
      (uR := fun τ x => uR * φ τ x)
      (vL := fun τ x => uL * φt τ x) (vR := fun τ x => uR * φt τ x)
      (s := fun τ => c * τ) (s' := fun _ => c) (a := a) (b := b) τ (hs τ)
      (continuous_const.mul hφc) (fun t x => (hφt t x).const_mul uL)
      (continuous_const.mul hct)
      (continuous_const.mul hφc) (fun t x => (hφt t x).const_mul uR)
      (continuous_const.mul hct)
  have hMd' : ∀ τ : ℝ, HasDerivAt
      (fun τ : ℝ => (∫ x in a..c * τ, uL * φ τ x) + (∫ x in c * τ..b, uR * φ τ x))
      ((∫ x, movingStep uL uR c τ x * φt τ x) +
        c * (uL * φ τ (c * τ) - uR * φ τ (c * τ))) τ := by
    intro τ
    have h := hMd τ
    rw [hsplit τ] at h
    exact h
  have hD1 : MeasureTheory.Integrable fun τ : ℝ => ∫ x, movingStep uL uR c τ x * φt τ x :=
    hU.integral_prod_left
  have hD2 : MeasureTheory.Integrable fun τ : ℝ =>
      c * (uL * φ τ (c * τ) - uR * φ τ (c * τ)) := by
    have htc : Continuous fun τ : ℝ => φ τ (c * τ) :=
      hφc.comp (continuous_id.prodMk (continuous_const.mul continuous_id))
    refine integrable_of_continuous_of_zero (A := T0) (B := T1)
      (continuous_const.mul ((continuous_const.mul htc).sub (continuous_const.mul htc)))
      fun τ hτ => ?_
    rw [hφ0 τ (c * τ) fun h => hτ h.1]
    ring
  have hftc : ∫ τ in A..B, ((∫ x, movingStep uL uR c τ x * φt τ x) +
      c * (uL * φ τ (c * τ) - uR * φ τ (c * τ))) =
      ((∫ x in a..c * B, uL * φ B x) + (∫ x in c * B..b, uR * φ B x)) -
      ((∫ x in a..c * A, uL * φ A x) + (∫ x in c * A..b, uR * φ A x)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hMd' τ)
      (hD1.add hD2).intervalIntegrable
  have hMB : (∫ x in a..c * B, uL * φ B x) + (∫ x in c * B..b, uR * φ B x) = 0 := by
    have h0 : ∀ x, φ B x = 0 := fun x => hφ0 B x fun h => by linarith [h.1.2]
    simp [h0]
  have hMA : (∫ x in a..c * A, uL * φ A x) + (∫ x in c * A..b, uR * φ A x) = 0 := by
    have h0 : ∀ x, φ A x = 0 := fun x => hφ0 A x fun h => by linarith [h.1.1]
    simp [h0]
  have hfull : ∫ τ in A..B, ((∫ x, movingStep uL uR c τ x * φt τ x) +
      c * (uL * φ τ (c * τ) - uR * φ τ (c * τ))) =
      ∫ τ, ((∫ x, movingStep uL uR c τ x * φt τ x) +
        c * (uL * φ τ (c * τ) - uR * φ τ (c * τ))) := by
    refine (integral_eq_intervalIntegral_of_zero hAB hA hB fun τ hτ => ?_).symm
    have h1 : ∀ x, movingStep uL uR c τ x * φt τ x = 0 := fun x => by
      rw [hφt0 τ x fun h => hτ h.1, mul_zero]
    rw [hφ0 τ (c * τ) fun h => hτ h.1]
    simp [h1]
  rw [hMB, hMA, sub_zero, hfull, MeasureTheory.integral_add hD1 hD2] at hftc
  have hfub : ∫ p : ℝ × ℝ, movingStep uL uR c p.1 p.2 * φt p.1 p.2 =
      ∫ τ : ℝ, ∫ x : ℝ, movingStep uL uR c τ x * φt τ x :=
    MeasureTheory.integral_prod _ hU
  have htrace : ∫ τ : ℝ, c * (uL * φ τ (c * τ) - uR * φ τ (c * τ)) =
      c * (uL - uR) * ∫ τ : ℝ, φ τ (c * τ) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext τ
    ring
  rw [hfub]
  linear_combination hftc - htrace

/-- Flux term: Fubini, then FTC in space on each side of the interface. -/
private lemma flux_part {f : ℝ → ℝ} {uL uR c T0 T1 X0 X1 : ℝ} {φ φx : ℝ → ℝ → ℝ}
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hcx : Continuous fun p : ℝ × ℝ => φx p.1 p.2)
    (hφ0 : ∀ t x : ℝ, (t, x) ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 → φ t x = 0)
    (hφx0 : ∀ t x : ℝ, (t, x) ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 → φx t x = 0)
    (hF : MeasureTheory.Integrable fun p : ℝ × ℝ =>
      f (movingStep uL uR c p.1 p.2) * φx p.1 p.2) :
    ∫ p : ℝ × ℝ, f (movingStep uL uR c p.1 p.2) * φx p.1 p.2 =
      (f uL - f uR) * ∫ t : ℝ, φ t (c * t) := by
  have hslice : ∀ t : ℝ, ∫ x, f (movingStep uL uR c t x) * φx t x =
      (f uL - f uR) * φ t (c * t) := by
    intro t
    have hcxt : Continuous fun x : ℝ => φx t x :=
      hcx.comp (continuous_const.prodMk continuous_id)
    have hxint : MeasureTheory.Integrable fun x : ℝ => φx t x :=
      integrable_of_continuous_of_zero (A := X0) (B := X1) hcxt
        fun x hx => hφx0 t x fun h => hx h.2
    exact slice_integral_step_deriv (ψ := fun y => φ t y) (ψ' := fun y => φx t y)
      (α := f uL) (β := f uR) (s := c * t) (X0 := X0) (X1 := X1) (hφx t)
      (fun x hx => hφ0 t x fun h => hx h.2)
      (integrable_slice_comp_movingStep_mul uL uR c t f hxint)
      (fun x hx => by rw [hφx0 t x fun h => hx h.2, mul_zero])
      (fun x hx => by rw [movingStep_of_lt hx])
      (fun x hx => by rw [movingStep_of_not_lt (not_lt.2 hx.le)])
  have hfub : ∫ p : ℝ × ℝ, f (movingStep uL uR c p.1 p.2) * φx p.1 p.2 =
      ∫ t : ℝ, ∫ x : ℝ, f (movingStep uL uR c t x) * φx t x :=
    MeasureTheory.integral_prod _ hF
  rw [hfub, ← MeasureTheory.integral_const_mul]
  congr 1
  funext t
  exact hslice t

/-! ### Integrability and the residual formula -/

/-- Explicit integrability. For a smooth test `φ` vanishing outside the bounded
rectangle `[T0, T1] × [X0, X1]`, with time and space partial derivatives `φt`
and `φx`, the residual integrand of the moving step and the trace
`t ↦ φ t (c * t)` along the interface are both integrable, so the two integrals
in `weakResidual_movingStep` are genuine. -/
lemma integrable_weakResidual_movingStep {f : ℝ → ℝ} {uL uR c T0 T1 X0 X1 : ℝ}
    {φ φt φx : ℝ → ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        movingStep uL uR c p.1 p.2 * φt p.1 p.2 +
          f (movingStep uL uR c p.1 p.2) * φx p.1 p.2) ∧
      MeasureTheory.Integrable (fun t : ℝ => φ t (c * t)) := by
  obtain ⟨hct, hcx, hpz⟩ := partials_facts hφ hφt hφx hsupp
  refine ⟨?_, ?_⟩
  · exact (integrable_comp_movingStep_mul uL uR c (fun u => u)
      (integrable_plane_of_continuous_of_zero hct fun p hp => (hpz p.1 p.2 hp).1)).add
      (integrable_comp_movingStep_mul uL uR c f
        (integrable_plane_of_continuous_of_zero hcx fun p hp => (hpz p.1 p.2 hp).2))
  · have htc : Continuous fun t : ℝ => φ t (c * t) :=
      hφ.continuous.comp (continuous_id.prodMk (continuous_const.mul continuous_id))
    exact integrable_of_continuous_of_zero (A := T0) (B := T1) htc
      fun t ht => phi_eq_zero_of_not_mem hsupp fun h => ht h.1

/-- Weak residual of a straight moving step. For constant states `uL`, `uR`,
interface `x = c * t`, any flux `f`, and a smooth test `φ` vanishing outside a
bounded rectangle, with partial derivatives `φt`, `φx`:
`∫∫ (u * φ_t + f u * φ_x) = -((f uR - f uL) - c * (uR - uL)) * ∫ φ (t, c * t) dt`.
The time-derivative terms use the moving-interval transport theorem
`ControlVolumes.movingJumpTransport`. -/
theorem weakResidual_movingStep {f : ℝ → ℝ} {uL uR c T0 T1 X0 X1 : ℝ}
    {φ φt φx : ℝ → ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) :
    weakResidual f (movingStep uL uR c) φt φx =
      -((f uR - f uL) - c * (uR - uL)) * ∫ t : ℝ, φ t (c * t) := by
  obtain ⟨hct, hcx, hpz⟩ := partials_facts hφ hφt hφx hsupp
  have hφ0 : ∀ t x : ℝ, (t, x) ∉ Set.Icc T0 T1 ×ˢ Set.Icc X0 X1 → φ t x = 0 :=
    fun _ _ h => phi_eq_zero_of_not_mem hsupp h
  have hU : MeasureTheory.Integrable fun p : ℝ × ℝ =>
      movingStep uL uR c p.1 p.2 * φt p.1 p.2 :=
    integrable_comp_movingStep_mul uL uR c (fun u => u)
      (integrable_plane_of_continuous_of_zero hct fun p hp => (hpz p.1 p.2 hp).1)
  have hF : MeasureTheory.Integrable fun p : ℝ × ℝ =>
      f (movingStep uL uR c p.1 p.2) * φx p.1 p.2 :=
    integrable_comp_movingStep_mul uL uR c f
      (integrable_plane_of_continuous_of_zero hcx fun p hp => (hpz p.1 p.2 hp).2)
  have hsplit : weakResidual f (movingStep uL uR c) φt φx =
      (∫ p : ℝ × ℝ, movingStep uL uR c p.1 p.2 * φt p.1 p.2) +
        ∫ p : ℝ × ℝ, f (movingStep uL uR c p.1 p.2) * φx p.1 p.2 :=
    MeasureTheory.integral_add hU hF
  rw [hsplit, time_part hφ.continuous hφt hct hφ0 (fun t x h => (hpz t x h).1) hU,
    flux_part hφx hcx hφ0 (fun t x h => (hpz t x h).2) hF]
  ring

/-! ### Fixtures -/

/-- A test that vanishes along the interface, in particular one supported away
from it, gives zero residual for every flux and every pair of states: such a
test alone cannot detect the jump. -/
lemma weakResidual_movingStep_eq_zero_of_trace_eq_zero {f : ℝ → ℝ}
    {uL uR c T0 T1 X0 X1 : ℝ} {φ φt φx : ℝ → ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1)
    (htrace : ∀ t : ℝ, φ t (c * t) = 0) :
    weakResidual f (movingStep uL uR c) φt φx = 0 := by
  rw [weakResidual_movingStep hφ hφt hφx hsupp]
  simp [htrace]

/-- Fixture: Burgers flux `u ^ 2 / 2` with the nonzero jump from `2` to `0`. At
the Rankine-Hugoniot speed `1` the residual vanishes for every admissible test;
at the incorrect stationary speed `0` it equals `2 * ∫ φ (t, 0) dt`, which is
nonzero exactly when the test has nonzero integral along the front. -/
lemma burgers_step_two_zero_weakResidual {T0 T1 X0 X1 : ℝ}
    {φ φt φx : ℝ → ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2))
    (hφt : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => φ τ x) (φt t x) t)
    (hφx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => φ t y) (φx t x) x)
    (hsupp : Function.support (fun p : ℝ × ℝ => φ p.1 p.2) ⊆
      Set.Icc T0 T1 ×ˢ Set.Icc X0 X1) :
    weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 1) φt φx = 0 ∧
      weakResidual (fun u : ℝ => u ^ 2 / 2) (movingStep 2 0 0) φt φx =
        2 * ∫ t : ℝ, φ t 0 := by
  constructor
  · rw [weakResidual_movingStep hφ hφt hφx hsupp]
    norm_num
  · rw [weakResidual_movingStep hφ hφt hφx hsupp]
    norm_num

end ScalarShock
