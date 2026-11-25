/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.SpeedMeasure
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

open MeasureTheory Set intervalIntegral
open scoped Topology

/-!
# Feller boundary classification for one-dimensional diffusions

This module records Feller's analytic integral test classifying the endpoints
`0` and `1` of a one-dimensional diffusion on `(0, 1)` with drift `b` and
diffusion coefficient `a`, following Karlin and Taylor (1981), Chapter 15.
Fixing an interior basepoint `c`, write `ψ` for the scale density
`scaleDensityFrom b a c` and `m` for the speed density
`speedDensityFrom b a c`. At the left endpoint the Feller functionals are
`Σ₀ = ∫₀^c (∫ₓ^c m(y) dy) ψ(x) dx` and
`N₀ = ∫₀^c (∫ₓ^c ψ(y) dy) m(x) dx`, with mirrored functionals `Σ₁, N₁` at the
right endpoint integrating over `(c, 1)` with inner integrals from `c` to `x`.
An endpoint is regular if both functionals are finite, exit if `Σ < ∞` and
`N = ∞`, entrance if `Σ = ∞` and `N < ∞`, and natural if both are infinite.
Finiteness is stated with `MeasureTheory.IntegrableOn` against `volume`.

Each of the eight predicates includes the standing hypotheses
`IsFellerAdmissible b a c`: the basepoint `c` is interior, `a` is positive and
continuous on `(0, 1)`, and `b / a` is continuous there. Without them the
finiteness pattern is not a classification: for `c = 0` the set `Ioo 0 c` is
empty, and for `a = 0` the speed density vanishes by division by zero, so the
integrability conditions hold vacuously. The classification is independent of
the interior basepoint.

This is Feller's analytic integral test only: the predicates record which
Feller functionals are finite. Attainability or non-attainability of the
boundary, boundary conditions for a semigroup, and existence or uniqueness of
extensions are not claimed; the process-level reading requires Feller
boundary theory not developed here.

## Main definitions and results

* `IsFellerAdmissible`: the standing hypotheses of the classification.
* `IsRegularBoundaryAtZero`, `IsExitBoundaryAtZero`, `IsEntranceBoundaryAtZero`,
  `IsNaturalBoundaryAtZero`, and their analogues at `1`: the four Feller
  classes of each endpoint.
* `isRegularBoundaryAtZero_basepoint_iff` and its seven analogues: the
  classification does not depend on the interior basepoint.

## References

* Karlin, S. and Taylor, H. M. (1981). *A Second Course in Stochastic
  Processes*. Academic Press, Chapter 15.
-/

@[expose] public section
namespace MathlibExt.Probability.Diffusion

/-- The standing hypotheses of Feller's boundary classification on `(0, 1)`
for drift `b`, diffusion coefficient `a` and basepoint `c`: the basepoint is
interior, and `a` is positive and continuous on `(0, 1)` with `b / a`
continuous there. Under them the scale and speed densities are positive and
continuous on `(0, 1)`. Nothing is assumed at the endpoints. -/
structure IsFellerAdmissible (b a : ℝ → ℝ) (c : ℝ) : Prop where
  /-- The basepoint is interior. -/
  mem_Ioo : c ∈ Ioo (0 : ℝ) 1
  /-- The diffusion coefficient is positive inside the interval. -/
  pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x
  /-- The diffusion coefficient is continuous inside the interval. -/
  continuousOn : ContinuousOn a (Ioo 0 1)
  /-- The drift-to-diffusion ratio is continuous inside the interval. -/
  continuousOn_div : ContinuousOn (fun x => b x / a x) (Ioo 0 1)

/-- The left endpoint `0` is a **regular** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and both the scale-weighted speed integral
`Σ₀` and the speed-weighted scale integral `N₀` are finite. Finiteness is
`MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo 0 c`, with inner
interval integrals from `x` to the basepoint `c`. The predicate records which
Feller functionals are finite only; it does not claim attainability of the
boundary. -/
noncomputable def IsRegularBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The left endpoint `0` is an **exit** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and the Feller functional `Σ₀` is finite
while `N₀` is infinite. Finiteness is `MeasureTheory.IntegrableOn` against
`volume` on `Set.Ioo 0 c`, with inner interval integrals from `x` to the
basepoint `c`, and infinitude is the negation of finiteness. The predicate
records which Feller functionals are finite only; it does not claim
attainability of the boundary. -/
noncomputable def IsExitBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  ¬ IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The left endpoint `0` is an **entrance** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and the Feller functional `Σ₀` is infinite
while `N₀` is finite. Finiteness is `MeasureTheory.IntegrableOn` against
`volume` on `Set.Ioo 0 c`, with inner interval integrals from `x` to the
basepoint `c`, and infinitude is the negation of finiteness. The predicate
records which Feller functionals are finite only; it does not claim
attainability of the boundary. -/
noncomputable def IsEntranceBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  ¬ IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The left endpoint `0` is a **natural** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and both Feller functionals `Σ₀` and `N₀` are
infinite. Finiteness is `MeasureTheory.IntegrableOn` against `volume` on
`Set.Ioo 0 c`, with inner interval integrals from `x` to the basepoint `c`,
and infinitude is the negation of finiteness. The predicate records which
Feller functionals are finite only; it does not claim attainability of the
boundary. -/
noncomputable def IsNaturalBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  ¬ IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  ¬ IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The right endpoint `1` is a **regular** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and both the scale-weighted speed integral
`Σ₁` and the speed-weighted scale integral `N₁` are finite. Finiteness is
`MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo c 1`, with inner
interval integrals from the basepoint `c` to `x`. The predicate records which
Feller functionals are finite only; it does not claim attainability of the
boundary. -/
noncomputable def IsRegularBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo c 1) volume ∧
  IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo c 1) volume

/-- The right endpoint `1` is an **exit** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and the Feller functional `Σ₁` is finite
while `N₁` is infinite. Finiteness is `MeasureTheory.IntegrableOn` against
`volume` on `Set.Ioo c 1`, with inner interval integrals from the basepoint
`c` to `x`, and infinitude is the negation of finiteness. The predicate
records which Feller functionals are finite only; it does not claim
attainability of the boundary. -/
noncomputable def IsExitBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo c 1) volume ∧
  ¬ IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo c 1) volume

/-- The right endpoint `1` is an **entrance** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and the Feller functional `Σ₁` is infinite
while `N₁` is finite. Finiteness is `MeasureTheory.IntegrableOn` against
`volume` on `Set.Ioo c 1`, with inner interval integrals from the basepoint
`c` to `x`, and infinitude is the negation of finiteness. The predicate
records which Feller functionals are finite only; it does not claim
attainability of the boundary. -/
noncomputable def IsEntranceBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  ¬ IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo c 1) volume ∧
  IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo c 1) volume

/-- The right endpoint `1` is a **natural** boundary in Feller's classification
(Karlin and Taylor (1981), Chapter 15): the standing hypotheses
`IsFellerAdmissible b a c` hold, and both Feller functionals `Σ₁` and `N₁` are
infinite. Finiteness is `MeasureTheory.IntegrableOn` against `volume` on
`Set.Ioo c 1`, with inner interval integrals from the basepoint `c` to `x`,
and infinitude is the negation of finiteness. The predicate records which
Feller functionals are finite only; it does not claim attainability of the
boundary. -/
noncomputable def IsNaturalBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IsFellerAdmissible b a c ∧
  ¬ IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo c 1) volume ∧
  ¬ IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo c 1) volume
-- Comparison: a nonnegative continuous factor is integrable when a positive
-- multiple of it is bounded above by an integrable function.
private theorem integrableOn_of_mul_le
    (Fav v' : ℝ → ℝ) (K : ℝ) (s : Set ℝ)
    (hK : 0 < K)
    (hv'cont : ContinuousOn v' s) (hs : MeasurableSet s)
    (hFav : IntegrableOn Fav s volume)
    (hle : ∀ᵐ x ∂(volume.restrict s), K * v' x ≤ Fav x)
    (hnn : ∀ᵐ x ∂(volume.restrict s), 0 ≤ v' x) :
    IntegrableOn v' s volume := by
  have hKmeas : AEStronglyMeasurable (fun x => K * v' x) (volume.restrict s) :=
    (continuousOn_const.mul hv'cont).aestronglyMeasurable hs
  have hKint : IntegrableOn (fun x => K * v' x) s volume := by
    apply Integrable.mono' hFav hKmeas
    filter_upwards [hle, hnn] with x hx1 hx2
    change ‖K * v' x‖ ≤ Fav x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK.le hx2)]
    exact hx1
  have hback : IntegrableOn (fun x => K⁻¹ * (K * v' x)) s volume :=
    Integrable.const_mul hKint K⁻¹
  refine IntegrableOn.congr_fun_ae hback ?_
  filter_upwards with x
  show K⁻¹ * (K * v' x) = v' x
  have hKne : K ≠ 0 := ne_of_gt hK
  rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]

-- An interval integral of `u` over a segment inside `(0, 1)` equals `L` times
-- the integral of `u'` when `u = L * u'` throughout `(0, 1)`.
private theorem intervalIntegral_congr_mul_of_eqOn
    (u u' : ℝ → ℝ) (L p q : ℝ)
    (hu : ∀ y ∈ Ioo (0 : ℝ) 1, u y = L * u' y)
    (hsub : Icc p q ⊆ Ioo (0 : ℝ) 1)
    (hpq : p ≤ q) :
    (∫ y in p..q, u y) = L * (∫ y in p..q, u' y) := by
  have hcongr : (∫ y in p..q, u y) = ∫ y in p..q, L * u' y := by
    conv_lhs => rw [integral_of_le hpq]
    conv_rhs => rw [integral_of_le hpq]
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards with y hy
    exact hu y (hsub (Ioc_subset_Icc_self hy))
  rw [hcongr, intervalIntegral.integral_const_mul]

-- Continuity in the lower limit of an interval integral over a set inside
-- `(0, 1)`, for an integrand continuous on `(0, 1)`.
private theorem continuousOn_intervalIntegral_left
    (w : ℝ → ℝ) (e : ℝ) (s : Set ℝ)
    (hw_cont : ContinuousOn w (Ioo 0 1))
    (hs : s ⊆ Ioo (0 : ℝ) 1)
    (hseg : ∀ x ∈ s, IntervalIntegrable w volume x e) :
    ContinuousOn (fun x => ∫ y in x..e, w y) s := by
  intro x hx
  have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hs hx
  have hcont : ContinuousAt w x :=
    hw_cont.continuousAt (isOpen_Ioo.mem_nhds hxIoo)
  have hmeas : StronglyMeasurableAtFilter w (𝓝 x) :=
    ⟨Ioo (0 : ℝ) 1, isOpen_Ioo.mem_nhds hxIoo,
      hw_cont.aestronglyMeasurable measurableSet_Ioo⟩
  exact (intervalIntegral.integral_hasDerivAt_left (hseg x hx) hmeas
    hcont).continuousAt.continuousWithinAt

-- Continuity in the upper limit of an interval integral over a set inside
-- `(0, 1)`, for an integrand continuous on `(0, 1)`.
private theorem continuousOn_intervalIntegral_right
    (w : ℝ → ℝ) (e : ℝ) (s : Set ℝ)
    (hw_cont : ContinuousOn w (Ioo 0 1))
    (hs : s ⊆ Ioo (0 : ℝ) 1)
    (hseg : ∀ x ∈ s, IntervalIntegrable w volume e x) :
    ContinuousOn (fun x => ∫ y in e..x, w y) s := by
  intro x hx
  have hxIoo : x ∈ Ioo (0 : ℝ) 1 := hs hx
  have hcont : ContinuousAt w x :=
    hw_cont.continuousAt (isOpen_Ioo.mem_nhds hxIoo)
  have hmeas : StronglyMeasurableAtFilter w (𝓝 x) :=
    ⟨Ioo (0 : ℝ) 1, isOpen_Ioo.mem_nhds hxIoo,
      hw_cont.aestronglyMeasurable measurableSet_Ioo⟩
  exact (intervalIntegral.integral_hasDerivAt_right (hseg x hx) hmeas
    hcont).continuousAt.continuousWithinAt

-- Left-endpoint Feller finiteness is preserved under rescaling of the two
-- densities by reciprocal positive constants, for ordered basepoints.
private theorem integrableOn_left_of_le
    (u u' v v' : ℝ → ℝ) (L : ℝ) (c c' : ℝ)
    (hL : 0 < L)
    (hu : ∀ y ∈ Ioo (0 : ℝ) 1, u y = L * u' y)
    (hv : ∀ x ∈ Ioo (0 : ℝ) 1, v x = L⁻¹ * v' x)
    (_hu_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u y)
    (_hv_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v x)
    (hu'_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u' y)
    (hv'_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v' x)
    (_hu_cont : ContinuousOn u (Ioo 0 1))
    (_hv_cont : ContinuousOn v (Ioo 0 1))
    (hu'_cont : ContinuousOn u' (Ioo 0 1))
    (hv'_cont : ContinuousOn v' (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1)
    (hcc' : c ≤ c') :
    IntegrableOn (fun x => (∫ y in x..c, u y) * v x) (Ioo 0 c) volume ↔
    IntegrableOn (fun x => (∫ y in x..c', u' y) * v' x) (Ioo 0 c') volume := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hcancel : ∀ A V : ℝ, (L * A) * (L⁻¹ * V) = A * V := by
    intro A V
    calc (L * A) * (L⁻¹ * V) = (L * L⁻¹) * (A * V) := by ring
      _ = A * V := by rw [mul_inv_cancel₀ hLne, one_mul]
  have hd0 : (0 : ℝ) < c / 2 := by linarith [hc.1]
  have hdc : c / 2 < c := by linarith [hc.1]
  have hd1 : c / 2 < 1 := by linarith [hc.1, hc.2]
  have hsubIco : Icc (c / 2) c ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨lt_of_lt_of_le hd0 hy.1, lt_of_le_of_lt hy.2 hc.2⟩
  have hv'Ico : IntegrableOn v' (Ico (c / 2) c) volume :=
    (hv'_cont.mono hsubIco).integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hpoint : ∀ x ∈ Ioo (0 : ℝ) c,
      (∫ y in x..c, u y) * v x
        = (∫ y in x..c', u' y) * v' x - (∫ y in c..c', u' y) * v' x := by
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_trans hx.2 hc.2⟩
    have hsub1 : Icc x c ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hc.2⟩
    have hsub2 : Icc x c' ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hc'.2⟩
    have hsub3 : Icc c c' ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hc'.2⟩
    have hi3 : IntervalIntegrable u' volume x c' :=
      (hu'_cont.mono hsub2).intervalIntegrable_of_Icc (hx.2.le.trans hcc')
    have hi2 : IntervalIntegrable u' volume c c' :=
      (hu'_cont.mono hsub3).intervalIntegrable_of_Icc hcc'
    have hscale : (∫ y in x..c, u y) = L * (∫ y in x..c, u' y) :=
      intervalIntegral_congr_mul_of_eqOn u u' L x c hu hsub1 hx.2.le
    have hadd : (∫ y in x..c', u' y) + (∫ y in c'..c, u' y)
        = ∫ y in x..c, u' y :=
      integral_add_adjacent_intervals hi3 hi2.symm
    have hsymm : (∫ y in c'..c, u' y) = -(∫ y in c..c', u' y) :=
      integral_symm c c'
    rw [hscale, ← hadd, hsymm, hv x hxIoo, hcancel]
    ring
  have hsub_dc' : Icc (c / 2) c' ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨lt_of_lt_of_le hd0 hy.1, lt_of_le_of_lt hy.2 hc'.2⟩
  have hη1 : 0 < ∫ y in (c / 2)..c, u' y := by
    apply intervalIntegral_pos_of_pos_on _ _ hdc
    · exact (hu'_cont.mono hsubIco).intervalIntegrable_of_Icc hdc.le
    · intro y hy
      exact hu'_pos y (hsubIco (Ioo_subset_Icc_self hy))
  have hη2 : 0 < ∫ y in (c / 2)..c', u' y := by
    have hlt : c / 2 < c' := lt_of_lt_of_le hdc hcc'
    apply intervalIntegral_pos_of_pos_on _ _ hlt
    · exact (hu'_cont.mono hsub_dc').intervalIntegrable_of_Icc hlt.le
    · intro y hy
      exact hu'_pos y (hsub_dc' (Ioo_subset_Icc_self hy))
  have hge1 : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      (∫ y in (c / 2)..c, u' y) * v' x ≤ (∫ y in x..c, u y) * v x := by
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hx.1, lt_trans hx.2 (lt_trans hdc hc.2)⟩
    have hxd : x ≤ c / 2 := hx.2.le
    have hsub_xd : Icc x (c / 2) ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hd1⟩
    have hsub_xc : Icc x c ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hc.2⟩
    have hadd : (∫ y in x..(c / 2), u' y) + (∫ y in (c / 2)..c, u' y)
        = ∫ y in x..c, u' y :=
      integral_add_adjacent_intervals
        ((hu'_cont.mono hsub_xd).intervalIntegrable_of_Icc hxd)
        ((hu'_cont.mono hsubIco).intervalIntegrable_of_Icc hdc.le)
    have hnn : 0 ≤ ∫ y in x..(c / 2), u' y := by
      apply intervalIntegral.integral_nonneg hxd
      intro y hy
      exact (hu'_pos y (hsub_xd hy)).le
    have hAle : (∫ y in (c / 2)..c, u' y) ≤ ∫ y in x..c, u' y := by
      linarith [hadd, hnn]
    have hscale : (∫ y in x..c, u y) = L * (∫ y in x..c, u' y) :=
      intervalIntegral_congr_mul_of_eqOn u u' L x c hu hsub_xc
        (hx.2.le.trans hdc.le)
    have hF : (∫ y in x..c, u y) * v x = (∫ y in x..c, u' y) * v' x := by
      rw [hscale, hv x hxIoo, hcancel]
    rw [hF]
    exact mul_le_mul_of_nonneg_right hAle (hv'_pos x hxIoo).le
  have hge2 : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      (∫ y in (c / 2)..c', u' y) * v' x
        ≤ (∫ y in x..c', u' y) * v' x := by
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hx.1, lt_trans hx.2 (lt_trans hdc hc.2)⟩
    have hxd : x ≤ c / 2 := hx.2.le
    have hsub_xd : Icc x (c / 2) ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hd1⟩
    have hlt : c / 2 < c' := lt_of_lt_of_le hdc hcc'
    have hadd : (∫ y in x..(c / 2), u' y) + (∫ y in (c / 2)..c', u' y)
        = ∫ y in x..c', u' y :=
      integral_add_adjacent_intervals
        ((hu'_cont.mono hsub_xd).intervalIntegrable_of_Icc hxd)
        ((hu'_cont.mono hsub_dc').intervalIntegrable_of_Icc hlt.le)
    have hnn : 0 ≤ ∫ y in x..(c / 2), u' y := by
      apply intervalIntegral.integral_nonneg hxd
      intro y hy
      exact (hu'_pos y (hsub_xd hy)).le
    have hAle : (∫ y in (c / 2)..c', u' y) ≤ ∫ y in x..c', u' y := by
      linarith [hadd, hnn]
    exact mul_le_mul_of_nonneg_right hAle (hv'_pos x hxIoo).le
  constructor
  · intro hFc
    have hFav : IntegrableOn (fun x => (∫ y in x..c, u y) * v x)
        (Ioo 0 (c / 2)) volume :=
      hFc.mono_set (fun x hx => ⟨hx.1, lt_trans hx.2 hdc⟩)
    have hle1 : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))),
        (∫ y in (c / 2)..c, u' y) * v' x
          ≤ (∫ y in x..c, u y) * v x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hge1 x hx
    have hnn1 : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))), 0 ≤ v' x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hv'_pos x ⟨hx.1, lt_trans hx.2 (lt_trans hdc hc.2)⟩).le
    have hv'Iood : IntegrableOn v' (Ioo 0 (c / 2)) volume :=
      integrableOn_of_mul_le _ _ _ _ hη1
        (hv'_cont.mono
          (fun x hx => ⟨hx.1, lt_trans hx.2 (lt_trans hdc hc.2)⟩))
        measurableSet_Ioo hFav hle1 hnn1
    have hv'Ioo : IntegrableOn v' (Ioo 0 c) volume := by
      rw [← Set.Ioo_union_Ico_eq_Ioo hd0 hdc.le]
      exact hv'Iood.union hv'Ico
    have hCv' : IntegrableOn (fun x => (∫ y in c..c', u' y) * v' x)
        (Ioo 0 c) volume :=
      Integrable.const_mul hv'Ioo _
    have hD : IntegrableOn (fun x => (∫ y in x..c', u' y) * v' x)
        (Ioo 0 c) volume := by
      have hadd2 := hFc.add hCv'
      refine IntegrableOn.congr_fun_ae hadd2 ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [Pi.add_apply]
      have h := hpoint x hx
      rw [h]
      ring
    have hsubcc' : Icc c c' ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hc'.2⟩
    have hF'cont : ContinuousOn (fun x => (∫ y in x..c', u' y) * v' x)
        (Icc c c') := by
      have hinner : ContinuousOn (fun x => ∫ y in x..c', u' y)
          (Icc c c') := by
        apply continuousOn_intervalIntegral_left u' c' (Icc c c') hu'_cont
          hsubcc'
        intro x hx
        have hsubx : Icc x c' ⊆ Ioo (0 : ℝ) 1 := by
          intro y hy
          exact ⟨lt_of_lt_of_le (lt_of_lt_of_le hc.1 hx.1) hy.1,
            lt_of_le_of_lt hy.2 hc'.2⟩
        exact (hu'_cont.mono hsubx).intervalIntegrable_of_Icc hx.2
      exact hinner.mul (hv'_cont.mono hsubcc')
    have hF'Ico : IntegrableOn (fun x => (∫ y in x..c', u' y) * v' x)
        (Ico c c') volume :=
      hF'cont.integrableOn_Icc.mono_set Ico_subset_Icc_self
    rw [← Set.Ioo_union_Ico_eq_Ioo hc.1 hcc']
    exact hD.union hF'Ico
  · intro hFc'
    have hsub' : IntegrableOn (fun x => (∫ y in x..c', u' y) * v' x)
        (Ioo 0 c) volume :=
      hFc'.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hcc'⟩)
    have hFav' : IntegrableOn (fun x => (∫ y in x..c', u' y) * v' x)
        (Ioo 0 (c / 2)) volume :=
      hFc'.mono_set
        (fun x hx => ⟨hx.1, lt_of_lt_of_le (lt_trans hx.2 hdc) hcc'⟩)
    have hle2 : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))),
        (∫ y in (c / 2)..c', u' y) * v' x
          ≤ (∫ y in x..c', u' y) * v' x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hge2 x hx
    have hnn2 : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))), 0 ≤ v' x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hv'_pos x ⟨hx.1, lt_trans hx.2 (lt_trans hdc hc.2)⟩).le
    have hv'Iood' : IntegrableOn v' (Ioo 0 (c / 2)) volume :=
      integrableOn_of_mul_le _ _ _ _ hη2
        (hv'_cont.mono
          (fun x hx => ⟨hx.1, lt_trans hx.2 (lt_trans hdc hc.2)⟩))
        measurableSet_Ioo hFav' hle2 hnn2
    have hv'Ioo' : IntegrableOn v' (Ioo 0 c) volume := by
      rw [← Set.Ioo_union_Ico_eq_Ioo hd0 hdc.le]
      exact hv'Iood'.union hv'Ico
    have hCv'' : IntegrableOn (fun x => (∫ y in c..c', u' y) * v' x)
        (Ioo 0 c) volume :=
      Integrable.const_mul hv'Ioo' _
    have hsub2 := hsub'.sub hCv''
    refine IntegrableOn.congr_fun_ae hsub2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [Pi.sub_apply]
    exact (hpoint x hx).symm

-- Right-endpoint Feller finiteness is preserved under rescaling of the two
-- densities by reciprocal positive constants, for ordered basepoints.
private theorem integrableOn_right_of_le
    (u u' v v' : ℝ → ℝ) (L : ℝ) (c c' : ℝ)
    (hL : 0 < L)
    (hu : ∀ y ∈ Ioo (0 : ℝ) 1, u y = L * u' y)
    (hv : ∀ x ∈ Ioo (0 : ℝ) 1, v x = L⁻¹ * v' x)
    (_hu_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u y)
    (_hv_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v x)
    (hu'_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u' y)
    (hv'_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v' x)
    (hu_cont : ContinuousOn u (Ioo 0 1))
    (hv_cont : ContinuousOn v (Ioo 0 1))
    (hu'_cont : ContinuousOn u' (Ioo 0 1))
    (hv'_cont : ContinuousOn v' (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1)
    (hcc' : c ≤ c') :
    IntegrableOn (fun x => (∫ y in c..x, u y) * v x) (Ioo c 1) volume ↔
    IntegrableOn (fun x => (∫ y in c'..x, u' y) * v' x) (Ioo c' 1) volume := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hcancel : ∀ A V : ℝ, (L * A) * (L⁻¹ * V) = A * V := by
    intro A V
    calc (L * A) * (L⁻¹ * V) = (L * L⁻¹) * (A * V) := by ring
      _ = A * V := by rw [mul_inv_cancel₀ hLne, one_mul]
  have hc'd : c' < (c' + 1) / 2 := by linarith [hc'.2]
  have hd1 : (c' + 1) / 2 < 1 := by linarith [hc'.2]
  have hd0 : (0 : ℝ) < (c' + 1) / 2 := by linarith [hc'.1]
  have hsubIoc : Icc c' ((c' + 1) / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨lt_of_lt_of_le hc'.1 hy.1, lt_of_le_of_lt hy.2 hd1⟩
  have hv'Ioc : IntegrableOn v' (Ioc c' ((c' + 1) / 2)) volume :=
    (hv'_cont.mono hsubIoc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hpoint : ∀ x ∈ Ioo c' 1,
      (∫ y in c..x, u y) * v x
        = (∫ y in c'..x, u' y) * v' x + (∫ y in c..c', u' y) * v' x := by
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_trans hc.1 (lt_of_le_of_lt hcc' hx.1), hx.2⟩
    have hcx : c ≤ x := le_trans hcc' hx.1.le
    have hsub1 : Icc c x ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    have hsub2 : Icc c' x ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hc'.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    have hsub3 : Icc c c' ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hc'.2⟩
    have hi1 : IntervalIntegrable u' volume c c' :=
      (hu'_cont.mono hsub3).intervalIntegrable_of_Icc hcc'
    have hi2 : IntervalIntegrable u' volume c' x :=
      (hu'_cont.mono hsub2).intervalIntegrable_of_Icc hx.1.le
    have hscale : (∫ y in c..x, u y) = L * (∫ y in c..x, u' y) :=
      intervalIntegral_congr_mul_of_eqOn u u' L c x hu hsub1 hcx
    have hadd : (∫ y in c..c', u' y) + (∫ y in c'..x, u' y)
        = ∫ y in c..x, u' y :=
      integral_add_adjacent_intervals hi1 hi2
    rw [hscale, ← hadd, hv x hxIoo, hcancel]
    ring
  have hcd : c < (c' + 1) / 2 := lt_of_le_of_lt hcc' hc'd
  have hsub_cd : Icc c ((c' + 1) / 2) ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hd1⟩
  have hη1 : 0 < ∫ y in c..((c' + 1) / 2), u' y := by
    apply intervalIntegral_pos_of_pos_on _ _ hcd
    · exact (hu'_cont.mono hsub_cd).intervalIntegrable_of_Icc hcd.le
    · intro y hy
      exact hu'_pos y (hsub_cd (Ioo_subset_Icc_self hy))
  have hη2 : 0 < ∫ y in c'..((c' + 1) / 2), u' y := by
    apply intervalIntegral_pos_of_pos_on _ _ hc'd
    · exact (hu'_cont.mono hsubIoc).intervalIntegrable_of_Icc hc'd.le
    · intro y hy
      exact hu'_pos y (hsubIoc (Ioo_subset_Icc_self hy))
  have hge1 : ∀ x ∈ Ioo ((c' + 1) / 2) 1,
      (∫ y in c..((c' + 1) / 2), u' y) * v' x
        ≤ (∫ y in c..x, u y) * v x := by
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hd0 hx.1, hx.2⟩
    have hdx : (c' + 1) / 2 ≤ x := hx.1.le
    have hcx : c ≤ x := le_trans hcd.le hdx
    have hsub_dx : Icc ((c' + 1) / 2) x ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hd0 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    have hsub_cx : Icc c x ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    have hadd : (∫ y in c..((c' + 1) / 2), u' y)
          + (∫ y in ((c' + 1) / 2)..x, u' y)
        = ∫ y in c..x, u' y :=
      integral_add_adjacent_intervals
        ((hu'_cont.mono hsub_cd).intervalIntegrable_of_Icc hcd.le)
        ((hu'_cont.mono hsub_dx).intervalIntegrable_of_Icc hdx)
    have hnn : 0 ≤ ∫ y in ((c' + 1) / 2)..x, u' y := by
      apply intervalIntegral.integral_nonneg hdx
      intro y hy
      exact (hu'_pos y (hsub_dx hy)).le
    have hAle : (∫ y in c..((c' + 1) / 2), u' y) ≤ ∫ y in c..x, u' y := by
      linarith [hadd, hnn]
    have hscale : (∫ y in c..x, u y) = L * (∫ y in c..x, u' y) :=
      intervalIntegral_congr_mul_of_eqOn u u' L c x hu hsub_cx hcx
    have hF : (∫ y in c..x, u y) * v x = (∫ y in c..x, u' y) * v' x := by
      rw [hscale, hv x hxIoo, hcancel]
    rw [hF]
    exact mul_le_mul_of_nonneg_right hAle (hv'_pos x hxIoo).le
  have hge2 : ∀ x ∈ Ioo ((c' + 1) / 2) 1,
      (∫ y in c'..((c' + 1) / 2), u' y) * v' x
        ≤ (∫ y in c'..x, u' y) * v' x := by
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hd0 hx.1, hx.2⟩
    have hdx : (c' + 1) / 2 ≤ x := hx.1.le
    have hsub_dx : Icc ((c' + 1) / 2) x ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hd0 hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    have hadd : (∫ y in c'..((c' + 1) / 2), u' y)
          + (∫ y in ((c' + 1) / 2)..x, u' y)
        = ∫ y in c'..x, u' y :=
      integral_add_adjacent_intervals
        ((hu'_cont.mono hsubIoc).intervalIntegrable_of_Icc hc'd.le)
        ((hu'_cont.mono hsub_dx).intervalIntegrable_of_Icc hdx)
    have hnn : 0 ≤ ∫ y in ((c' + 1) / 2)..x, u' y := by
      apply intervalIntegral.integral_nonneg hdx
      intro y hy
      exact (hu'_pos y (hsub_dx hy)).le
    have hAle : (∫ y in c'..((c' + 1) / 2), u' y) ≤ ∫ y in c'..x, u' y := by
      linarith [hadd, hnn]
    exact mul_le_mul_of_nonneg_right hAle (hv'_pos x hxIoo).le
  constructor
  · intro hGc
    have hsub : IntegrableOn (fun x => (∫ y in c..x, u y) * v x)
        (Ioo c' 1) volume :=
      hGc.mono_set (fun x hx => ⟨lt_of_le_of_lt hcc' hx.1, hx.2⟩)
    have hFav : IntegrableOn (fun x => (∫ y in c..x, u y) * v x)
        (Ioo ((c' + 1) / 2) 1) volume :=
      hGc.mono_set (fun x hx => ⟨lt_trans hcd hx.1, hx.2⟩)
    have hle1 : ∀ᵐ x ∂(volume.restrict (Ioo ((c' + 1) / 2) 1)),
        (∫ y in c..((c' + 1) / 2), u' y) * v' x
          ≤ (∫ y in c..x, u y) * v x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hge1 x hx
    have hnn1 : ∀ᵐ x ∂(volume.restrict (Ioo ((c' + 1) / 2) 1)),
        0 ≤ v' x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hv'_pos x ⟨lt_trans hd0 hx.1, hx.2⟩).le
    have hv'Ioo1 : IntegrableOn v' (Ioo ((c' + 1) / 2) 1) volume :=
      integrableOn_of_mul_le _ _ _ _ hη1
        (hv'_cont.mono (fun x hx => ⟨lt_trans hd0 hx.1, hx.2⟩))
        measurableSet_Ioo hFav hle1 hnn1
    have hv'Ioo : IntegrableOn v' (Ioo c' 1) volume := by
      rw [← Set.Ioc_union_Ioo_eq_Ioo hc'd.le hd1]
      exact hv'Ioc.union hv'Ioo1
    have hCv' : IntegrableOn (fun x => (∫ y in c..c', u' y) * v' x)
        (Ioo c' 1) volume :=
      Integrable.const_mul hv'Ioo _
    have hsub2 := hsub.sub hCv'
    refine IntegrableOn.congr_fun_ae hsub2 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [Pi.sub_apply]
    have h := hpoint x hx
    rw [h]
    ring
  · intro hGc'
    have hFav' : IntegrableOn (fun x => (∫ y in c'..x, u' y) * v' x)
        (Ioo ((c' + 1) / 2) 1) volume :=
      hGc'.mono_set (fun x hx => ⟨lt_trans hc'd hx.1, hx.2⟩)
    have hle2 : ∀ᵐ x ∂(volume.restrict (Ioo ((c' + 1) / 2) 1)),
        (∫ y in c'..((c' + 1) / 2), u' y) * v' x
          ≤ (∫ y in c'..x, u' y) * v' x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hge2 x hx
    have hnn2 : ∀ᵐ x ∂(volume.restrict (Ioo ((c' + 1) / 2) 1)),
        0 ≤ v' x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hv'_pos x ⟨lt_trans hd0 hx.1, hx.2⟩).le
    have hv'Ioo1' : IntegrableOn v' (Ioo ((c' + 1) / 2) 1) volume :=
      integrableOn_of_mul_le _ _ _ _ hη2
        (hv'_cont.mono (fun x hx => ⟨lt_trans hd0 hx.1, hx.2⟩))
        measurableSet_Ioo hFav' hle2 hnn2
    have hv'Ioo' : IntegrableOn v' (Ioo c' 1) volume := by
      rw [← Set.Ioc_union_Ioo_eq_Ioo hc'd.le hd1]
      exact hv'Ioc.union hv'Ioo1'
    have hCv'' : IntegrableOn (fun x => (∫ y in c..c', u' y) * v' x)
        (Ioo c' 1) volume :=
      Integrable.const_mul hv'Ioo' _
    have hD : IntegrableOn (fun x => (∫ y in c..x, u y) * v x)
        (Ioo c' 1) volume := by
      have hadd2 := hGc'.add hCv''
      refine IntegrableOn.congr_fun_ae hadd2 ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [Pi.add_apply]
      exact (hpoint x hx).symm
    have hsubcc' : Icc c c' ⊆ Ioo (0 : ℝ) 1 := by
      intro y hy
      exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hc'.2⟩
    have hGcont : ContinuousOn (fun x => (∫ y in c..x, u y) * v x)
        (Icc c c') := by
      have hinner : ContinuousOn (fun x => ∫ y in c..x, u y)
          (Icc c c') := by
        apply continuousOn_intervalIntegral_right u c (Icc c c') hu_cont
          hsubcc'
        intro x hx
        have hsubx : Icc c x ⊆ Ioo (0 : ℝ) 1 := by
          intro y hy
          exact ⟨lt_of_lt_of_le hc.1 hy.1,
            lt_of_le_of_lt hy.2 (lt_of_le_of_lt hx.2 hc'.2)⟩
        exact (hu_cont.mono hsubx).intervalIntegrable_of_Icc hx.1
      exact hinner.mul (hv_cont.mono hsubcc')
    have hGIoc : IntegrableOn (fun x => (∫ y in c..x, u y) * v x)
        (Ioc c c') volume :=
      hGcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [← Set.Ioc_union_Ioo_eq_Ioo hcc' hc'.2]
    exact hGIoc.union hD

-- Left-endpoint Feller finiteness for arbitrary interior basepoints, by
-- symmetry in the order of the basepoints.
private theorem integrableOn_left_of_rescale
    (u u' v v' : ℝ → ℝ) (L : ℝ) (c c' : ℝ)
    (hL : 0 < L)
    (hu : ∀ y ∈ Ioo (0 : ℝ) 1, u y = L * u' y)
    (hv : ∀ x ∈ Ioo (0 : ℝ) 1, v x = L⁻¹ * v' x)
    (hu_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u y)
    (hv_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v x)
    (hu'_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u' y)
    (hv'_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v' x)
    (hu_cont : ContinuousOn u (Ioo 0 1))
    (hv_cont : ContinuousOn v (Ioo 0 1))
    (hu'_cont : ContinuousOn u' (Ioo 0 1))
    (hv'_cont : ContinuousOn v' (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in x..c, u y) * v x) (Ioo 0 c) volume ↔
    IntegrableOn (fun x => (∫ y in x..c', u' y) * v' x) (Ioo 0 c') volume := by
  rcases le_total c c' with h | h
  · exact integrableOn_left_of_le u u' v v' L c c' hL hu hv hu_pos hv_pos
      hu'_pos hv'_pos hu_cont hv_cont hu'_cont hv'_cont hc hc' h
  · have hLne : L ≠ 0 := ne_of_gt hL
    have hu's : ∀ y ∈ Ioo (0 : ℝ) 1, u' y = L⁻¹ * u y := by
      intro y hy
      rw [hu y hy, ← mul_assoc, inv_mul_cancel₀ hLne, one_mul]
    have hv's : ∀ x ∈ Ioo (0 : ℝ) 1, v' x = (L⁻¹)⁻¹ * v x := by
      intro x hx
      rw [inv_inv, hv x hx, ← mul_assoc, mul_inv_cancel₀ hLne, one_mul]
    have hsymm := integrableOn_left_of_le u' u v' v L⁻¹ c' c (inv_pos.mpr hL)
      hu's hv's hu'_pos hv'_pos hu_pos hv_pos hu'_cont hv'_cont hu_cont hv_cont
      hc' hc h
    exact hsymm.symm

-- Right-endpoint Feller finiteness for arbitrary interior basepoints, by
-- symmetry in the order of the basepoints.
private theorem integrableOn_right_of_rescale
    (u u' v v' : ℝ → ℝ) (L : ℝ) (c c' : ℝ)
    (hL : 0 < L)
    (hu : ∀ y ∈ Ioo (0 : ℝ) 1, u y = L * u' y)
    (hv : ∀ x ∈ Ioo (0 : ℝ) 1, v x = L⁻¹ * v' x)
    (hu_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u y)
    (hv_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v x)
    (hu'_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < u' y)
    (hv'_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < v' x)
    (hu_cont : ContinuousOn u (Ioo 0 1))
    (hv_cont : ContinuousOn v (Ioo 0 1))
    (hu'_cont : ContinuousOn u' (Ioo 0 1))
    (hv'_cont : ContinuousOn v' (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in c..x, u y) * v x) (Ioo c 1) volume ↔
    IntegrableOn (fun x => (∫ y in c'..x, u' y) * v' x) (Ioo c' 1) volume := by
  rcases le_total c c' with h | h
  · exact integrableOn_right_of_le u u' v v' L c c' hL hu hv hu_pos hv_pos
      hu'_pos hv'_pos hu_cont hv_cont hu'_cont hv'_cont hc hc' h
  · have hLne : L ≠ 0 := ne_of_gt hL
    have hu's : ∀ y ∈ Ioo (0 : ℝ) 1, u' y = L⁻¹ * u y := by
      intro y hy
      rw [hu y hy, ← mul_assoc, inv_mul_cancel₀ hLne, one_mul]
    have hv's : ∀ x ∈ Ioo (0 : ℝ) 1, v' x = (L⁻¹)⁻¹ * v x := by
      intro x hx
      rw [inv_inv, hv x hx, ← mul_assoc, mul_inv_cancel₀ hLne, one_mul]
    have hsymm := integrableOn_right_of_le u' u v' v L⁻¹ c' c (inv_pos.mpr hL)
      hu's hv's hu'_pos hv'_pos hu_pos hv_pos hu'_cont hv'_cont hu_cont hv_cont
      hc' hc h
    exact hsymm.symm

-- The scale density at basepoint `c` is a positive constant multiple of the
-- scale density at basepoint `c'`, on the open interval.
private theorem scaleDensityFrom_basepoint_rescale
    (b a : ℝ → ℝ) (c c' : ℝ)
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    ∀ y ∈ Ioo (0 : ℝ) 1, scaleDensityFrom b a c y
      = Real.exp (-∫ z in c..c', 2 * b z / a z)
        * scaleDensityFrom b a c' y := by
  have hf_cont : ContinuousOn (fun z => 2 * b z / a z) (Ioo (0 : ℝ) 1) := by
    have h2 : ContinuousOn (fun z => 2 * (b z / a z)) (Ioo (0 : ℝ) 1) :=
      continuousOn_const.mul hdiv_cont
    have hfun : (fun z => 2 * b z / a z) = fun z => 2 * (b z / a z) := by
      funext z
      exact mul_div_assoc _ _ _
    rwa [hfun]
  have hseg_cc' : IntervalIntegrable (fun z => 2 * b z / a z) volume c c' := by
    rcases le_total c c' with h | h
    · have hsub : Icc c c' ⊆ Ioo (0 : ℝ) 1 := by
        intro y hy
        exact ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hc'.2⟩
      exact (hf_cont.mono hsub).intervalIntegrable_of_Icc h
    · have hsub : Icc c' c ⊆ Ioo (0 : ℝ) 1 := by
        intro y hy
        exact ⟨lt_of_lt_of_le hc'.1 hy.1, lt_of_le_of_lt hy.2 hc.2⟩
      exact ((hf_cont.mono hsub).intervalIntegrable_of_Icc h).symm
  intro y hy
  have hseg_c'y : IntervalIntegrable (fun z => 2 * b z / a z) volume c' y := by
    rcases le_total c' y with h | h
    · have hsub : Icc c' y ⊆ Ioo (0 : ℝ) 1 := by
        intro z hz
        exact ⟨lt_of_lt_of_le hc'.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
      exact (hf_cont.mono hsub).intervalIntegrable_of_Icc h
    · have hsub : Icc y c' ⊆ Ioo (0 : ℝ) 1 := by
        intro z hz
        exact ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hc'.2⟩
      exact ((hf_cont.mono hsub).intervalIntegrable_of_Icc h).symm
  have hadd : (∫ z in c..c', 2 * b z / a z) + (∫ z in c'..y, 2 * b z / a z)
      = ∫ z in c..y, 2 * b z / a z :=
    integral_add_adjacent_intervals hseg_cc' hseg_c'y
  unfold scaleDensityFrom
  rw [← hadd, neg_add, Real.exp_add]

-- The speed density at basepoint `c` is the reciprocal positive constant
-- multiple of the speed density at basepoint `c'`, on the open interval.
private theorem speedDensityFrom_basepoint_rescale
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, speedDensityFrom b a c x
      = (Real.exp (-∫ z in c..c', 2 * b z / a z))⁻¹
        * speedDensityFrom b a c' x := by
  intro x hx
  have hψ := scaleDensityFrom_basepoint_rescale b a c c' hdiv_cont hc hc' x hx
  have hK : Real.exp (-∫ z in c..c', 2 * b z / a z) ≠ 0 := Real.exp_ne_zero _
  have hψ' : scaleDensityFrom b a c' x ≠ 0 :=
    (scaleDensityFrom_pos b a c' x).ne'
  have ha : a x ≠ 0 := (ha_pos x hx).ne'
  have haKψ : a x * (Real.exp (-∫ z in c..c', 2 * b z / a z)
      * scaleDensityFrom b a c' x) ≠ 0 :=
    mul_ne_zero ha (mul_ne_zero hK hψ')
  have haψ : a x * scaleDensityFrom b a c' x ≠ 0 := mul_ne_zero ha hψ'
  unfold speedDensityFrom
  rw [hψ]
  field_simp

-- The scale density is continuous on the open interval.
private theorem continuousOn_scaleDensityFrom
    (b a : ℝ → ℝ) (c : ℝ)
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (scaleDensityFrom b a c) (Ioo 0 1) := by
  intro x hx
  exact ((hasDerivAt_scaleDensityFrom b a c x hdiv_cont hx
    hc).continuousAt).continuousWithinAt

-- The speed density is continuous on the open interval.
private theorem continuousOn_speedDensityFrom
    (b a : ℝ → ℝ) (c : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (speedDensityFrom b a c) (Ioo 0 1) := by
  have hψ := continuousOn_scaleDensityFrom b a c hdiv_cont hc
  have hdiv : ContinuousOn (fun x => 2 / (a x * scaleDensityFrom b a c x))
      (Ioo 0 1) :=
    continuousOn_const.div (ha_cont.mul hψ) (fun x hx =>
      mul_ne_zero (ha_pos x hx).ne' (scaleDensityFrom_pos b a c x).ne')
  exact hdiv

-- Basepoint helpers state finiteness equivalence of each Feller functional
-- between two interior basepoints.
private theorem integrableOn_left_sigma_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
      scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ↔
    IntegrableOn (fun x => (∫ y in x..c', speedDensityFrom b a c' y) *
      scaleDensityFrom b a c' x) (Set.Ioo 0 c') volume := by
  have hK : 0 < Real.exp (-∫ z in c..c', 2 * b z / a z) := Real.exp_pos _
  have hψ := scaleDensityFrom_basepoint_rescale b a c c' hdiv_cont hc hc'
  have hm := speedDensityFrom_basepoint_rescale b a c c' ha_pos hdiv_cont
    hc hc'
  have hψc := continuousOn_scaleDensityFrom b a c hdiv_cont hc
  have hψc' := continuousOn_scaleDensityFrom b a c' hdiv_cont hc'
  have hmc := continuousOn_speedDensityFrom b a c ha_pos ha_cont hdiv_cont hc
  have hmc' := continuousOn_speedDensityFrom b a c' ha_pos ha_cont hdiv_cont
    hc'
  have hvswap : ∀ x ∈ Ioo (0 : ℝ) 1, scaleDensityFrom b a c x
      = ((Real.exp (-∫ z in c..c', 2 * b z / a z))⁻¹)⁻¹
        * scaleDensityFrom b a c' x := by
    intro x hx
    rw [inv_inv]
    exact hψ x hx
  exact integrableOn_left_of_rescale (speedDensityFrom b a c)
    (speedDensityFrom b a c') (scaleDensityFrom b a c)
    (scaleDensityFrom b a c')
    (Real.exp (-∫ z in c..c', 2 * b z / a z))⁻¹ c c' (inv_pos.mpr hK) hm
    hvswap
    (fun x hx => speedDensityFrom_pos b a c x ha_pos hx)
    (fun x hx => scaleDensityFrom_pos b a c x)
    (fun x hx => speedDensityFrom_pos b a c' x ha_pos hx)
    (fun x hx => scaleDensityFrom_pos b a c' x)
    hmc hψc hmc' hψc' hc hc'

private theorem integrableOn_left_scale_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
      speedDensityFrom b a c x) (Set.Ioo 0 c) volume ↔
    IntegrableOn (fun x => (∫ y in x..c', scaleDensityFrom b a c' y) *
      speedDensityFrom b a c' x) (Set.Ioo 0 c') volume := by
  have hK : 0 < Real.exp (-∫ z in c..c', 2 * b z / a z) := Real.exp_pos _
  have hψ := scaleDensityFrom_basepoint_rescale b a c c' hdiv_cont hc hc'
  have hm := speedDensityFrom_basepoint_rescale b a c c' ha_pos hdiv_cont
    hc hc'
  have hψc := continuousOn_scaleDensityFrom b a c hdiv_cont hc
  have hψc' := continuousOn_scaleDensityFrom b a c' hdiv_cont hc'
  have hmc := continuousOn_speedDensityFrom b a c ha_pos ha_cont hdiv_cont hc
  have hmc' := continuousOn_speedDensityFrom b a c' ha_pos ha_cont hdiv_cont
    hc'
  exact integrableOn_left_of_rescale (scaleDensityFrom b a c)
    (scaleDensityFrom b a c') (speedDensityFrom b a c)
    (speedDensityFrom b a c')
    (Real.exp (-∫ z in c..c', 2 * b z / a z)) c c' hK hψ hm
    (fun x hx => scaleDensityFrom_pos b a c x)
    (fun x hx => speedDensityFrom_pos b a c x ha_pos hx)
    (fun x hx => scaleDensityFrom_pos b a c' x)
    (fun x hx => speedDensityFrom_pos b a c' x ha_pos hx)
    hψc hmc hψc' hmc' hc hc'

private theorem integrableOn_right_sigma_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
      scaleDensityFrom b a c x) (Set.Ioo c 1) volume ↔
    IntegrableOn (fun x => (∫ y in c'..x, speedDensityFrom b a c' y) *
      scaleDensityFrom b a c' x) (Set.Ioo c' 1) volume := by
  have hK : 0 < Real.exp (-∫ z in c..c', 2 * b z / a z) := Real.exp_pos _
  have hψ := scaleDensityFrom_basepoint_rescale b a c c' hdiv_cont hc hc'
  have hm := speedDensityFrom_basepoint_rescale b a c c' ha_pos hdiv_cont
    hc hc'
  have hψc := continuousOn_scaleDensityFrom b a c hdiv_cont hc
  have hψc' := continuousOn_scaleDensityFrom b a c' hdiv_cont hc'
  have hmc := continuousOn_speedDensityFrom b a c ha_pos ha_cont hdiv_cont hc
  have hmc' := continuousOn_speedDensityFrom b a c' ha_pos ha_cont hdiv_cont
    hc'
  have hvswap : ∀ x ∈ Ioo (0 : ℝ) 1, scaleDensityFrom b a c x
      = ((Real.exp (-∫ z in c..c', 2 * b z / a z))⁻¹)⁻¹
        * scaleDensityFrom b a c' x := by
    intro x hx
    rw [inv_inv]
    exact hψ x hx
  exact integrableOn_right_of_rescale (speedDensityFrom b a c)
    (speedDensityFrom b a c') (scaleDensityFrom b a c)
    (scaleDensityFrom b a c')
    (Real.exp (-∫ z in c..c', 2 * b z / a z))⁻¹ c c' (inv_pos.mpr hK) hm
    hvswap
    (fun x hx => speedDensityFrom_pos b a c x ha_pos hx)
    (fun x hx => scaleDensityFrom_pos b a c x)
    (fun x hx => speedDensityFrom_pos b a c' x ha_pos hx)
    (fun x hx => scaleDensityFrom_pos b a c' x)
    hmc hψc hmc' hψc' hc hc'

private theorem integrableOn_right_scale_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
      speedDensityFrom b a c x) (Set.Ioo c 1) volume ↔
    IntegrableOn (fun x => (∫ y in c'..x, scaleDensityFrom b a c' y) *
      speedDensityFrom b a c' x) (Set.Ioo c' 1) volume := by
  have hK : 0 < Real.exp (-∫ z in c..c', 2 * b z / a z) := Real.exp_pos _
  have hψ := scaleDensityFrom_basepoint_rescale b a c c' hdiv_cont hc hc'
  have hm := speedDensityFrom_basepoint_rescale b a c c' ha_pos hdiv_cont
    hc hc'
  have hψc := continuousOn_scaleDensityFrom b a c hdiv_cont hc
  have hψc' := continuousOn_scaleDensityFrom b a c' hdiv_cont hc'
  have hmc := continuousOn_speedDensityFrom b a c ha_pos ha_cont hdiv_cont hc
  have hmc' := continuousOn_speedDensityFrom b a c' ha_pos ha_cont hdiv_cont
    hc'
  exact integrableOn_right_of_rescale (scaleDensityFrom b a c)
    (scaleDensityFrom b a c') (speedDensityFrom b a c)
    (speedDensityFrom b a c')
    (Real.exp (-∫ z in c..c', 2 * b z / a z)) c c' hK hψ hm
    (fun x hx => scaleDensityFrom_pos b a c x)
    (fun x hx => speedDensityFrom_pos b a c x ha_pos hx)
    (fun x hx => scaleDensityFrom_pos b a c' x)
    (fun x hx => speedDensityFrom_pos b a c' x ha_pos hx)
    hψc hmc hψc' hmc' hc hc'

-- With the coefficient hypotheses fixed, admissibility only depends on the
-- basepoint being interior.
private theorem isFellerAdmissible_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsFellerAdmissible b a c ↔ IsFellerAdmissible b a c' :=
  ⟨fun _ => ⟨hc', ha_pos, ha_cont, hdiv_cont⟩, fun _ => ⟨hc, ha_pos, ha_cont, hdiv_cont⟩⟩

/-- Basepoint independence of the regular case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, regularity at basepoint `c`
holds iff it holds at `c'`, for interior basepoints `c` and `c'`. Reference:
Karlin and Taylor (1981), Chapter 15. -/
theorem isRegularBoundaryAtZero_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsRegularBoundaryAtZero b a c ↔ IsRegularBoundaryAtZero b a c' := by
  unfold IsRegularBoundaryAtZero
  have hP :=
    integrableOn_left_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_left_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr hP hQ)

/-- Basepoint independence of the exit case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the exit classification at
basepoint `c` holds iff it holds at `c'`, for interior basepoints `c` and
`c'`. Reference: Karlin and Taylor (1981), Chapter 15. -/
theorem isExitBoundaryAtZero_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsExitBoundaryAtZero b a c ↔ IsExitBoundaryAtZero b a c' := by
  unfold IsExitBoundaryAtZero
  have hP :=
    integrableOn_left_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_left_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr hP (not_congr hQ))

/-- Basepoint independence of the entrance case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the entrance classification at
basepoint `c` holds iff it holds at `c'`, for interior basepoints `c` and
`c'`. Reference: Karlin and Taylor (1981), Chapter 15. -/
theorem isEntranceBoundaryAtZero_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsEntranceBoundaryAtZero b a c ↔ IsEntranceBoundaryAtZero b a c' := by
  unfold IsEntranceBoundaryAtZero
  have hP :=
    integrableOn_left_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_left_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr (not_congr hP) hQ)

/-- Basepoint independence of the natural case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the natural classification at
basepoint `c` holds iff it holds at `c'`, for interior basepoints `c` and
`c'`. Reference: Karlin and Taylor (1981), Chapter 15. -/
theorem isNaturalBoundaryAtZero_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsNaturalBoundaryAtZero b a c ↔ IsNaturalBoundaryAtZero b a c' := by
  unfold IsNaturalBoundaryAtZero
  have hP :=
    integrableOn_left_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_left_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr (not_congr hP) (not_congr hQ))

/-- Basepoint independence of the regular case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, regularity at basepoint `c`
holds iff it holds at `c'`, for interior basepoints `c` and `c'`. Reference:
Karlin and Taylor (1981), Chapter 15. -/
theorem isRegularBoundaryAtOne_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsRegularBoundaryAtOne b a c ↔ IsRegularBoundaryAtOne b a c' := by
  unfold IsRegularBoundaryAtOne
  have hP :=
    integrableOn_right_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_right_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr hP hQ)

/-- Basepoint independence of the exit case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the exit classification at
basepoint `c` holds iff it holds at `c'`, for interior basepoints `c` and
`c'`. Reference: Karlin and Taylor (1981), Chapter 15. -/
theorem isExitBoundaryAtOne_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsExitBoundaryAtOne b a c ↔ IsExitBoundaryAtOne b a c' := by
  unfold IsExitBoundaryAtOne
  have hP :=
    integrableOn_right_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_right_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr hP (not_congr hQ))

/-- Basepoint independence of the entrance case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the entrance classification at
basepoint `c` holds iff it holds at `c'`, for interior basepoints `c` and
`c'`. Reference: Karlin and Taylor (1981), Chapter 15. -/
theorem isEntranceBoundaryAtOne_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsEntranceBoundaryAtOne b a c ↔ IsEntranceBoundaryAtOne b a c' := by
  unfold IsEntranceBoundaryAtOne
  have hP :=
    integrableOn_right_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_right_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr (not_congr hP) hQ)

/-- Basepoint independence of the natural case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the natural classification at
basepoint `c` holds iff it holds at `c'`, for interior basepoints `c` and
`c'`. Reference: Karlin and Taylor (1981), Chapter 15. -/
theorem isNaturalBoundaryAtOne_basepoint_iff
    (b a : ℝ → ℝ) (c c' : ℝ)
    (ha_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < a x)
    (ha_cont : ContinuousOn a (Ioo 0 1))
    (hdiv_cont : ContinuousOn (fun x => b x / a x) (Ioo 0 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hc' : c' ∈ Ioo (0 : ℝ) 1) :
    IsNaturalBoundaryAtOne b a c ↔ IsNaturalBoundaryAtOne b a c' := by
  unfold IsNaturalBoundaryAtOne
  have hP :=
    integrableOn_right_sigma_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  have hQ :=
    integrableOn_right_scale_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc'
  exact and_congr (isFellerAdmissible_basepoint_iff b a c c' ha_pos ha_cont hdiv_cont hc hc')
    (and_congr (not_congr hP) (not_congr hQ))
end MathlibExt.Probability.Diffusion
