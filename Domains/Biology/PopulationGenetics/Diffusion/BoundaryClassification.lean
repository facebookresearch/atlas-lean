/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.SingularSpeedMeasure
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Defs.Filter
public import Domains.Biology.PopulationGenetics.Diffusion.SelectionMutationSpeedMeasure
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
The predicates record these raw finiteness patterns at the chosen
basepoint; the classification reading is for an interior basepoint, which
every theorem below assumes.

The classification is independent of the interior basepoint. For the
Wright-Fisher selection-mutation diffusion (see Ewens (2004), Chapter 4)
with nonnegative mutation parameters, each endpoint is exit, regular, or
entrance according as the corresponding mutation parameter equals `0`,
lies strictly between `0` and `1`, or is at least `1`, independently of
selection and of the other endpoint's parameter. For a general real
parameter the analytic criteria proved below are finiteness of `Σ` exactly
below `1` and finiteness of `N` exactly above `0`, so the exit pattern also
occurs for negative parameters, which are outside the population-genetics
reading.

This is Feller's analytic integral test only: the predicates record which
Feller functionals are finite. Attainability or non-attainability of the
boundary, boundary conditions for a semigroup, and existence or uniqueness of
extensions are not claimed; the process-level reading requires Feller
boundary theory not developed here.

## References

* Karlin, S. and Taylor, H. M. (1981). *A Second Course in Stochastic
  Processes*. Academic Press, Chapter 15.
* Ewens, W. J. (2004). *Mathematical Population Genetics 1: Theoretical
  Introduction*. Second edition. Springer, Chapter 4.
-/

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The left endpoint `0` is **regular** in Feller's classification (Karlin
and Taylor (1981), Chapter 15): both the scale-weighted speed integral `Σ₀`
and the speed-weighted scale integral `N₀` are finite. Finiteness is
`MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo 0 c`, with inner
interval integrals from `x` to the interior basepoint `c`. The predicate
records which Feller functionals are finite only; it does not claim
attainability of the boundary. -/
public noncomputable def IsRegularBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The left endpoint `0` is an **exit** boundary (Karlin and Taylor (1981),
Chapter 15): the Feller functional `Σ₀` is finite while `N₀` is infinite.
Finiteness is `MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo 0 c`,
with inner interval integrals from `x` to the interior basepoint `c`, and
infinitude is the negation of finiteness. The predicate records which Feller
functionals are finite only; it does not claim attainability. -/
public noncomputable def IsExitBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  ¬ IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The left endpoint `0` is an **entrance** boundary (Karlin and Taylor
(1981), Chapter 15): the Feller functional `Σ₀` is infinite while `N₀` is
finite. Finiteness is `MeasureTheory.IntegrableOn` against `volume` on
`Set.Ioo 0 c`, with inner interval integrals from `x` to the interior
basepoint `c`, and infinitude is the negation of finiteness. The predicate
records which Feller functionals are finite only; it does not claim
attainability. -/
public noncomputable def IsEntranceBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The left endpoint `0` is a **natural** boundary (Karlin and Taylor (1981),
Chapter 15): both Feller functionals `Σ₀` and `N₀` are infinite. Finiteness
is `MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo 0 c`, with inner
interval integrals from `x` to the interior basepoint `c`, and infinitude is
the negation of finiteness. The predicate records which Feller functionals
are finite only; it does not claim attainability. -/
public noncomputable def IsNaturalBoundaryAtZero (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo 0 c) volume ∧
  ¬ IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo 0 c) volume

/-- The right endpoint `1` is **regular** in Feller's classification (Karlin
and Taylor (1981), Chapter 15): both the scale-weighted speed integral `Σ₁`
and the speed-weighted scale integral `N₁` are finite. Finiteness is
`MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo c 1`, with inner
interval integrals from the interior basepoint `c` to `x`. The predicate
records which Feller functionals are finite only; it does not claim
attainability of the boundary. -/
public noncomputable def IsRegularBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo c 1) volume ∧
  IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo c 1) volume

/-- The right endpoint `1` is an **exit** boundary (Karlin and Taylor (1981),
Chapter 15): the Feller functional `Σ₁` is finite while `N₁` is infinite.
Finiteness is `MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo c 1`,
with inner interval integrals from the interior basepoint `c` to `x`, and
infinitude is the negation of finiteness. The predicate records which Feller
functionals are finite only; it does not claim attainability. -/
public noncomputable def IsExitBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo c 1) volume ∧
  ¬ IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo c 1) volume

/-- The right endpoint `1` is an **entrance** boundary (Karlin and Taylor
(1981), Chapter 15): the Feller functional `Σ₁` is infinite while `N₁` is
finite. Finiteness is `MeasureTheory.IntegrableOn` against `volume` on
`Set.Ioo c 1`, with inner interval integrals from the interior basepoint `c`
to `x`, and infinitude is the negation of finiteness. The predicate records
which Feller functionals are finite only; it does not claim attainability. -/
public noncomputable def IsEntranceBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
  ¬ IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom b a c y) *
    scaleDensityFrom b a c x) (Set.Ioo c 1) volume ∧
  IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom b a c y) *
    speedDensityFrom b a c x) (Set.Ioo c 1) volume

/-- The right endpoint `1` is a **natural** boundary (Karlin and Taylor
(1981), Chapter 15): both Feller functionals `Σ₁` and `N₁` are infinite.
Finiteness is `MeasureTheory.IntegrableOn` against `volume` on `Set.Ioo c 1`,
with inner interval integrals from the interior basepoint `c` to `x`, and
infinitude is the negation of finiteness. The predicate records which Feller
functionals are finite only; it does not claim attainability. -/
public noncomputable def IsNaturalBoundaryAtOne (b a : ℝ → ℝ) (c : ℝ) : Prop :=
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
    show ‖K * v' x‖ ≤ Fav x
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
-- between basepoints. Wright-Fisher helpers state finiteness equivalence
-- with the stated mutation-parameter inequality.
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



private theorem wrightFisher_left_speed_pos (α θ₁ θ₂ x : ℝ)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < selectionMutationSpeedDensity α θ₁ θ₂ x := by
  have hx0 : 0 < x := hx.1
  have h1x : 0 < 1 - x := by linarith [hx.2]
  simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
    mul_assoc, mul_comm, mul_left_comm]
  positivity

private theorem wrightFisher_left_scale_pos (α θ₁ θ₂ x : ℝ)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < selectionMutationScaleDensity α θ₁ θ₂ x := by
  have hx0 : 0 < x := hx.1
  have h1x : 0 < 1 - x := by linarith [hx.2]
  simp only [selectionMutationScaleDensity, mutationScaleDensity,
    mul_assoc, mul_comm, mul_left_comm]
  positivity

private theorem wrightFisher_left_split (f : ℝ → ℝ) (c : ℝ)
    (hc0 : 0 < c) :
    IntegrableOn f (Ioo 0 c) volume ↔
      IntegrableOn f (Ioo 0 (c / 2)) volume ∧
        IntegrableOn f (Ico (c / 2) c) volume := by
  have hc2pos : 0 < c / 2 := by linarith
  have hc2lt : c / 2 < c := by linarith
  have heq : Ioo 0 c = Ioo 0 (c / 2) ∪ Ico (c / 2) c := by
    ext x
    simp only [mem_Ioo, mem_Ico, mem_union]
    constructor
    · intro hx
      by_cases h : x < c / 2
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨le_of_not_gt h, hx.2⟩
    · intro hx
      rcases hx with ⟨hx0, hxc2⟩ | ⟨hxc2, hxc⟩
      · exact ⟨hx0, lt_trans hxc2 hc2lt⟩
      · exact ⟨lt_of_lt_of_le hc2pos hxc2, hxc⟩
  constructor
  · intro h
    have hsub1 : Ioo 0 (c / 2) ⊆ Ioo 0 c := by
      intro x hx
      exact ⟨hx.1, lt_trans hx.2 hc2lt⟩
    have hsub2 : Ico (c / 2) c ⊆ Ioo 0 c := by
      intro x hx
      exact ⟨lt_of_lt_of_le hc2pos hx.1, hx.2⟩
    exact ⟨h.mono_set hsub1, h.mono_set hsub2⟩
  · intro h
    rw [heq]
    exact h.1.union h.2

private theorem wrightFisher_left_continuous_speedFactor_on
    (α θ₂ : ℝ) {s : Set ℝ} (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (fun y : ℝ => Real.exp (2 * α * y) * (2 * (1 - y) ^ (θ₂ - 1)))
      s := by
  have hsub : ContinuousOn (fun y : ℝ => (1 : ℝ) - y) s :=
    continuousOn_const.sub continuousOn_id
  have hpow : ContinuousOn (fun y : ℝ => ((1 : ℝ) - y) ^ (θ₂ - 1)) s :=
    ContinuousOn.rpow_const hsub
      (fun y hy => Or.inl (ne_of_gt (by linarith [h1 y hy])))
  have hexp : ContinuousOn (fun y : ℝ => Real.exp (2 * α * y)) s :=
    Real.continuous_exp.comp_continuousOn'
      (continuousOn_const.mul continuousOn_id)
  exact hexp.mul (continuousOn_const.mul hpow)

private theorem wrightFisher_left_continuous_scaleFactor_on
    (α θ₂ : ℝ) {s : Set ℝ} (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (fun x : ℝ => Real.exp (-2 * α * x) * (1 - x) ^ (-θ₂))
      s := by
  have hsub : ContinuousOn (fun x : ℝ => (1 : ℝ) - x) s :=
    continuousOn_const.sub continuousOn_id
  have hpow : ContinuousOn (fun x : ℝ => ((1 : ℝ) - x) ^ (-θ₂)) s :=
    ContinuousOn.rpow_const hsub
      (fun x hx => Or.inl (ne_of_gt (by linarith [h1 x hx])))
  have hexp : ContinuousOn (fun x : ℝ => Real.exp (-2 * α * x)) s :=
    Real.continuous_exp.comp_continuousOn'
      (continuousOn_const.mul continuousOn_id)
  exact hexp.mul hpow

private theorem wrightFisher_left_speed_factor_eq (α θ₁ θ₂ y : ℝ) :
    selectionMutationSpeedDensity α θ₁ θ₂ y =
      Real.exp (2 * α * y) * (2 * (1 - y) ^ (θ₂ - 1)) * y ^ (θ₁ - 1) := by
  simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
    mul_assoc, mul_comm, mul_left_comm]

private theorem wrightFisher_left_scale_factor_eq (α θ₁ θ₂ x : ℝ) :
    selectionMutationScaleDensity α θ₁ θ₂ x =
      Real.exp (-2 * α * x) * (1 - x) ^ (-θ₂) * x ^ (-θ₁) := by
  simp only [selectionMutationScaleDensity, mutationScaleDensity,
    mul_assoc, mul_comm, mul_left_comm]

private theorem wrightFisher_left_continuous_speed_on
    (α θ₁ θ₂ : ℝ) {s : Set ℝ} (h0 : ∀ x ∈ s, 0 < x) (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (selectionMutationSpeedDensity α θ₁ θ₂) s := by
  have hF : ContinuousOn _ s :=
    wrightFisher_left_continuous_speedFactor_on α θ₂ h1
  have hpow : ContinuousOn (fun x : ℝ => x ^ (θ₁ - 1)) s :=
    ContinuousOn.rpow_const continuousOn_id
      (fun x hx => Or.inl (ne_of_gt (h0 x hx)))
  exact (hF.mul hpow).congr
    (fun y hy => wrightFisher_left_speed_factor_eq α θ₁ θ₂ y)

private theorem wrightFisher_left_continuous_scale_on
    (α θ₁ θ₂ : ℝ) {s : Set ℝ} (h0 : ∀ x ∈ s, 0 < x) (h1 : ∀ x ∈ s, x < 1) :
    ContinuousOn (selectionMutationScaleDensity α θ₁ θ₂) s := by
  have hF : ContinuousOn _ s :=
    wrightFisher_left_continuous_scaleFactor_on α θ₂ h1
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-θ₁)) s :=
    ContinuousOn.rpow_const continuousOn_id
      (fun x hx => Or.inl (ne_of_gt (h0 x hx)))
  exact (hF.mul hpow).congr
    (fun y hy => wrightFisher_left_scale_factor_eq α θ₁ θ₂ y)

private theorem wrightFisher_left_factor_bound (f : ℝ → ℝ) (c : ℝ)
    (hc0 : 0 < c) (hcont : ContinuousOn f (Icc 0 c))
    (hpos : ∀ x ∈ Icc 0 c, 0 < f x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ y ∈ Ioo (0 : ℝ) c, m ≤ f y ∧ f y ≤ M := by
  have hcompact : IsCompact (Icc (0 : ℝ) c) := isCompact_Icc
  have hne : (Icc (0 : ℝ) c).Nonempty := ⟨0, mem_Icc.mpr ⟨le_rfl, le_of_lt hc0⟩⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨x0, hx0mem, hx0min⟩ := IsCompact.exists_isMinOn hcompact hne hcont
  have hmpos : 0 < f x0 := hpos x0 hx0mem
  refine ⟨f x0, M, hmpos, fun y hy => ?_⟩
  have hyIcc : y ∈ Icc (0 : ℝ) c := mem_Icc.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hleL : f x0 ≤ f y := (isMinOn_iff.mp hx0min) y hyIcc
  have hleU : f y ≤ M := by
    have hnorm : ‖f y‖ ≤ M := hM y hyIcc
    have hle : f y ≤ ‖f y‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact le_trans hle hnorm
  exact ⟨hleL, hleU⟩

private theorem wrightFisher_left_speed_bound (α θ₁ θ₂ c : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ m M : ℝ, 0 < m ∧ ∀ y ∈ Ioo (0 : ℝ) c,
      m * y ^ (θ₁ - 1) ≤ selectionMutationSpeedDensity α θ₁ θ₂ y ∧
        selectionMutationSpeedDensity α θ₁ θ₂ y ≤ M * y ^ (θ₁ - 1) := by
  obtain ⟨hc0, hc1⟩ := hc
  have hcont : ContinuousOn _ (Icc 0 c) :=
    wrightFisher_left_continuous_speedFactor_on α θ₂
      (fun y hy => lt_of_le_of_lt hy.2 hc1)
  have hpos : ∀ y ∈ Icc (0 : ℝ) c,
      0 < Real.exp (2 * α * y) * (2 * (1 - y) ^ (θ₂ - 1)) := by
    intro y hy
    have h1y : (0 : ℝ) < 1 - y := by linarith [hy.2, hc1]
    positivity
  obtain ⟨m, M, hmpos, hbd⟩ :=
    wrightFisher_left_factor_bound _ c hc0 hcont hpos
  refine ⟨m, M, hmpos, fun y hy => ?_⟩
  have hrpow_nn : 0 ≤ y ^ (θ₁ - 1) := Real.rpow_nonneg (le_of_lt hy.1) _
  have heq := wrightFisher_left_speed_factor_eq α θ₁ θ₂ y
  obtain ⟨hlo, hhi⟩ := hbd y hy
  constructor
  · rw [heq]; exact mul_le_mul_of_nonneg_right hlo hrpow_nn
  · rw [heq]; exact mul_le_mul_of_nonneg_right hhi hrpow_nn

private theorem wrightFisher_left_scale_bound (α θ₁ θ₂ c : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ Ioo (0 : ℝ) c,
      m * x ^ (-θ₁) ≤ selectionMutationScaleDensity α θ₁ θ₂ x ∧
        selectionMutationScaleDensity α θ₁ θ₂ x ≤ M * x ^ (-θ₁) := by
  obtain ⟨hc0, hc1⟩ := hc
  have hcont : ContinuousOn _ (Icc 0 c) :=
    wrightFisher_left_continuous_scaleFactor_on α θ₂
      (fun x hx => lt_of_le_of_lt hx.2 hc1)
  have hpos : ∀ x ∈ Icc (0 : ℝ) c,
      0 < Real.exp (-2 * α * x) * (1 - x) ^ (-θ₂) := by
    intro x hx
    have h1x : (0 : ℝ) < 1 - x := by linarith [hx.2, hc1]
    positivity
  obtain ⟨m, M, hmpos, hbd⟩ :=
    wrightFisher_left_factor_bound _ c hc0 hcont hpos
  refine ⟨m, M, hmpos, fun x hx => ?_⟩
  have hrpow_nn : 0 ≤ x ^ (-θ₁) := Real.rpow_nonneg (le_of_lt hx.1) _
  have heq := wrightFisher_left_scale_factor_eq α θ₁ θ₂ x
  obtain ⟨hlo, hhi⟩ := hbd x hx
  constructor
  · rw [heq]; exact mul_le_mul_of_nonneg_right hlo hrpow_nn
  · rw [heq]; exact mul_le_mul_of_nonneg_right hhi hrpow_nn

private theorem wrightFisher_left_inner_ge (Inner : ℝ → ℝ) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hInner_nn : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ Inner y)
    (hInner_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < Inner y)
    (hInner_cont : ∀ d : ℝ, 0 < d → d < c → ContinuousOn Inner (Icc d c)) :
    (∀ x ∈ Ioo (0 : ℝ) (c / 2), (∫ y in (c / 2)..c, Inner y) ≤
      (∫ y in x..c, Inner y) ∧ 0 ≤ ∫ y in x..c, Inner y) ∧
      0 < ∫ y in (c / 2)..c, Inner y := by
  have hc2pos : 0 < c / 2 := by linarith
  have hc2lt : c / 2 < c := by linarith
  have hcont_c2 : ContinuousOn Inner (Icc (c / 2) c) :=
    hInner_cont (c / 2) hc2pos hc2lt
  have hInt_c2 : IntervalIntegrable _ volume (c / 2) c :=
    hcont_c2.intervalIntegrable_of_Icc hc2lt.le
  have hP : 0 < ∫ y in (c / 2)..c, Inner y :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hInt_c2
      (fun x hx => hInner_pos x ⟨lt_trans hc2pos hx.1, lt_trans hx.2 hc1⟩) hc2lt
  refine ⟨fun x hx => ?_, hP⟩
  have hx0 : 0 < x := hx.1
  have hxc : x < c := lt_trans hx.2 hc2lt
  have hInt_xc : IntervalIntegrable _ volume x c :=
    (hInner_cont x hx0 hxc).intervalIntegrable_of_Icc hxc.le
  have hf : 0 ≤ᵐ[volume.restrict (Ioc x c)] Inner := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
    exact hInner_nn y ⟨lt_trans hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩
  have hge : (∫ y in (c / 2)..c, Inner y) ≤ ∫ y in x..c, Inner y :=
    intervalIntegral.integral_mono_interval (le_of_lt hx.2) hc2lt.le le_rfl hf
      hInt_xc
  have hnn : 0 ≤ ∫ y in x..c, Inner y :=
    intervalIntegral.integral_nonneg hxc.le
      (fun y hy => hInner_nn y ⟨lt_of_lt_of_le hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩)
  exact ⟨hge, hnn⟩

private theorem wrightFisher_left_cancel (α θ₁ θ₂ c : ℝ) (hc0 : 0 < c)
    (hc1 : c < 1) :
    (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) = 1 := by
  have h1cpos : 0 < 1 - c := by linarith
  have hr1 : c ^ (-θ₁) * c ^ θ₁ = 1 := by
    rw [← Real.rpow_add hc0, show (-θ₁ : ℝ) + θ₁ = 0 by ring, Real.rpow_zero]
  have hr2 : (1 - c) ^ (-θ₂) * (1 - c) ^ θ₂ = 1 := by
    rw [← Real.rpow_add h1cpos, show (-θ₂ : ℝ) + θ₂ = 0 by ring, Real.rpow_zero]
  have he : Real.exp (-2 * α * c) * Real.exp (2 * α * c) = 1 := by
    rw [← Real.exp_add, show -2 * α * c + 2 * α * c = 0 by ring, Real.exp_zero]
  have hring : (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
          (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) =
        (c ^ (-θ₁) * c ^ θ₁) * ((1 - c) ^ (-θ₂) * (1 - c) ^ θ₂) *
          (Real.exp (-2 * α * c) * Real.exp (2 * α * c)) := by
    ring
  rw [hring, hr1, hr2, he, mul_one, mul_one]

private theorem wrightFisher_left_Feller_mp
    {Inner Outer : ℝ → ℝ} {P m r : ℝ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hP : 0 < P) (hm : 0 < m) (hr : r ≤ -1)
    (hInner : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      P ≤ (∫ y in x..c, Inner y) ∧ 0 ≤ ∫ y in x..c, Inner y)
    (hOuter : ∀ x ∈ Ioo (0 : ℝ) (c / 2), m * x ^ r ≤ Outer x ∧ 0 ≤ Outer x)
    (hInt : IntegrableOn (fun x => (∫ y in x..c, Inner y) * Outer x)
      (Ioo (0 : ℝ) (c / 2)) volume) :
    False := by
  have hrpow_nint : ¬ IntegrableOn (fun x => x ^ r) (Ioo 0 (c / 2)) volume :=
    mt (intervalIntegral.integrableOn_Ioo_rpow_iff (by linarith)).mp
      (not_lt.mpr hr)
  have hcont_pow : ContinuousOn (fun x : ℝ => x ^ r) (Ioo 0 (c / 2)) :=
    ContinuousOn.rpow_const continuousOn_id
      (fun x hx => Or.inl (ne_of_gt hx.1))
  have hKpos : 0 < P * m := mul_pos hP hm
  have hle : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))),
      ((P * m) * x ^ r) ≤ (∫ y in x..c, Inner y) * Outer x := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have heq0 : (P * m) * x ^ r = P * (m * x ^ r) := by ring
    calc (P * m) * x ^ r = P * (m * x ^ r) := heq0
      _ ≤ P * Outer x :=
        mul_le_mul_of_nonneg_left (hOuter x hx).1 (le_of_lt hP)
      _ ≤ (∫ y in x..c, Inner y) * Outer x :=
        mul_le_mul_of_nonneg_right (hInner x hx).1 (hOuter x hx).2
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))), 0 ≤ x ^ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg (le_of_lt hx.1) _
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ r)
      (volume.restrict (Ioo 0 (c / 2))) :=
    hcont_pow.aestronglyMeasurable measurableSet_Ioo
  have hKne : P * m ≠ 0 := ne_of_gt hKpos
  have hKinv_nn : 0 ≤ (P * m)⁻¹ := inv_nonneg.mpr (le_of_lt hKpos)
  have hFavsmul : Integrable _ (volume.restrict (Ioo 0 (c / 2))) :=
    hInt.const_mul (P * m)⁻¹
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioo 0 (c / 2))),
      ‖x ^ r‖ ≤ (P * m)⁻¹ * ((∫ y in x..c, Inner y) * Outer x) := by
    filter_upwards [hle, hnn] with x hx hnx
    rw [Real.norm_eq_abs, abs_of_nonneg hnx]
    have h2 : (P * m)⁻¹ * ((P * m) * x ^ r) = x ^ r := by
      rw [← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
    calc x ^ r = (P * m)⁻¹ * ((P * m) * x ^ r) := h2.symm
      _ ≤ (P * m)⁻¹ * ((∫ y in x..c, Inner y) * Outer x) :=
        mul_le_mul_of_nonneg_left hx hKinv_nn
  have hint : IntegrableOn _ (Ioo 0 (c / 2)) volume :=
    hFavsmul.mono' hmeas hbound
  exact hrpow_nint hint

private theorem wrightFisher_left_regular (I O : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c)
    (hI : ContinuousOn I (Icc (c / 2) c)) (hO : ContinuousOn O (Icc (c / 2) c)) :
    IntegrableOn (fun x => (∫ y in x..c, I y) * O x) (Ico (c / 2) c) volume := by
  have hc2le : c / 2 ≤ c := by linarith
  have hI' : IntegrableOn I (uIcc (c / 2) c) volume := by
    rw [uIcc_of_le hc2le]; exact hI.integrableOn_Icc
  have hP : ContinuousOn (fun x => ∫ y in x..c, I y) (Icc (c / 2) c) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left hI'
    rwa [uIcc_of_le hc2le] at h
  exact (hP.mul hO).integrableOn_Icc.mono_set Ico_subset_Icc_self

private theorem wrightFisher_left_singular_sufficiency
    (Inner Outer : ℝ → ℝ) (c p q M₁ M₂ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hpq : p + q + 1 = 0) (hpneg : p < 0)
    (hInner_bound : ∀ y ∈ Ioo (0 : ℝ) c, Inner y ≤ M₁ * y ^ p)
    (hOuter_bound : ∀ x ∈ Ioo (0 : ℝ) (c / 2), Outer x ≤ M₂ * x ^ q)
    (hInner_pos : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < Inner y)
    (hOuter_pos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < Outer x)
    (hInner_cont : ∀ d : ℝ, 0 < d → d < c → ContinuousOn Inner (Icc d c))
    (hOuter_cont : ContinuousOn Outer (Ioo (0 : ℝ) (c / 2))) :
    IntegrableOn (fun x => (∫ y in x..c, Inner y) * Outer x)
      (Ioo (0 : ℝ) (c / 2)) volume := by
  have hc2pos : 0 < c / 2 := by linarith
  have hc2lt : c / 2 < c := by linarith
  have hM₁ : 0 < M₁ := by
    have hI := hInner_bound (c / 2) ⟨hc2pos, hc2lt⟩
    have hP := hInner_pos (c / 2) ⟨hc2pos, by linarith⟩
    have hrp : 0 < (c / 2) ^ p := Real.rpow_pos_of_pos hc2pos p
    by_contra hcon
    push Not at hcon
    have hle := mul_nonpos_of_nonpos_of_nonneg hcon hrp.le
    linarith
  have hM₂ : 0 < M₂ := by
    have hO := hOuter_bound (c / 4) ⟨by linarith, by linarith⟩
    have hP := hOuter_pos (c / 4) ⟨by linarith, by linarith⟩
    have hrp : 0 < (c / 4) ^ q := Real.rpow_pos_of_pos (by linarith) q
    by_contra hcon
    push Not at hcon
    have hle := mul_nonpos_of_nonpos_of_nonneg hcon hrp.le
    linarith
  have hC₂_nn : 0 ≤ ∫ y in (c / 2)..c, Inner y :=
    intervalIntegral.integral_nonneg hc2lt.le (fun y hy =>
      le_of_lt (hInner_pos y ⟨lt_of_lt_of_le hc2pos hy.1,
        lt_of_le_of_lt hy.2 hc1⟩))
  have hsplit : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      (∫ y in x..c, Inner y) =
        (∫ y in x..(c / 2), Inner y) + ∫ y in (c / 2)..c, Inner y := by
    intro x hx
    have hxc : x < c := lt_trans hx.2 hc2lt
    have hcont : ContinuousOn Inner (Icc x c) := hInner_cont x hx.1 hxc
    have hxc2 : IntervalIntegrable Inner volume x (c / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc hx.2.le
        (hcont.mono (fun y hy => ⟨hy.1, le_trans hy.2 hc2lt.le⟩))
    have hc2c : IntervalIntegrable Inner volume (c / 2) c :=
      ContinuousOn.intervalIntegrable_of_Icc hc2lt.le
        (hcont.mono (fun y hy => ⟨le_trans hx.2.le hy.1, hy.2⟩))
    exact (intervalIntegral.integral_add_adjacent_intervals hxc2 hc2c).symm
  have hJ : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      (∫ y in x..(c / 2), Inner y) ≤ M₁ * ∫ y in x..(c / 2), y ^ p := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := lt_trans hx.2 hc2lt
    have hcont : ContinuousOn Inner (Icc x c) := hInner_cont x hx0 hxc
    have hIx : IntervalIntegrable Inner volume x (c / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc hx.2.le
        (hcont.mono (fun y hy => ⟨hy.1, le_trans hy.2 hc2lt.le⟩))
    have hpow : ContinuousOn (fun y : ℝ => y ^ p) (Icc x (c / 2)) :=
      ContinuousOn.rpow_const continuousOn_id
        (fun y hy => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 hy.1)))
    have hIp : IntervalIntegrable (fun y : ℝ => M₁ * y ^ p) volume x (c / 2) :=
      ContinuousOn.intervalIntegrable_of_Icc hx.2.le
        (continuousOn_const.mul hpow)
    have hmono := intervalIntegral.integral_mono_on hx.2.le hIx hIp
      (fun y hy => hInner_bound y ⟨lt_of_lt_of_le hx0 hy.1,
        lt_of_le_of_lt hy.2 hc2lt⟩)
    rwa [intervalIntegral.integral_const_mul M₁ (fun y : ℝ => y ^ p)] at hmono
  have hFcont : ContinuousOn (fun x => (∫ y in x..c, Inner y) * Outer x)
      (Ioo (0 : ℝ) (c / 2)) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := lt_trans hx.2 hc2lt
    have hd0 : 0 < x / 2 := by linarith
    have hdx : x / 2 < x := by linarith
    have hdc : x / 2 < c := lt_trans hdx hxc
    have hIc : ContinuousOn Inner (Icc (x / 2) c) :=
      hInner_cont (x / 2) hd0 hdc
    have hIu : IntegrableOn Inner (uIcc (x / 2) c) volume := by
      rw [uIcc_of_le hdc.le]; exact hIc.integrableOn_Icc
    have hP : ContinuousOn (fun x => ∫ y in x..c, Inner y) (Icc (x / 2) c) := by
      have h := intervalIntegral.continuousOn_primitive_interval_left hIu
      rwa [uIcc_of_le hdc.le] at h
    have hmem : Icc (x / 2) c ∈ 𝓝 x :=
      Filter.mem_of_superset (Ioo_mem_nhds hdx hxc) Ioo_subset_Icc_self
    have hprim : ContinuousAt (fun x => ∫ y in x..c, Inner y) x :=
      hP.continuousAt hmem
    have hout : ContinuousAt Outer x :=
      hOuter_cont.continuousAt (IsOpen.mem_nhds isOpen_Ioo hx)
    exact (hprim.mul hout).continuousWithinAt
  have hInner_nn : ∀ x ∈ Ioo (0 : ℝ) (c / 2), 0 ≤ ∫ y in x..c, Inner y := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := lt_trans hx.2 hc2lt
    exact intervalIntegral.integral_nonneg hxc.le (fun y hy =>
      le_of_lt (hInner_pos y ⟨lt_of_lt_of_le hx0 hy.1,
        lt_of_le_of_lt hy.2 hc1⟩))
  have hOuter_nn : ∀ x ∈ Ioo (0 : ℝ) (c / 2), 0 ≤ Outer x :=
    fun x hx => le_of_lt
      (hOuter_pos x ⟨hx.1, lt_trans (lt_trans hx.2 hc2lt) hc1⟩)
  have hFnn : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
      0 ≤ (∫ y in x..c, Inner y) * Outer x :=
    fun x hx => mul_nonneg (hInner_nn x hx) (hOuter_nn x hx)
  have hprod : ∀ a b U V : ℝ, a ≤ U → b ≤ V → 0 ≤ b → 0 ≤ U → a * b ≤ U * V :=
    fun a b U V h1 h2 hb hU => le_trans (mul_le_mul_of_nonneg_right h1 hb)
      (mul_le_mul_of_nonneg_left h2 hU)
  have hFmeas : AEStronglyMeasurable
      (fun x => (∫ y in x..c, Inner y) * Outer x)
      (volume.restrict (Ioo (0 : ℝ) (c / 2))) :=
    hFcont.aestronglyMeasurable measurableSet_Ioo
  have hq_int : IntegrableOn (fun x : ℝ => x ^ q) (Ioo 0 (c / 2)) volume :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hc2pos).mpr (by linarith)
  have hfin : volume (Ioo (0 : ℝ) (c / 2)) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ne_of_lt ENNReal.ofReal_lt_top
  rcases lt_trichotomy p (-1) with hlt | heq | hgt
  · have hDpos : 0 < -(p + 1) := by linarith
    have hne : p ≠ -1 := ne_of_lt hlt
    have hne1 : p + 1 ≠ 0 := ne_of_lt (by linarith)
    have hne2 : -(p + 1) ≠ 0 := ne_of_gt hDpos
    have hpow_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..(c / 2), y ^ p) ≤ x ^ (p + 1) / (-(p + 1)) := by
      intro x hx
      have h0mem : (0 : ℝ) ∉ uIcc x (c / 2) := by
        rw [uIcc_of_le hx.2.le]
        intro hcon
        have hx0' : x ≤ 0 := (mem_Icc.mp hcon).1
        linarith [hx.1]
      rw [integral_rpow (Or.inr ⟨hne, h0mem⟩)]
      have hflip : ((c / 2) ^ (p + 1) - x ^ (p + 1)) / (p + 1) =
          (x ^ (p + 1) - (c / 2) ^ (p + 1)) / (-(p + 1)) := by
        field_simp
        ring
      rw [hflip]
      have hnum : x ^ (p + 1) - (c / 2) ^ (p + 1) ≤ x ^ (p + 1) := by
        have hnn : 0 ≤ (c / 2) ^ (p + 1) := Real.rpow_nonneg hc2pos.le _
        linarith
      exact div_le_div_of_nonneg_right hnum hDpos.le
    have hInner_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..c, Inner y) ≤ M₁ * (x ^ (p + 1) / (-(p + 1))) +
          ∫ y in (c / 2)..c, Inner y := by
      intro x hx
      rw [hsplit x hx]
      have h1 := mul_le_mul_of_nonneg_left (hpow_le x hx) hM₁.le
      linarith [hJ x hx]
    have hpt : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ M₁ * M₂ / (-(p + 1)) +
          (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hrw : x ^ (p + 1) * x ^ q = 1 := by
        rw [← Real.rpow_add hx0, show (p + 1) + q = 0 by linarith,
          Real.rpow_zero]
      have hU_nn : 0 ≤ M₁ * (x ^ (p + 1) / (-(p + 1))) +
          (∫ y in (c / 2)..c, Inner y) :=
        add_nonneg (mul_nonneg hM₁.le
          (div_pos (Real.rpow_pos_of_pos hx0 _) hDpos).le) hC₂_nn
      have hmul : (∫ y in x..c, Inner y) * Outer x ≤
          (M₁ * (x ^ (p + 1) / (-(p + 1))) +
            (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) :=
        hprod _ _ _ _ (hInner_le x hx) (hOuter_bound x hx) (hOuter_nn x hx) hU_nn
      have e1 : M₁ * (x ^ (p + 1) / (-(p + 1))) * (M₂ * x ^ q) =
          M₁ * M₂ / (-(p + 1)) * (x ^ (p + 1) * x ^ q) := by ring
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x hx)]
      calc (∫ y in x..c, Inner y) * Outer x
          ≤ (M₁ * (x ^ (p + 1) / (-(p + 1))) +
              (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) := hmul
        _ = M₁ * M₂ / (-(p + 1)) +
            (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q := by
            rw [add_mul, e1, hrw, mul_one]
            ring
    have hg : IntegrableOn (fun x => M₁ * M₂ / (-(p + 1)) +
        (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q)
        (Ioo (0 : ℝ) (c / 2)) volume := by
      have h1 : IntegrableOn (fun _ => M₁ * M₂ / (-(p + 1)))
          (Ioo (0 : ℝ) (c / 2)) volume := integrableOn_const hfin
      have h2 : IntegrableOn
          (fun x => (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q)
          (Ioo (0 : ℝ) (c / 2)) volume :=
        hq_int.const_mul ((∫ y in (c / 2)..c, Inner y) * M₂)
      exact h1.add h2
    have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) (c / 2))),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ M₁ * M₂ / (-(p + 1)) +
          (∫ y in (c / 2)..c, Inner y) * M₂ * x ^ q := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    exact hg.mono' hFmeas hbound
  · have hq0 : q = 0 := by linarith
    have hs_int : IntegrableOn (fun x : ℝ => x ^ (-1 / 2 : ℝ))
        (Ioo 0 (c / 2)) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hc2pos).mpr (by linarith)
    have hlog_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        -Real.log x ≤ 2 * x ^ (-1 / 2 : ℝ) := by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hspos : 0 < x ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
      have hrpow : Real.log (x ^ (-1 / 2 : ℝ)) = (-1 / 2 : ℝ) * Real.log x :=
        Real.log_rpow hx0 _
      have hle : Real.log (x ^ (-1 / 2 : ℝ)) ≤ x ^ (-1 / 2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hspos
      have hlogeq : -Real.log x = 2 * Real.log (x ^ (-1 / 2 : ℝ)) := by
        rw [hrpow]; ring
      rw [hlogeq]
      linarith
    have hInner_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..c, Inner y) ≤ M₁ * (Real.log (c / 2) - Real.log x) +
          (∫ y in (c / 2)..c, Inner y) := by
      intro x hx
      rw [hsplit x hx]
      have h1 := hJ x hx
      have hftc : (∫ y in x..(c / 2), y ^ p) =
          Real.log (c / 2) - Real.log x := by
        rw [heq]
        simp only [Real.rpow_neg_one]
        rw [integral_inv_of_pos hx.1 hc2pos,
          Real.log_div (ne_of_gt hc2pos) (ne_of_gt hx.1)]
      rw [hftc] at h1
      linarith
    have hOuter_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2), Outer x ≤ M₂ := by
      intro x hx
      have h := hOuter_bound x hx
      rw [hq0, Real.rpow_zero, mul_one] at h
      exact h
    have hL : Real.log (c / 2) ≤ 0 :=
      le_of_lt (Real.log_neg hc2pos (by linarith))
    have hpt : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) +
          (∫ y in (c / 2)..c, Inner y) * M₂ := by
      intro x hx
      have hlog := hlog_le x hx
      have hU_nn : 0 ≤ M₁ * (Real.log (c / 2) - Real.log x) +
          (∫ y in (c / 2)..c, Inner y) :=
        add_nonneg (mul_nonneg hM₁.le
          (sub_pos.mpr (Real.log_lt_log hx.1 hx.2)).le) hC₂_nn
      have hmul : (∫ y in x..c, Inner y) * Outer x ≤
          (M₁ * (Real.log (c / 2) - Real.log x) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ :=
        hprod _ _ _ _ (hInner_le x hx) (hOuter_le x hx) (hOuter_nn x hx) hU_nn
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x hx)]
      have hexpand : (M₁ * (Real.log (c / 2) - Real.log x) +
          (∫ y in (c / 2)..c, Inner y)) * M₂ =
          M₁ * M₂ * (Real.log (c / 2) - Real.log x) +
            (∫ y in (c / 2)..c, Inner y) * M₂ := by ring
      rw [hexpand] at hmul
      have hLe : M₁ * M₂ * (Real.log (c / 2) - Real.log x) ≤
          2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) := by
        have hMM : 0 ≤ M₁ * M₂ := mul_nonneg hM₁.le hM₂.le
        have hsum : Real.log (c / 2) - Real.log x ≤
            2 * x ^ (-1 / 2 : ℝ) := by
          linarith
        calc M₁ * M₂ * (Real.log (c / 2) - Real.log x)
            = (M₁ * M₂) * (Real.log (c / 2) - Real.log x) := by ring
          _ ≤ (M₁ * M₂) * (2 * x ^ (-1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hsum hMM
          _ = 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) := by ring
      linarith [hmul, hLe]
    have hg : IntegrableOn (fun x => 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) +
        (∫ y in (c / 2)..c, Inner y) * M₂)
        (Ioo (0 : ℝ) (c / 2)) volume := by
      have h1 : IntegrableOn (fun _ => (∫ y in (c / 2)..c, Inner y) * M₂)
          (Ioo (0 : ℝ) (c / 2)) volume := integrableOn_const hfin
      have h2 : IntegrableOn (fun x => 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ))
          (Ioo (0 : ℝ) (c / 2)) volume :=
        hs_int.const_mul (2 * M₁ * M₂)
      exact h2.add h1
    have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) (c / 2))),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤ 2 * M₁ * M₂ * x ^ (-1 / 2 : ℝ) +
          (∫ y in (c / 2)..c, Inner y) * M₂ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    exact hg.mono' hFmeas hbound
  · have hPpos : 0 < p + 1 := by linarith
    have hpow_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..(c / 2), y ^ p) ≤ (c / 2) ^ (p + 1) / (p + 1) := by
      intro x hx
      rw [integral_rpow (Or.inl hgt)]
      have hnum : (c / 2) ^ (p + 1) - x ^ (p + 1) ≤ (c / 2) ^ (p + 1) := by
        have hnn : 0 ≤ x ^ (p + 1) := Real.rpow_nonneg hx.1.le _
        linarith
      exact div_le_div_of_nonneg_right hnum hPpos.le
    have hK1 : 0 < M₁ * ((c / 2) ^ (p + 1) / (p + 1)) :=
      mul_pos hM₁ (div_pos (Real.rpow_pos_of_pos hc2pos _) hPpos)
    have hInner_le : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        (∫ y in x..c, Inner y) ≤ M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
          (∫ y in (c / 2)..c, Inner y) := by
      intro x hx
      rw [hsplit x hx]
      have h1 := mul_le_mul_of_nonneg_left (hpow_le x hx) hM₁.le
      linarith [hJ x hx]
    have hK_nn : 0 ≤ M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
        (∫ y in (c / 2)..c, Inner y) := add_nonneg hK1.le hC₂_nn
    have hpt : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q := by
      intro x hx
      have hmul : (∫ y in x..c, Inner y) * Outer x ≤
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) :=
        hprod _ _ _ _ (hInner_le x hx) (hOuter_bound x hx) (hOuter_nn x hx) hK_nn
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn x hx)]
      have heq : (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
          (∫ y in (c / 2)..c, Inner y)) * (M₂ * x ^ q) =
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q := by ring
      rwa [heq] at hmul
    have hg : IntegrableOn (fun x => (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
        (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q)
        (Ioo (0 : ℝ) (c / 2)) volume :=
      hq_int.const_mul ((M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
        (∫ y in (c / 2)..c, Inner y)) * M₂)
    have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) (c / 2))),
        ‖(∫ y in x..c, Inner y) * Outer x‖ ≤
          (M₁ * ((c / 2) ^ (p + 1) / (p + 1)) +
            (∫ y in (c / 2)..c, Inner y)) * M₂ * x ^ q := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    exact hg.mono' hFmeas hbound

private theorem integrableOn_wrightFisher_left_sigma_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔ θ₁ < 1 := by
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  have hc2lt : c / 2 < c := by linarith
  let G : ℝ → ℝ := fun x =>
    (∫ y in x..c, selectionMutationSpeedDensity α θ₁ θ₂ y) *
      selectionMutationScaleDensity α θ₁ θ₂ x
  have hEq : Set.EqOn (fun x => (∫ y in x..c, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) G (Ioo 0 c) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := hx.2
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, lt_trans hxc hc1⟩
    have hinner : (∫ y in x..c, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) =
        (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
          (∫ y in x..c, selectionMutationSpeedDensity α θ₁ θ₂ y) := by
      have hpoint : ∀ y ∈ Ioc x c, speedDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y =
          (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
            selectionMutationSpeedDensity α θ₁ θ₂ y :=
        fun y hy => speedDensityFrom_selectionMutation α θ₁ θ₂ c y hc
          ⟨lt_trans hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩
      have hIoc : uIoc x c = Ioc x c := uIoc_of_le (le_of_lt hxc)
      have hcongr : (∫ y in x..c, speedDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y) =
          (∫ y in x..c, (c ^ (-θ₁) * (1 - c) ^ (-θ₂) *
            Real.exp (-2 * α * c)) *
            selectionMutationSpeedDensity α θ₁ θ₂ y) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [hIoc]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
        exact hpoint y hy
      rw [hcongr, intervalIntegral.integral_const_mul]
    have houter : scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
          selectionMutationScaleDensity α θ₁ θ₂ x :=
      scaleDensityFrom_selectionMutation α θ₁ θ₂ c x hc hx01
    have hcancel := wrightFisher_left_cancel α θ₁ θ₂ c hc0 hc1
    have hgoal : (∫ y in x..c, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (∫ y in x..c, selectionMutationSpeedDensity α θ₁ θ₂ y) *
          selectionMutationScaleDensity α θ₁ θ₂ x := by
      rw [hinner, houter, mul_mul_mul_comm, hcancel, one_mul]
    exact hgoal
  have hFiff : IntegrableOn (fun x => (∫ y in x..c, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔
      IntegrableOn G (Ioo 0 c) volume :=
    ⟨fun h => h.congr_fun hEq measurableSet_Ioo,
      fun h => h.congr_fun (fun x hx => (hEq hx).symm) measurableSet_Ioo⟩
  rw [hFiff]
  have hsplit := wrightFisher_left_split G c hc0
  have hspeed_fun : ∀ d : ℝ, 0 < d → d < c →
      ContinuousOn (selectionMutationSpeedDensity α θ₁ θ₂) (Icc d c) :=
    fun d hd0 _hdc => wrightFisher_left_continuous_speed_on α θ₁ θ₂
      (fun y hy => lt_of_lt_of_le hd0 hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
  obtain ⟨m₂, _, hm₂, hscale⟩ := wrightFisher_left_scale_bound α θ₁ θ₂ c hc
  have hspeed_nn : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ selectionMutationSpeedDensity α θ₁ θ₂ y :=
    fun y hy => le_of_lt (wrightFisher_left_speed_pos α θ₁ θ₂ y hy)
  have hspeed_pos' : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < selectionMutationSpeedDensity α θ₁ θ₂ y :=
    fun y hy => wrightFisher_left_speed_pos α θ₁ θ₂ y hy
  have hInner_full := wrightFisher_left_inner_ge _ _ hc0 hc1 hspeed_nn hspeed_pos' hspeed_fun
  have hsing : IntegrableOn G (Ioo 0 (c / 2)) volume ↔ θ₁ < 1 := by
    constructor
    · intro hInt
      by_contra hcon
      have hle : 1 ≤ θ₁ := le_of_not_gt hcon
      have hr : -θ₁ ≤ -1 := by linarith
      have hOuter : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
          m₂ * x ^ (-θ₁) ≤ selectionMutationScaleDensity α θ₁ θ₂ x ∧
            0 ≤ selectionMutationScaleDensity α θ₁ θ₂ x := by
        intro x hx
        exact ⟨(hscale x ⟨hx.1, lt_trans hx.2 hc2lt⟩).1,
          le_of_lt (wrightFisher_left_scale_pos α θ₁ θ₂ x
            ⟨hx.1, lt_trans (lt_trans hx.2 hc2lt) hc1⟩)⟩
      have hfalse : False :=
        wrightFisher_left_Feller_mp hc0 hc1 hInner_full.2 hm₂ hr hInner_full.1
          hOuter hInt
      exact hfalse.elim
    · intro h
      obtain ⟨_, M₁, _, hspeed⟩ := wrightFisher_left_speed_bound α θ₁ θ₂ c hc
      exact wrightFisher_left_singular_sufficiency _ _ c (θ₁ - 1) (-θ₁) _ _
        hc0 hc1 (by ring) (by linarith) (fun y hy => (hspeed y hy).2)
        (fun x hx => (hscale x ⟨hx.1, lt_trans hx.2 hc2lt⟩).2)
        (fun y hy => wrightFisher_left_speed_pos α θ₁ θ₂ y hy)
        (fun x hx => wrightFisher_left_scale_pos α θ₁ θ₂ x hx) hspeed_fun
        (wrightFisher_left_continuous_scale_on α θ₁ θ₂ (fun y hy => hy.1)
          (fun y hy => lt_trans (lt_trans hy.2 hc2lt) hc1))
  rw [hsplit]
  constructor
  · intro h
    exact hsing.mp h.1
  · intro h
    refine ⟨hsing.mpr h, ?_⟩
    have hc2pos : 0 < c / 2 := by linarith
    have hO : ContinuousOn (selectionMutationScaleDensity α θ₁ θ₂) (Icc (c/2) c) :=
      wrightFisher_left_continuous_scale_on α θ₁ θ₂
        (fun y hy => lt_of_lt_of_le hc2pos hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
    exact wrightFisher_left_regular _ _ c hc0 (hspeed_fun (c/2) hc2pos hc2lt) hO

private theorem integrableOn_wrightFisher_left_scale_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔ 0 < θ₁ := by
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  have hc2lt : c / 2 < c := by linarith
  let G : ℝ → ℝ := fun x =>
    (∫ y in x..c, selectionMutationScaleDensity α θ₁ θ₂ y) *
      selectionMutationSpeedDensity α θ₁ θ₂ x
  have hEq : Set.EqOn (fun x => (∫ y in x..c, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) G (Ioo 0 c) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxc : x < c := hx.2
    have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, lt_trans hxc hc1⟩
    have hinner : (∫ y in x..c, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) =
        (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
          (∫ y in x..c, selectionMutationScaleDensity α θ₁ θ₂ y) := by
      have hpoint : ∀ y ∈ Ioc x c, scaleDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y =
          (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
            selectionMutationScaleDensity α θ₁ θ₂ y :=
        fun y hy => scaleDensityFrom_selectionMutation α θ₁ θ₂ c y hc
          ⟨lt_trans hx0 hy.1, lt_of_le_of_lt hy.2 hc1⟩
      have hIoc : uIoc x c = Ioc x c := uIoc_of_le (le_of_lt hxc)
      have hcongr : (∫ y in x..c, scaleDensityFrom
          (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
          (fun x => x * (1 - x)) c y) =
          (∫ y in x..c, (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
            selectionMutationScaleDensity α θ₁ θ₂ y) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [hIoc]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
        exact hpoint y hy
      rw [hcongr, intervalIntegral.integral_const_mul]
    have houter : speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
          selectionMutationSpeedDensity α θ₁ θ₂ x :=
      speedDensityFrom_selectionMutation α θ₁ θ₂ c x hc hx01
    have hcancel := wrightFisher_left_cancel α θ₁ θ₂ c hc0 hc1
    have hgoal : (∫ y in x..c, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x =
        (∫ y in x..c, selectionMutationScaleDensity α θ₁ θ₂ y) *
          selectionMutationSpeedDensity α θ₁ θ₂ x := by
      rw [hinner, houter, mul_mul_mul_comm]
      have hcancel' : (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
          (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) = 1 := by
        rw [mul_comm]; exact hcancel
      rw [hcancel', one_mul]
    exact hgoal
  have hFiff : IntegrableOn (fun x => (∫ y in x..c, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo 0 c) volume ↔
      IntegrableOn G (Ioo 0 c) volume :=
    ⟨fun h => h.congr_fun hEq measurableSet_Ioo,
      fun h => h.congr_fun (fun x hx => (hEq hx).symm) measurableSet_Ioo⟩
  rw [hFiff]
  have hsplit := wrightFisher_left_split G c hc0
  have hscale_fun : ∀ d : ℝ, 0 < d → d < c →
      ContinuousOn (selectionMutationScaleDensity α θ₁ θ₂) (Icc d c) :=
    fun d hd0 _hdc => wrightFisher_left_continuous_scale_on α θ₁ θ₂
      (fun y hy => lt_of_lt_of_le hd0 hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
  obtain ⟨m₁, _, hm₁, hspeed⟩ := wrightFisher_left_speed_bound α θ₁ θ₂ c hc
  have hscale_nn : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ selectionMutationScaleDensity α θ₁ θ₂ y :=
    fun y hy => le_of_lt (wrightFisher_left_scale_pos α θ₁ θ₂ y hy)
  have hscale_pos' : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < selectionMutationScaleDensity α θ₁ θ₂ y :=
    fun y hy => wrightFisher_left_scale_pos α θ₁ θ₂ y hy
  have hInner_full := wrightFisher_left_inner_ge _ _ hc0 hc1 hscale_nn hscale_pos' hscale_fun
  have hsing : IntegrableOn G (Ioo 0 (c / 2)) volume ↔ 0 < θ₁ := by
    constructor
    · intro hInt
      by_contra hcon
      have hle : θ₁ ≤ 0 := le_of_not_gt hcon
      have hr : θ₁ - 1 ≤ -1 := by linarith
      have hOuter : ∀ x ∈ Ioo (0 : ℝ) (c / 2),
          m₁ * x ^ (θ₁ - 1) ≤ selectionMutationSpeedDensity α θ₁ θ₂ x ∧
            0 ≤ selectionMutationSpeedDensity α θ₁ θ₂ x := by
        intro x hx
        exact ⟨(hspeed x ⟨hx.1, lt_trans hx.2 hc2lt⟩).1,
          le_of_lt (wrightFisher_left_speed_pos α θ₁ θ₂ x
            ⟨hx.1, lt_trans (lt_trans hx.2 hc2lt) hc1⟩)⟩
      have hfalse : False :=
        wrightFisher_left_Feller_mp hc0 hc1 hInner_full.2 hm₁ hr hInner_full.1
          hOuter hInt
      exact hfalse.elim
    · intro h
      obtain ⟨_, M₂, _, hscale⟩ := wrightFisher_left_scale_bound α θ₁ θ₂ c hc
      exact wrightFisher_left_singular_sufficiency _ _ c (-θ₁) (θ₁ - 1) _ _
        hc0 hc1 (by ring) (by linarith) (fun y hy => (hscale y hy).2)
        (fun x hx => (hspeed x ⟨hx.1, lt_trans hx.2 hc2lt⟩).2)
        (fun y hy => wrightFisher_left_scale_pos α θ₁ θ₂ y hy)
        (fun x hx => wrightFisher_left_speed_pos α θ₁ θ₂ x hx) hscale_fun
        (wrightFisher_left_continuous_speed_on α θ₁ θ₂ (fun y hy => hy.1)
          (fun y hy => lt_trans (lt_trans hy.2 hc2lt) hc1))
  rw [hsplit]
  constructor
  · intro h
    exact hsing.mp h.1
  · intro h
    refine ⟨hsing.mpr h, ?_⟩
    have hc2pos : 0 < c / 2 := by linarith
    have hO : ContinuousOn (selectionMutationSpeedDensity α θ₁ θ₂) (Icc (c/2) c) :=
      wrightFisher_left_continuous_speed_on α θ₁ θ₂
        (fun y hy => lt_of_lt_of_le hc2pos hy.1) (fun y hy => lt_of_le_of_lt hy.2 hc1)
    exact wrightFisher_left_regular _ _ c hc0 (hscale_fun (c/2) hc2pos hc2lt) hO

private theorem wrightFisher_right_speed_reflect (α θ₁ θ₂ z : ℝ) :
    selectionMutationSpeedDensity α θ₁ θ₂ (1 - z) =
      Real.exp (2 * α) * selectionMutationSpeedDensity (-α) θ₂ θ₁ z := by
  simp only [selectionMutationSpeedDensity, mutationSpeedDensity]
  have h1 : (1 : ℝ) - (1 - z) = z := by ring
  have hexp : 2 * α * (1 - z) = 2 * α + 2 * (-α) * z := by ring
  rw [h1, hexp, Real.exp_add]
  ring
private theorem wrightFisher_right_scale_reflect (α θ₁ θ₂ z : ℝ) :
    selectionMutationScaleDensity α θ₁ θ₂ (1 - z) =
      Real.exp (-2 * α) * selectionMutationScaleDensity (-α) θ₂ θ₁ z := by
  simp only [selectionMutationScaleDensity, mutationScaleDensity]
  have h1 : (1 : ℝ) - (1 - z) = z := by ring
  have hexp : -2 * α * (1 - z) = -2 * α + -2 * (-α) * z := by ring
  rw [h1, hexp, Real.exp_add]
  ring
private theorem wrightFisher_right_const_cancel (u v p q r s : ℝ) (hu : 0 < u)
    (hv : 0 < v) (hrs : r + s = 0) :
    (u ^ (-p) * v ^ (-q) * Real.exp r) * (u ^ p * v ^ q * Real.exp s) = 1 := by
  have e1 : u ^ (-p) * u ^ p = 1 := by rw [← Real.rpow_add hu, neg_add_cancel, Real.rpow_zero]
  have e2 : v ^ (-q) * v ^ q = 1 := by rw [← Real.rpow_add hv, neg_add_cancel, Real.rpow_zero]
  have e3 : Real.exp r * Real.exp s = 1 := by rw [← Real.exp_add, hrs, Real.exp_zero]
  linear_combination e1 * (v ^ (-q) * Real.exp r * v ^ q * Real.exp s) +
    e2 * (Real.exp r * Real.exp s) + e3
private theorem wrightFisher_right_exp_cancel (α : ℝ) :
    Real.exp (2 * α) * Real.exp (-2 * α) = 1 := by
  have h : (2 : ℝ) * α + -2 * α = 0 := by ring
  rw [← Real.exp_add, h, Real.exp_zero]
private theorem wrightFisher_right_speedInner_explicit (α θ₁ θ₂ c a b : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    (∫ y in a..b, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) =
      (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        (∫ y in a..b, selectionMutationSpeedDensity α θ₁ θ₂ y) := by
  have heq : EqOn
      (fun y => speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y)
      (fun y => (c ^ (-θ₁) * (1 - c) ^ (-θ₂) * Real.exp (-2 * α * c)) *
        selectionMutationSpeedDensity α θ₁ θ₂ y)
      (uIcc a b) := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    obtain ⟨hay, hyb⟩ := mem_Icc.mp hy
    have hy01 : y ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha.1 hay, lt_of_le_of_lt hyb hb.2⟩
    exact speedDensityFrom_selectionMutation α θ₁ θ₂ c y hc hy01
  rw [intervalIntegral.integral_congr (μ := volume) heq, intervalIntegral.integral_const_mul]
private theorem wrightFisher_right_scaleInner_explicit (α θ₁ θ₂ c a b : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) :
    (∫ y in a..b, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) =
      (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
        (∫ y in a..b, selectionMutationScaleDensity α θ₁ θ₂ y) := by
  have heq : EqOn
      (fun y => scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y)
      (fun y => (c ^ θ₁ * (1 - c) ^ θ₂ * Real.exp (2 * α * c)) *
        selectionMutationScaleDensity α θ₁ θ₂ y)
      (uIcc a b) := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    obtain ⟨hay, hyb⟩ := mem_Icc.mp hy
    have hy01 : y ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha.1 hay, lt_of_le_of_lt hyb hb.2⟩
    exact scaleDensityFrom_selectionMutation α θ₁ θ₂ c y hc hy01
  rw [intervalIntegral.integral_congr (μ := volume) heq, intervalIntegral.integral_const_mul]
private theorem wrightFisher_right_sigma_explicit (α θ₁ θ₂ c a b z : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (∫ y in a..b, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c z =
      (∫ y in a..b, selectionMutationSpeedDensity α θ₁ θ₂ y) *
        selectionMutationScaleDensity α θ₁ θ₂ z := by
  have hinner := wrightFisher_right_speedInner_explicit α θ₁ θ₂ c a b hc ha hb hab
  have houter := scaleDensityFrom_selectionMutation α θ₁ θ₂ c z hc hz
  have h1c : (0 : ℝ) < 1 - c := by linarith [hc.2]
  have hcc := wrightFisher_right_const_cancel c (1 - c) θ₁ θ₂ (-2 * α * c)
    (2 * α * c) hc.1 h1c (by ring)
  rw [hinner, houter]
  linear_combination
    ((∫ y in a..b, selectionMutationSpeedDensity α θ₁ θ₂ y) *
      selectionMutationScaleDensity α θ₁ θ₂ z) * hcc
private theorem wrightFisher_right_scale_explicit (α θ₁ θ₂ c a b z : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a ≤ b) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (∫ y in a..b, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c z =
      (∫ y in a..b, selectionMutationScaleDensity α θ₁ θ₂ y) *
        selectionMutationSpeedDensity α θ₁ θ₂ z := by
  have hinner := wrightFisher_right_scaleInner_explicit α θ₁ θ₂ c a b hc ha hb hab
  have houter := speedDensityFrom_selectionMutation α θ₁ θ₂ c z hc hz
  have h1c : (0 : ℝ) < 1 - c := by linarith [hc.2]
  have hcc := wrightFisher_right_const_cancel c (1 - c) θ₁ θ₂ (-2 * α * c)
    (2 * α * c) hc.1 h1c (by ring)
  rw [hinner, houter]
  linear_combination
    ((∫ y in a..b, selectionMutationScaleDensity α θ₁ θ₂ y) *
      selectionMutationSpeedDensity α θ₁ θ₂ z) * hcc
private theorem wrightFisher_right_speedInner_subst (α θ₁ θ₂ c x : ℝ) :
    (∫ y in c..x, selectionMutationSpeedDensity α θ₁ θ₂ y) =
      Real.exp (2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ y) := by
  have hc1 : (1 : ℝ) - (1 - c) = c := by ring
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hcomp : (∫ u in (1 - x)..(1 - c),
      selectionMutationSpeedDensity α θ₁ θ₂ (1 - u)) =
      (∫ v in c..x, selectionMutationSpeedDensity α θ₁ θ₂ v) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun v => selectionMutationSpeedDensity α θ₁ θ₂ v) 1 (a := 1 - x)
      (b := 1 - c)
    rw [hc1, hx1] at h
    exact h
  have hcongr : (∫ u in (1 - x)..(1 - c),
      selectionMutationSpeedDensity α θ₁ θ₂ (1 - u)) =
      ∫ u in (1 - x)..(1 - c), Real.exp (2 * α) *
        selectionMutationSpeedDensity (-α) θ₂ θ₁ u := by
    apply intervalIntegral.integral_congr
    intro u _
    exact wrightFisher_right_speed_reflect α θ₁ θ₂ u
  have hcm : (∫ u in (1 - x)..(1 - c), Real.exp (2 * α) *
      selectionMutationSpeedDensity (-α) θ₂ θ₁ u) =
      Real.exp (2 * α) *
        (∫ u in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ u) := intervalIntegral.integral_const_mul _ _
  calc (∫ y in c..x, selectionMutationSpeedDensity α θ₁ θ₂ y)
      = (∫ u in (1 - x)..(1 - c),
        selectionMutationSpeedDensity α θ₁ θ₂ (1 - u)) := hcomp.symm
    _ = (∫ u in (1 - x)..(1 - c), Real.exp (2 * α) *
        selectionMutationSpeedDensity (-α) θ₂ θ₁ u) := hcongr
    _ = Real.exp (2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ y) := hcm
private theorem wrightFisher_right_scaleInner_subst (α θ₁ θ₂ c x : ℝ) :
    (∫ y in c..x, selectionMutationScaleDensity α θ₁ θ₂ y) =
      Real.exp (-2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ y) := by
  have hc1 : (1 : ℝ) - (1 - c) = c := by ring
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hcomp : (∫ u in (1 - x)..(1 - c),
      selectionMutationScaleDensity α θ₁ θ₂ (1 - u)) =
      (∫ v in c..x, selectionMutationScaleDensity α θ₁ θ₂ v) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun v => selectionMutationScaleDensity α θ₁ θ₂ v) 1 (a := 1 - x)
      (b := 1 - c)
    rw [hc1, hx1] at h
    exact h
  have hcongr : (∫ u in (1 - x)..(1 - c),
      selectionMutationScaleDensity α θ₁ θ₂ (1 - u)) =
      ∫ u in (1 - x)..(1 - c), Real.exp (-2 * α) *
        selectionMutationScaleDensity (-α) θ₂ θ₁ u := by
    apply intervalIntegral.integral_congr
    intro u _
    exact wrightFisher_right_scale_reflect α θ₁ θ₂ u
  have hcm : (∫ u in (1 - x)..(1 - c), Real.exp (-2 * α) *
      selectionMutationScaleDensity (-α) θ₂ θ₁ u) =
      Real.exp (-2 * α) *
        (∫ u in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ u) := intervalIntegral.integral_const_mul _ _
  calc (∫ y in c..x, selectionMutationScaleDensity α θ₁ θ₂ y)
      = (∫ u in (1 - x)..(1 - c),
        selectionMutationScaleDensity α θ₁ θ₂ (1 - u)) := hcomp.symm
    _ = (∫ u in (1 - x)..(1 - c), Real.exp (-2 * α) *
        selectionMutationScaleDensity (-α) θ₂ θ₁ u) := hcongr
    _ = Real.exp (-2 * α) *
        (∫ y in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ y) := hcm
private theorem wrightFisher_right_sigma_eq (α θ₁ θ₂ c x : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo c 1) :
    (∫ y in c..x, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x =
      (∫ y in (1 - x)..(1 - c), speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := by
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hc.1 hx.1, hx.2⟩
  have hcx : c ≤ x := le_of_lt hx.1
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hz : (1 : ℝ) - x ∈ Ioo (0 : ℝ) (1 - c) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hz01 : (1 : ℝ) - x ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, lt_trans hz.2 (by linarith [hc.1])⟩
  have hzx : (1 : ℝ) - x ≤ 1 - c := le_of_lt hz.2
  have hstep1 := wrightFisher_right_sigma_explicit α θ₁ θ₂ c c x x hc hc hx01
    hcx hx01
  have hsub := wrightFisher_right_speedInner_subst α θ₁ θ₂ c x
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hrout := wrightFisher_right_scale_reflect α θ₁ θ₂ (1 - x)
  rw [hx1] at hrout
  have hexp := wrightFisher_right_exp_cancel α
  have hstep3 := wrightFisher_right_sigma_explicit (-α) θ₂ θ₁ (1 - c) (1 - x)
    (1 - c) (1 - x) hc' hz01 hc' hzx hz01
  calc (∫ y in c..x, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x
      = (∫ y in c..x, selectionMutationSpeedDensity α θ₁ θ₂ y) *
        selectionMutationScaleDensity α θ₁ θ₂ x := hstep1
    _ = (Real.exp (2 * α) *
          (∫ y in (1 - x)..(1 - c),
            selectionMutationSpeedDensity (-α) θ₂ θ₁ y)) *
        (Real.exp (-2 * α) *
          selectionMutationScaleDensity (-α) θ₂ θ₁ (1 - x)) := by rw [hsub, hrout]
    _ = (∫ y in (1 - x)..(1 - c),
          selectionMutationSpeedDensity (-α) θ₂ θ₁ y) *
        selectionMutationScaleDensity (-α) θ₂ θ₁ (1 - x) := by
        linear_combination
          ((∫ y in (1 - x)..(1 - c),
            selectionMutationSpeedDensity (-α) θ₂ θ₁ y) *
            selectionMutationScaleDensity (-α) θ₂ θ₁ (1 - x)) * hexp
    _ = (∫ y in (1 - x)..(1 - c), speedDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := hstep3.symm
private theorem wrightFisher_right_scale_eq (α θ₁ θ₂ c x : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo c 1) :
    (∫ y in c..x, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x =
      (∫ y in (1 - x)..(1 - c), scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := by
  have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans hc.1 hx.1, hx.2⟩
  have hcx : c ≤ x := le_of_lt hx.1
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have hz : (1 : ℝ) - x ∈ Ioo (0 : ℝ) (1 - c) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hz01 : (1 : ℝ) - x ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, lt_trans hz.2 (by linarith [hc.1])⟩
  have hzx : (1 : ℝ) - x ≤ 1 - c := le_of_lt hz.2
  have hstep1 := wrightFisher_right_scale_explicit α θ₁ θ₂ c c x x hc hc hx01
    hcx hx01
  have hsub := wrightFisher_right_scaleInner_subst α θ₁ θ₂ c x
  have hx1 : (1 : ℝ) - (1 - x) = x := by ring
  have hrout := wrightFisher_right_speed_reflect α θ₁ θ₂ (1 - x)
  rw [hx1] at hrout
  have hexp := wrightFisher_right_exp_cancel α
  have hstep3 := wrightFisher_right_scale_explicit (-α) θ₂ θ₁ (1 - c) (1 - x)
    (1 - c) (1 - x) hc' hz01 hc' hzx hz01
  calc (∫ y in c..x, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x
      = (∫ y in c..x, selectionMutationScaleDensity α θ₁ θ₂ y) *
        selectionMutationSpeedDensity α θ₁ θ₂ x := hstep1
    _ = (Real.exp (-2 * α) *
          (∫ y in (1 - x)..(1 - c),
            selectionMutationScaleDensity (-α) θ₂ θ₁ y)) *
        (Real.exp (2 * α) *
          selectionMutationSpeedDensity (-α) θ₂ θ₁ (1 - x)) := by rw [hsub, hrout]
    _ = (∫ y in (1 - x)..(1 - c),
          selectionMutationScaleDensity (-α) θ₂ θ₁ y) *
        selectionMutationSpeedDensity (-α) θ₂ θ₁ (1 - x) := by
        linear_combination
          ((∫ y in (1 - x)..(1 - c),
            selectionMutationScaleDensity (-α) θ₂ θ₁ y) *
            selectionMutationSpeedDensity (-α) θ₂ θ₁ (1 - x)) * hexp
    _ = (∫ y in (1 - x)..(1 - c), scaleDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x) := hstep3.symm
private theorem wrightFisher_right_reflection (f : ℝ → ℝ) (c : ℝ)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => f (1 - x)) (Ioo c 1) volume ↔
      IntegrableOn f (Ioo 0 (1 - c)) volume := by
  have h50 : (0 : ℝ) ≤ 1 - c := by linarith [hc.2]
  have h1 : (1 : ℝ) - (1 - c) = c := by ring
  have h2 : (1 : ℝ) - 0 = 1 := by ring
  calc IntegrableOn (fun x => f (1 - x)) (Ioo c 1) volume
      ↔ IntervalIntegrable (fun x => f (1 - x)) volume c 1 :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.2.le).symm
    _ ↔ IntervalIntegrable (fun x => f (1 - x)) volume (1 - (1 - c))
        (1 - 0) := by
        rw [h1, h2]
    _ ↔ IntervalIntegrable f volume (1 - c) 0 :=
        IntervalIntegrable.comp_sub_left_iff 1
    _ ↔ IntervalIntegrable f volume 0 (1 - c) :=
        ⟨IntervalIntegrable.symm, IntervalIntegrable.symm⟩
    _ ↔ IntegrableOn f (Ioo 0 (1 - c)) volume :=
        intervalIntegrable_iff_integrableOn_Ioo_of_le h50

private theorem integrableOn_wrightFisher_right_sigma_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in c..x, speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo c 1) volume ↔ θ₂ < 1 := by
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have heq : EqOn
      (fun x => (∫ y in c..x, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x)
      (fun x => (∫ y in (1 - x)..(1 - c), speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x))
      (Ioo c 1) := by
    intro x hx
    exact wrightFisher_right_sigma_eq α θ₁ θ₂ c x hc hx
  have hcong : IntegrableOn
      (fun x => (∫ y in c..x, speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x) (Ioo c 1) volume ↔
      IntegrableOn
        (fun x => (∫ y in (1 - x)..(1 - c), speedDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
          scaleDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) (1 - x)) (Ioo c 1) volume :=
    ⟨fun h => h.congr_fun heq measurableSet_Ioo,
      fun h => h.congr_fun heq.symm measurableSet_Ioo⟩
  have hrefl :=
    wrightFisher_right_reflection (fun x => (∫ y in x..(1 - c), speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) x)
      c hc
  have hleft := integrableOn_wrightFisher_left_sigma_iff (-α) θ₂ θ₁ (1 - c) hc'
  exact hcong.trans (hrefl.trans hleft)

private theorem integrableOn_wrightFisher_right_scale_iff
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun x => (∫ y in c..x, scaleDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c y) *
      speedDensityFrom
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c x) (Set.Ioo c 1) volume ↔ 0 < θ₂ := by
  have hc' : (1 : ℝ) - c ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  have heq : EqOn
      (fun x => (∫ y in c..x, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x)
      (fun x => (∫ y in (1 - x)..(1 - c), scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) (1 - x))
      (Ioo c 1) := by
    intro x hx
    exact wrightFisher_right_scale_eq α θ₁ θ₂ c x hc hx
  have hcong : IntegrableOn
      (fun x => (∫ y in c..x, scaleDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c y) *
        speedDensityFrom
        (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
        (fun x => x * (1 - x)) c x) (Ioo c 1) volume ↔
      IntegrableOn
        (fun x => (∫ y in (1 - x)..(1 - c), scaleDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) y) *
          speedDensityFrom
          (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
          (fun x => x * (1 - x)) (1 - c) (1 - x)) (Ioo c 1) volume :=
    ⟨fun h => h.congr_fun heq measurableSet_Ioo,
      fun h => h.congr_fun heq.symm measurableSet_Ioo⟩
  have hrefl :=
    wrightFisher_right_reflection (fun x => (∫ y in x..(1 - c), scaleDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) y) *
        speedDensityFrom
        (fun x => (θ₂ * (1 - x) - θ₁ * x) / 2 + -α * (x * (1 - x)))
        (fun x => x * (1 - x)) (1 - c) x)
      c hc
  have hleft := integrableOn_wrightFisher_left_scale_iff (-α) θ₂ θ₁ (1 - c) hc'
  exact hcong.trans (hrefl.trans hleft)






/-- Basepoint independence of the regular case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, regularity at basepoint `c`
holds iff it holds at `c'`. This states independence of the finiteness
pattern only, not the boundary class itself. Reference: Karlin and Taylor
(1981), Chapter 15. -/
public theorem isRegularBoundaryAtZero_basepoint_iff
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
  constructor
  · intro h
    exact ⟨hP.mp h.1, hQ.mp h.2⟩
  · intro h
    exact ⟨hP.mpr h.1, hQ.mpr h.2⟩

/-- Basepoint independence of the exit case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the exit classification at
basepoint `c` holds iff it holds at `c'`. This states independence of the
finiteness pattern only, not the boundary class itself. Reference: Karlin
and Taylor (1981), Chapter 15. -/
public theorem isExitBoundaryAtZero_basepoint_iff
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
  constructor
  · intro h
    exact ⟨hP.mp h.1, fun hq' => h.2 (hQ.mpr hq')⟩
  · intro h
    exact ⟨hP.mpr h.1, fun hq => h.2 (hQ.mp hq)⟩

/-- Basepoint independence of the entrance case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the entrance classification
at basepoint `c` holds iff it holds at `c'`. This states independence of the
finiteness pattern only, not the boundary class itself. Reference: Karlin
and Taylor (1981), Chapter 15. -/
public theorem isEntranceBoundaryAtZero_basepoint_iff
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
  constructor
  · intro h
    exact ⟨fun hp' => h.1 (hP.mpr hp'), hQ.mp h.2⟩
  · intro h
    exact ⟨fun hp => h.1 (hP.mp hp), hQ.mpr h.2⟩

/-- Basepoint independence of the natural case at `0`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the natural classification at
basepoint `c` holds iff it holds at `c'`. This states independence of the
finiteness pattern only, not the boundary class itself. Reference: Karlin
and Taylor (1981), Chapter 15. -/
public theorem isNaturalBoundaryAtZero_basepoint_iff
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
  constructor
  · intro h
    exact ⟨fun hp' => h.1 (hP.mpr hp'), fun hq' => h.2 (hQ.mpr hq')⟩
  · intro h
    exact ⟨fun hp => h.1 (hP.mp hp), fun hq => h.2 (hQ.mp hq)⟩

/-- Basepoint independence of the regular case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, regularity at basepoint `c`
holds iff it holds at `c'`. This states independence of the finiteness
pattern only, not the boundary class itself. Reference: Karlin and Taylor
(1981), Chapter 15. -/
public theorem isRegularBoundaryAtOne_basepoint_iff
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
  constructor
  · intro h
    exact ⟨hP.mp h.1, hQ.mp h.2⟩
  · intro h
    exact ⟨hP.mpr h.1, hQ.mpr h.2⟩

/-- Basepoint independence of the exit case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the exit classification at
basepoint `c` holds iff it holds at `c'`. This states independence of the
finiteness pattern only, not the boundary class itself. Reference: Karlin
and Taylor (1981), Chapter 15. -/
public theorem isExitBoundaryAtOne_basepoint_iff
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
  constructor
  · intro h
    exact ⟨hP.mp h.1, fun hq' => h.2 (hQ.mpr hq')⟩
  · intro h
    exact ⟨hP.mpr h.1, fun hq => h.2 (hQ.mp hq)⟩

/-- Basepoint independence of the entrance case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the entrance classification
at basepoint `c` holds iff it holds at `c'`. This states independence of the
finiteness pattern only, not the boundary class itself. Reference: Karlin
and Taylor (1981), Chapter 15. -/
public theorem isEntranceBoundaryAtOne_basepoint_iff
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
  constructor
  · intro h
    exact ⟨fun hp' => h.1 (hP.mpr hp'), hQ.mp h.2⟩
  · intro h
    exact ⟨fun hp => h.1 (hP.mp hp), hQ.mpr h.2⟩

/-- Basepoint independence of the natural case at `1`: with `a` positive and
continuous and `b / a` continuous on `Ioo 0 1`, the natural classification at
basepoint `c` holds iff it holds at `c'`. This states independence of the
finiteness pattern only, not the boundary class itself. Reference: Karlin
and Taylor (1981), Chapter 15. -/
public theorem isNaturalBoundaryAtOne_basepoint_iff
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
  constructor
  · intro h
    exact ⟨fun hp' => h.1 (hP.mpr hp'), fun hq' => h.2 (hQ.mpr hq')⟩
  · intro h
    exact ⟨fun hp => h.1 (hP.mp hp), fun hq => h.2 (hQ.mp hq)⟩

/-- Wright-Fisher selection-mutation diffusion at `0`: with mutation parameter
`θ₁ = 0`, drift `(θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))` and
diffusion coefficient `x * (1 - x)`, the endpoint `0` is an exit boundary,
for any selection `α`, any `θ₂`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The
conclusion records finiteness of the Feller functionals only. References:
Karlin and Taylor (1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtZero_selectionMutation_exit
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : θ₁ = 0) :
    IsExitBoundaryAtZero
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsExitBoundaryAtZero
  have hSigma := integrableOn_wrightFisher_left_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_left_scale_iff α θ₁ θ₂ c hc
  have h1 : θ₁ < 1 := by rw [hθ]; exact zero_lt_one
  have h2 : ¬ 0 < θ₁ := by rw [hθ]; exact lt_irrefl 0
  exact ⟨hSigma.mpr h1, fun h => h2 (hScale.mp h)⟩

/-- Wright-Fisher selection-mutation diffusion at `0`: with mutation
parameters `0 < θ₁ < 1`, drift as above and diffusion coefficient
`x * (1 - x)`, the endpoint `0` is a regular boundary, for any selection `α`,
any `θ₂`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records
finiteness of the Feller functionals only. References: Karlin and Taylor
(1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtZero_selectionMutation_regular
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 < θ₁ ∧ θ₁ < 1) :
    IsRegularBoundaryAtZero
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsRegularBoundaryAtZero
  have hSigma := integrableOn_wrightFisher_left_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_left_scale_iff α θ₁ θ₂ c hc
  exact ⟨hSigma.mpr hθ.2, hScale.mpr hθ.1⟩

/-- Wright-Fisher selection-mutation diffusion at `0`: with mutation parameter
`1 ≤ θ₁`, drift as above and diffusion coefficient `x * (1 - x)`, the
endpoint `0` is an entrance boundary, for any selection `α`, any `θ₂`, and
any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records finiteness of the
Feller functionals only. References: Karlin and Taylor (1981), Chapter 15
and Ewens (2004), Chapter 4. -/
public theorem boundaryAtZero_selectionMutation_entrance
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : 1 ≤ θ₁) :
    IsEntranceBoundaryAtZero
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsEntranceBoundaryAtZero
  have hSigma := integrableOn_wrightFisher_left_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_left_scale_iff α θ₁ θ₂ c hc
  have h1 : ¬ θ₁ < 1 := not_lt_of_ge hθ
  have h2 : 0 < θ₁ := lt_of_lt_of_le zero_lt_one hθ
  exact ⟨fun h => h1 (hSigma.mp h), hScale.mpr h2⟩

/-- Wright-Fisher selection-mutation diffusion at `1`: with mutation parameter
`θ₂ = 0`, drift `(θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x))` and
diffusion coefficient `x * (1 - x)`, the endpoint `1` is an exit boundary,
for any selection `α`, any `θ₁`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The
conclusion records finiteness of the Feller functionals only. References:
Karlin and Taylor (1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtOne_selectionMutation_exit
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : θ₂ = 0) :
    IsExitBoundaryAtOne
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsExitBoundaryAtOne
  have hSigma := integrableOn_wrightFisher_right_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_right_scale_iff α θ₁ θ₂ c hc
  have h1 : θ₂ < 1 := by rw [hθ]; exact zero_lt_one
  have h2 : ¬ 0 < θ₂ := by rw [hθ]; exact lt_irrefl 0
  exact ⟨hSigma.mpr h1, fun h => h2 (hScale.mp h)⟩

/-- Wright-Fisher selection-mutation diffusion at `1`: with mutation
parameters `0 < θ₂ < 1`, drift as above and diffusion coefficient
`x * (1 - x)`, the endpoint `1` is a regular boundary, for any selection `α`,
any `θ₁`, and any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records
finiteness of the Feller functionals only. References: Karlin and Taylor
(1981), Chapter 15 and Ewens (2004), Chapter 4. -/
public theorem boundaryAtOne_selectionMutation_regular
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hθ : 0 < θ₂ ∧ θ₂ < 1) :
    IsRegularBoundaryAtOne
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsRegularBoundaryAtOne
  have hSigma := integrableOn_wrightFisher_right_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_right_scale_iff α θ₁ θ₂ c hc
  exact ⟨hSigma.mpr hθ.2, hScale.mpr hθ.1⟩

/-- Wright-Fisher selection-mutation diffusion at `1`: with mutation parameter
`1 ≤ θ₂`, drift as above and diffusion coefficient `x * (1 - x)`, the
endpoint `1` is an entrance boundary, for any selection `α`, any `θ₁`, and
any basepoint `c ∈ Ioo (0 : ℝ) 1`. The conclusion records finiteness of the
Feller functionals only. References: Karlin and Taylor (1981), Chapter 15
and Ewens (2004), Chapter 4. -/
public theorem boundaryAtOne_selectionMutation_entrance
    (α θ₁ θ₂ : ℝ) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hθ : 1 ≤ θ₂) :
    IsEntranceBoundaryAtOne
      (fun x => (θ₁ * (1 - x) - θ₂ * x) / 2 + α * (x * (1 - x)))
      (fun x => x * (1 - x)) c := by
  unfold IsEntranceBoundaryAtOne
  have hSigma := integrableOn_wrightFisher_right_sigma_iff α θ₁ θ₂ c hc
  have hScale := integrableOn_wrightFisher_right_scale_iff α θ₁ θ₂ c hc
  have h1 : ¬ θ₂ < 1 := not_lt_of_ge hθ
  have h2 : 0 < θ₂ := lt_of_lt_of_le zero_lt_one hθ
  exact ⟨fun h => h1 (hSigma.mp h), hScale.mpr h2⟩

end MathlibExt.Biology.PopulationGenetics.Diffusion
