/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Domains.Biology.PopulationGenetics.Diffusion.SpeedDensity
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Selection-mutation stationary partition function

This module introduces the normalizing constant (partition function), mean,
and variance of the mutation-selection stationary density on the unit
interval, together with the derivative identities relating them.

The stationary density is proportional to `e ^ (2 * α * x) * x ^ (θ₁ - 1) *
(1 - x) ^ (θ₂ - 1)` on `(0, 1)`, where `α` is the selection parameter and
`θ₁`, `θ₂` are the mutation parameters. Differentiating the log-normalizer
in `α` gives twice the stationary mean, and differentiating the mean gives
twice the stationary variance; hence the mean is strictly increasing in `α`.

## Main definitions

* `selectionMutationPartition`: the normalizing integral of the
  selection-mutation speed density over `(0, 1)`.
* `selectionMutationMean`: the normalized first moment (stationary mean).
* `selectionMutationVariance`: the normalized centered second moment.

## Main results

* `intervalIntegrable_selectionMutationSpeedDensity`: integrability of the
  density on `[0, 1]` for positive mutation parameters.
* `selectionMutationPartition_pos`: positivity of the normalizer.
* `hasDerivAt_log_selectionMutationPartition`: the log-normalizer derivative
  is twice the mean.
* `hasDerivAt_selectionMutationMean`: the mean derivative is twice the
  variance.
* `selectionMutationVariance_pos`: positivity of the variance.
* `strictMono_selectionMutationMean`: the mean is strictly increasing in `α`.

## Conventions

Parameters are real numbers: `α` is arbitrary while the theorems assume
`0 < θ₁` and `0 < θ₂`. Integrals are interval integrals over `(0, 1)`, so
the definitions make sense for all real parameters; outside the positivity
hypotheses the values are junk. Real powers follow Mathlib convention.

These are analytic statements about the density and its normalizer only.
No claim is made about construction of a mutation-selection process, about
invariance of any process law, or about convergence to equilibrium.

## References

* Wright, S. (1931). Evolution in Mendelian populations. Genetics 16:97-159.
* Crow, J. F. and Kimura, M. (1970). An Introduction to Population Genetics
  Theory. Harper & Row.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Normalizing constant (partition function) of the selection-mutation
stationary density: the integral of `selectionMutationSpeedDensity` over
`(0, 1)`. Defined for all real parameters by the interval-integral junk
convention; the theorems assume `0 < θ₁` and `0 < θ₂`. For `θ₁ ≤ 0` or `θ₂ ≤ 0` the
density is not integrable on `[0, 1]` and the value is `0`. This is an analytic
normalizer only, not a process construction. -/
noncomputable def selectionMutationPartition (α θ₁ θ₂ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, selectionMutationSpeedDensity α θ₁ θ₂ x

/-- Stationary mean under selection-mutation balance: the normalized first
moment of the speed density over `(0, 1)`. The integral of a non-integrable function is `0`
(which makes the normalizer vanish for `θ₁ ≤ 0` or `θ₂ ≤ 0`), and with `x / 0 = 0` the ratio is `0`
when the normalizer vanishes; that the normalizer is positive for `0 < θ₁`, `0 < θ₂` is proved
separately. -/
noncomputable def selectionMutationMean (α θ₁ θ₂ : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, x * selectionMutationSpeedDensity α θ₁ θ₂ x) /
    selectionMutationPartition α θ₁ θ₂

/-- Stationary variance under selection-mutation balance: the normalized
centered second moment of the speed density over `(0, 1)`, centered at
`selectionMutationMean`. The integral of a non-integrable function is `0` (which makes the
normalizer vanish for `θ₁ ≤ 0` or `θ₂ ≤ 0`), and with `x / 0 = 0` the variance is `0` when the
normalizer vanishes. The intended domain is `0 < θ₁`, `0 < θ₂`. -/
noncomputable def selectionMutationVariance (α θ₁ θ₂ : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1,
      (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
        selectionMutationSpeedDensity α θ₁ θ₂ x) /
    selectionMutationPartition α θ₁ θ₂

/-- Nonnegativity of the mutation speed density on `[0, 1]`. -/
private theorem mutationSpeedDensity_nonneg_aux (θ₁ θ₂ x : ℝ) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : 0 ≤ mutationSpeedDensity θ₁ θ₂ x := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have ha := Real.rpow_nonneg hx0 (θ₁ - 1)
  have hb := Real.rpow_nonneg (sub_nonneg.mpr hx1) (θ₂ - 1)
  simpa only [mutationSpeedDensity, mul_assoc, mul_comm, mul_left_comm] using
    mul_nonneg (mul_nonneg h2 ha) hb

/-- Positivity of the mutation speed density on `(0, 1)`. -/
private theorem mutationSpeedDensity_pos_aux (θ₁ θ₂ x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) : 0 < mutationSpeedDensity θ₁ θ₂ x := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have ha := Real.rpow_pos_of_pos hx0 (θ₁ - 1)
  have hb := Real.rpow_pos_of_pos (sub_pos.mpr hx1) (θ₂ - 1)
  simpa only [mutationSpeedDensity, mul_assoc, mul_comm, mul_left_comm] using
    mul_pos (mul_pos h2 ha) hb

/-- Nonnegativity of the selection-mutation speed density on `[0, 1]`. -/
private theorem selectionSpeedDensity_nonneg_aux (α θ₁ θ₂ x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ selectionMutationSpeedDensity α θ₁ θ₂ x := by
  have he := (Real.exp_pos (2 * α * x)).le
  have hm := mutationSpeedDensity_nonneg_aux θ₁ θ₂ x hx0 hx1
  simpa only [selectionMutationSpeedDensity, mutationSpeedDensity, mul_assoc,
    mul_comm, mul_left_comm] using mul_nonneg he hm

/-- Positivity of the selection-mutation speed density on `(0, 1)`. -/
private theorem selectionSpeedDensity_pos_aux (α θ₁ θ₂ x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) : 0 < selectionMutationSpeedDensity α θ₁ θ₂ x := by
  have he := Real.exp_pos (2 * α * x)
  have hm := mutationSpeedDensity_pos_aux θ₁ θ₂ x hx0 hx1
  simpa only [selectionMutationSpeedDensity, mutationSpeedDensity, mul_assoc,
    mul_comm, mul_left_comm] using mul_pos he hm

/-- Points of `Ioo (α₀ - 1) (α₀ + 1)` have norm at most `|α₀| + 1`. -/
private theorem abs_le_of_mem_Ioo_aux {α α₀ : ℝ}
    (hα : α ∈ Set.Ioo (α₀ - 1) (α₀ + 1)) : |α| ≤ |α₀| + 1 := by
  obtain ⟨hlo, hhi⟩ := hα
  have habs : |α - α₀| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have htri : |α| ≤ |α - α₀| + |α₀| := by
    conv_lhs => rw [← sub_add_cancel α α₀]
    exact abs_add_le _ _
  linarith [htri, habs]

/-- Interval integrability of the mutation speed density on `[0, 1]`. -/
private theorem intervalIntegrable_mutation_aux (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) :
    IntervalIntegrable (fun x => mutationSpeedDensity θ₁ θ₂ x)
      MeasureTheory.volume 0 1 := by
  have hleft : IntervalIntegrable
      (fun x : ℝ => 2 * x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1))
      MeasureTheory.volume 0 (1 / 2) := by
    have hrpow : IntervalIntegrable (fun x : ℝ => x ^ (θ₁ - 1))
        MeasureTheory.volume 0 (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow'
        (show (-1 : ℝ) < θ₁ - 1 by linarith)
    have h2 : IntervalIntegrable (fun x : ℝ => 2 * x ^ (θ₁ - 1))
        MeasureTheory.volume 0 (1 / 2) :=
      hrpow.const_mul 2
    have hcont : ContinuousOn (fun x : ℝ => (1 - x) ^ (θ₂ - 1))
        (Set.uIcc 0 (1 / 2)) := by
      refine ContinuousOn.rpow_const
        (continuousOn_const.sub continuousOn_id) ?_
      intro x hx
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have hne : (1 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      exact Or.inl hne
    exact h2.mul_continuousOn hcont
  have hright : IntervalIntegrable
      (fun x : ℝ => 2 * x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1))
      MeasureTheory.volume (1 / 2) 1 := by
    have hbase : IntervalIntegrable (fun x : ℝ => x ^ (θ₂ - 1))
        MeasureTheory.volume 0 (1 / 2) :=
      intervalIntegral.intervalIntegrable_rpow'
        (show (-1 : ℝ) < θ₂ - 1 by linarith)
    have hrefl : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (θ₂ - 1))
        MeasureTheory.volume (1 / 2) 1 := by
      have h := (hbase.comp_sub_left (1 : ℝ)).symm
      simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        show (1 : ℝ) - 0 = 1 by norm_num] using h
    have hcont : ContinuousOn (fun x : ℝ => 2 * x ^ (θ₁ - 1))
        (Set.uIcc (1 / 2) 1) := by
      have hpow : ContinuousOn (fun x : ℝ => x ^ (θ₁ - 1))
          (Set.uIcc (1 / 2) 1) := by
        refine ContinuousOn.rpow_const continuousOn_id ?_
        intro x hx
        rw [Set.uIcc_of_le (show (1 / 2 : ℝ) ≤ 1 by norm_num)] at hx
        obtain ⟨hx0, hx1⟩ := hx
        have hne : (x : ℝ) ≠ 0 := ne_of_gt (by linarith)
        exact Or.inl hne
      exact hpow.const_mul 2
    exact hrefl.continuousOn_mul hcont
  have h := hleft.trans hright
  simpa only [mutationSpeedDensity, mul_assoc, mul_comm, mul_left_comm] using
    h

/-- The selection-mutation speed density is interval integrable on `[0, 1]`
for positive mutation parameters. -/
theorem intervalIntegrable_selectionMutationSpeedDensity (α : ℝ) {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    IntervalIntegrable (fun x => selectionMutationSpeedDensity α θ₁ θ₂ x)
      MeasureTheory.volume 0 1 := by
  have hm := intervalIntegrable_mutation_aux θ₁ θ₂ hθ₁ hθ₂
  have hexp : ContinuousOn (fun x : ℝ => Real.exp (2 * α * x))
      (Set.uIcc 0 1) := by
    have hlin : ContinuousOn (fun x : ℝ => 2 * α * x) (Set.uIcc 0 1) :=
      continuousOn_id.const_mul (2 * α)
    exact hlin.rexp
  have h := hm.continuousOn_mul hexp
  simpa only [selectionMutationSpeedDensity, mutationSpeedDensity, mul_assoc,
    mul_comm, mul_left_comm] using h

/-- Integrability of `x ↦ x * density` on `[0, 1]`. -/
private theorem intervalIntegrable_x_mul_aux (α θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) :
    IntervalIntegrable
      (fun x : ℝ => x * selectionMutationSpeedDensity α θ₁ θ₂ x)
      MeasureTheory.volume 0 1 :=
  (intervalIntegrable_selectionMutationSpeedDensity α hθ₁
    hθ₂).continuousOn_mul continuousOn_id

/-- Integrability of `x ↦ (x * x) * density` on `[0, 1]`. -/
private theorem intervalIntegrable_xx_mul_aux (α θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) :
    IntervalIntegrable
      (fun x : ℝ => (x * x) * selectionMutationSpeedDensity α θ₁ θ₂ x)
      MeasureTheory.volume 0 1 := by
  have hxx : ContinuousOn (fun x : ℝ => x * x) (Set.uIcc 0 1) :=
    continuousOn_id.mul continuousOn_id
  exact (intervalIntegrable_selectionMutationSpeedDensity α hθ₁
    hθ₂).continuousOn_mul hxx

/-- Derivative of the partition function in the selection parameter. -/
private theorem hasDerivAt_selectionPartition_aux (α₀ θ₁ θ₂ : ℝ)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    HasDerivAt (fun α => selectionMutationPartition α θ₁ θ₂)
      (2 * ∫ x in (0 : ℝ)..1, x * selectionMutationSpeedDensity α₀ θ₁ θ₂ x)
      α₀ := by
  unfold selectionMutationPartition
  have hs : Set.Ioo (α₀ - 1) (α₀ + 1) ∈ nhds α₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : Filter.Eventually
      (fun α => MeasureTheory.AEStronglyMeasurable
        (fun x => selectionMutationSpeedDensity α θ₁ θ₂ x)
        (MeasureTheory.volume.restrict (Set.uIoc 0 1)))
      (nhds α₀) :=
    Filter.Eventually.of_forall fun α =>
      (intervalIntegrable_selectionMutationSpeedDensity α hθ₁
        hθ₂).aestronglyMeasurable_restrict_uIoc
  have hF_int :=
    intervalIntegrable_selectionMutationSpeedDensity α₀ hθ₁ hθ₂
  have hF'_meas :=
    ((intervalIntegrable_x_mul_aux α₀ θ₁ θ₂ hθ₁
      hθ₂).const_mul 2).aestronglyMeasurable_restrict_uIoc
  have h_bound : Filter.Eventually
      (fun t => t ∈ Set.uIoc 0 1 → ∀ α ∈ Set.Ioo (α₀ - 1) (α₀ + 1),
        ‖2 * (t * selectionMutationSpeedDensity α θ₁ θ₂ t)‖ ≤
          2 * Real.exp (2 * (|α₀| + 1)) *
            mutationSpeedDensity θ₁ θ₂ t)
      (MeasureTheory.ae MeasureTheory.volume) := by
    refine Filter.Eventually.of_forall fun t ht α hα => ?_
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hα := abs_le_of_mem_Ioo_aux hα
    have hm : 0 ≤ mutationSpeedDensity θ₁ θ₂ t :=
      mutationSpeedDensity_nonneg_aux θ₁ θ₂ t ht0.le ht1
    have h1 : 2 * α * t ≤ 2 * (|α₀| + 1) := by
      have e1 : α * t ≤ |α| * t :=
        mul_le_mul_of_nonneg_right (le_abs_self α) ht0.le
      have e2 : |α| * t ≤ (|α₀| + 1) * 1 :=
        mul_le_mul hα ht1 ht0.le (by linarith [abs_nonneg α₀])
      linarith [e1, e2]
    have h2 : Real.exp (2 * α * t) ≤ Real.exp (2 * (|α₀| + 1)) :=
      Real.exp_strictMono.monotone h1
    have hnn : (0 : ℝ) ≤
        2 * (t * selectionMutationSpeedDensity α θ₁ θ₂ t) :=
      mul_nonneg (by norm_num) (mul_nonneg ht0.le
        (selectionSpeedDensity_nonneg_aux α θ₁ θ₂ t ht0.le ht1))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hcore : 2 * (t * Real.exp (2 * α * t)) ≤
        2 * Real.exp (2 * (|α₀| + 1)) := by
      have e3 : t * Real.exp (2 * α * t) ≤
          1 * Real.exp (2 * (|α₀| + 1)) :=
        mul_le_mul ht1 h2 (Real.exp_pos _).le (by norm_num)
      linarith [e3]
    have hdecomp : 2 * (t * selectionMutationSpeedDensity α θ₁ θ₂ t) =
        (2 * (t * Real.exp (2 * α * t))) *
          mutationSpeedDensity θ₁ θ₂ t := by
      simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
        mul_assoc, mul_comm, mul_left_comm]
    rw [hdecomp]
    exact mul_le_mul_of_nonneg_right hcore hm
  have hbound_int : IntervalIntegrable
      (fun x : ℝ => 2 * Real.exp (2 * (|α₀| + 1)) *
        mutationSpeedDensity θ₁ θ₂ x)
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_mutation_aux θ₁ θ₂ hθ₁
      hθ₂).const_mul (2 * Real.exp (2 * (|α₀| + 1)))
  have h_diff : Filter.Eventually
      (fun t => t ∈ Set.uIoc 0 1 → ∀ α ∈ Set.Ioo (α₀ - 1) (α₀ + 1),
        HasDerivAt (fun α' => selectionMutationSpeedDensity α' θ₁ θ₂ t)
          (2 * (t * selectionMutationSpeedDensity α θ₁ θ₂ t)) α)
      (MeasureTheory.ae MeasureTheory.volume) := by
    refine Filter.Eventually.of_forall fun t _ α _ => ?_
    have hinner : HasDerivAt (fun a : ℝ => 2 * a * t) ((2 * 1) * t) α :=
      ((hasDerivAt_id' α).const_mul 2).mul_const t
    have hexp : HasDerivAt (fun a : ℝ => Real.exp (2 * a * t))
        (Real.exp (2 * α * t) * ((2 * 1) * t)) α :=
      hinner.exp
    have hmul := hexp.mul_const (mutationSpeedDensity θ₁ θ₂ t)
    have hfun : (fun α' => selectionMutationSpeedDensity α' θ₁ θ₂ t) =
        (fun α' => Real.exp (2 * α' * t) *
          mutationSpeedDensity θ₁ θ₂ t) := by
      funext α'
      simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
        mul_assoc, mul_comm, mul_left_comm]
    rw [hfun]
    refine hmul.congr_deriv ?_
    simp only [selectionMutationSpeedDensity, mutationSpeedDensity]
    ring
  have hmain :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun a x => selectionMutationSpeedDensity a θ₁ θ₂ x)
      (F' := fun a x => 2 * (x * selectionMutationSpeedDensity a θ₁ θ₂ x))
      (s := Set.Ioo (α₀ - 1) (α₀ + 1))
      (bound := fun x => 2 * Real.exp (2 * (|α₀| + 1)) *
        mutationSpeedDensity θ₁ θ₂ x)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hderiv := hmain.2
  simp only [intervalIntegral.integral_const_mul] at hderiv
  exact hderiv

/-- Derivative of the unnormalized first moment in `α`. -/
private theorem hasDerivAt_selectionMoment_aux (α₀ θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) :
    HasDerivAt
      (fun α => ∫ x in (0 : ℝ)..1,
        x * selectionMutationSpeedDensity α θ₁ θ₂ x)
      (2 * ∫ x in (0 : ℝ)..1, (x * x) *
        selectionMutationSpeedDensity α₀ θ₁ θ₂ x)
      α₀ := by
  have hs : Set.Ioo (α₀ - 1) (α₀ + 1) ∈ nhds α₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : Filter.Eventually
      (fun α => MeasureTheory.AEStronglyMeasurable
        (fun x => x * selectionMutationSpeedDensity α θ₁ θ₂ x)
        (MeasureTheory.volume.restrict (Set.uIoc 0 1)))
      (nhds α₀) :=
    Filter.Eventually.of_forall fun α =>
      (intervalIntegrable_x_mul_aux α θ₁ θ₂ hθ₁
        hθ₂).aestronglyMeasurable_restrict_uIoc
  have hF_int := intervalIntegrable_x_mul_aux α₀ θ₁ θ₂ hθ₁ hθ₂
  have hF'_meas :=
    ((intervalIntegrable_xx_mul_aux α₀ θ₁ θ₂ hθ₁
      hθ₂).const_mul 2).aestronglyMeasurable_restrict_uIoc
  have h_bound : Filter.Eventually
      (fun t => t ∈ Set.uIoc 0 1 → ∀ α ∈ Set.Ioo (α₀ - 1) (α₀ + 1),
        ‖2 * ((t * t) * selectionMutationSpeedDensity α θ₁ θ₂ t)‖ ≤
          2 * Real.exp (2 * (|α₀| + 1)) *
            mutationSpeedDensity θ₁ θ₂ t)
      (MeasureTheory.ae MeasureTheory.volume) := by
    refine Filter.Eventually.of_forall fun t ht α hα => ?_
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hα := abs_le_of_mem_Ioo_aux hα
    have hm : 0 ≤ mutationSpeedDensity θ₁ θ₂ t :=
      mutationSpeedDensity_nonneg_aux θ₁ θ₂ t ht0.le ht1
    have htt1 : t * t ≤ 1 * 1 :=
      mul_le_mul ht1 ht1 ht0.le (by norm_num)
    have h1 : 2 * α * t ≤ 2 * (|α₀| + 1) := by
      have e1 : α * t ≤ |α| * t :=
        mul_le_mul_of_nonneg_right (le_abs_self α) ht0.le
      have e2 : |α| * t ≤ (|α₀| + 1) * 1 :=
        mul_le_mul hα ht1 ht0.le (by linarith [abs_nonneg α₀])
      linarith [e1, e2]
    have h2 : Real.exp (2 * α * t) ≤ Real.exp (2 * (|α₀| + 1)) :=
      Real.exp_strictMono.monotone h1
    have htt0 : (0 : ℝ) ≤ t * t := mul_nonneg ht0.le ht0.le
    have hnn : (0 : ℝ) ≤
        2 * ((t * t) * selectionMutationSpeedDensity α θ₁ θ₂ t) :=
      mul_nonneg (by norm_num) (mul_nonneg htt0
        (selectionSpeedDensity_nonneg_aux α θ₁ θ₂ t ht0.le ht1))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hcore : 2 * ((t * t) * Real.exp (2 * α * t)) ≤
        2 * Real.exp (2 * (|α₀| + 1)) := by
      have e3 : (t * t) * Real.exp (2 * α * t) ≤
          (1 * 1) * Real.exp (2 * (|α₀| + 1)) :=
        mul_le_mul htt1 h2 (Real.exp_pos _).le (by norm_num)
      linarith [e3]
    have hdecomp : 2 * ((t * t) * selectionMutationSpeedDensity α θ₁ θ₂ t) =
        (2 * ((t * t) * Real.exp (2 * α * t))) *
          mutationSpeedDensity θ₁ θ₂ t := by
      simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
        mul_assoc, mul_comm, mul_left_comm]
    rw [hdecomp]
    exact mul_le_mul_of_nonneg_right hcore hm
  have hbound_int : IntervalIntegrable
      (fun x : ℝ => 2 * Real.exp (2 * (|α₀| + 1)) *
        mutationSpeedDensity θ₁ θ₂ x)
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_mutation_aux θ₁ θ₂ hθ₁
      hθ₂).const_mul (2 * Real.exp (2 * (|α₀| + 1)))
  have h_diff : Filter.Eventually
      (fun t => t ∈ Set.uIoc 0 1 → ∀ α ∈ Set.Ioo (α₀ - 1) (α₀ + 1),
        HasDerivAt (fun α' => t * selectionMutationSpeedDensity α' θ₁ θ₂ t)
          (2 * ((t * t) * selectionMutationSpeedDensity α θ₁ θ₂ t)) α)
      (MeasureTheory.ae MeasureTheory.volume) := by
    refine Filter.Eventually.of_forall fun t _ α _ => ?_
    have hinner : HasDerivAt (fun a : ℝ => 2 * a * t) ((2 * 1) * t) α :=
      ((hasDerivAt_id' α).const_mul 2).mul_const t
    have hexp : HasDerivAt (fun a : ℝ => Real.exp (2 * a * t))
        (Real.exp (2 * α * t) * ((2 * 1) * t)) α :=
      hinner.exp
    have hmul := hexp.mul_const (mutationSpeedDensity θ₁ θ₂ t)
    have hN := HasDerivAt.const_mul t hmul
    have hfun : (fun α' => t * selectionMutationSpeedDensity α' θ₁ θ₂ t) =
        (fun α' => t * (Real.exp (2 * α' * t) *
          mutationSpeedDensity θ₁ θ₂ t)) := by
      funext α'
      simp only [selectionMutationSpeedDensity, mutationSpeedDensity,
        mul_assoc, mul_comm, mul_left_comm]
    rw [hfun]
    refine hN.congr_deriv ?_
    simp only [selectionMutationSpeedDensity, mutationSpeedDensity]
    ring
  have hmain :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun a x => x * selectionMutationSpeedDensity a θ₁ θ₂ x)
      (F' := fun a x => 2 * ((x * x) * selectionMutationSpeedDensity a θ₁ θ₂ x))
      (s := Set.Ioo (α₀ - 1) (α₀ + 1))
      (bound := fun x => 2 * Real.exp (2 * (|α₀| + 1)) *
        mutationSpeedDensity θ₁ θ₂ x)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hderiv := hmain.2
  simp only [intervalIntegral.integral_const_mul] at hderiv
  exact hderiv

/-- Positivity of the selection-mutation partition function for positive
mutation parameters. -/
theorem selectionMutationPartition_pos (α : ℝ) {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) : 0 < selectionMutationPartition α θ₁ θ₂ := by
  unfold selectionMutationPartition
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_selectionMutationSpeedDensity α hθ₁ hθ₂) ?_
    (by norm_num)
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  show 0 < selectionMutationSpeedDensity α θ₁ θ₂ x
  exact selectionSpeedDensity_pos_aux α θ₁ θ₂ x hx0 hx1

/-- Derivative of the log partition function in the selection parameter, for positive
mutation parameters: d/dα log Z equals twice the stationary mean. -/
theorem hasDerivAt_log_selectionMutationPartition (α : ℝ) {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    HasDerivAt (fun α => Real.log (selectionMutationPartition α θ₁ θ₂))
      (2 * selectionMutationMean α θ₁ θ₂) α := by
  have hZ := hasDerivAt_selectionPartition_aux α θ₁ θ₂ hθ₁ hθ₂
  have hZne : selectionMutationPartition α θ₁ θ₂ ≠ 0 :=
    ne_of_gt (selectionMutationPartition_pos α hθ₁ hθ₂)
  have hlog := hZ.log hZne
  refine hlog.congr_deriv ?_
  unfold selectionMutationMean
  ring

/-- Derivative of the stationary mean in the selection parameter, for positive mutation
parameters: d/dα mean equals twice the stationary variance. -/
theorem hasDerivAt_selectionMutationMean (α : ℝ) {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) :
    HasDerivAt (fun α => selectionMutationMean α θ₁ θ₂)
      (2 * selectionMutationVariance α θ₁ θ₂) α := by
  have hN := hasDerivAt_selectionMoment_aux α θ₁ θ₂ hθ₁ hθ₂
  have hZ := hasDerivAt_selectionPartition_aux α θ₁ θ₂ hθ₁ hθ₂
  have hZne : selectionMutationPartition α θ₁ θ₂ ≠ 0 :=
    ne_of_gt (selectionMutationPartition_pos α hθ₁ hθ₂)
  have hdiv := hN.fun_div hZ hZne
  have hexpand : ∫ x in (0 : ℝ)..1,
        (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
          selectionMutationSpeedDensity α θ₁ θ₂ x =
      (∫ x in (0 : ℝ)..1, (x * x) *
          selectionMutationSpeedDensity α θ₁ θ₂ x) -
        2 * selectionMutationMean α θ₁ θ₂ *
          (∫ x in (0 : ℝ)..1, x * selectionMutationSpeedDensity α θ₁ θ₂ x) +
        (selectionMutationMean α θ₁ θ₂) ^ 2 *
          selectionMutationPartition α θ₁ θ₂ := by
    have hfun : (fun x : ℝ => (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
          selectionMutationSpeedDensity α θ₁ θ₂ x) =
        (fun x => ((x * x) * selectionMutationSpeedDensity α θ₁ θ₂ x -
          2 * selectionMutationMean α θ₁ θ₂ *
            (x * selectionMutationSpeedDensity α θ₁ θ₂ x)) +
          (selectionMutationMean α θ₁ θ₂) ^ 2 *
            selectionMutationSpeedDensity α θ₁ θ₂ x) := by
      funext x
      ring
    have hA := intervalIntegrable_xx_mul_aux α θ₁ θ₂ hθ₁ hθ₂
    have hB : IntervalIntegrable
        (fun x : ℝ => 2 * selectionMutationMean α θ₁ θ₂ *
          (x * selectionMutationSpeedDensity α θ₁ θ₂ x))
        MeasureTheory.volume 0 1 :=
      (intervalIntegrable_x_mul_aux α θ₁ θ₂ hθ₁ hθ₂).const_mul
        (2 * selectionMutationMean α θ₁ θ₂)
    have hC : IntervalIntegrable
        (fun x : ℝ => (selectionMutationMean α θ₁ θ₂) ^ 2 *
          selectionMutationSpeedDensity α θ₁ θ₂ x)
        MeasureTheory.volume 0 1 :=
      (intervalIntegrable_selectionMutationSpeedDensity α hθ₁
        hθ₂).const_mul ((selectionMutationMean α θ₁ θ₂) ^ 2)
    have hsub : IntervalIntegrable
        (fun x : ℝ => (x * x) * selectionMutationSpeedDensity α θ₁ θ₂ x -
          2 * selectionMutationMean α θ₁ θ₂ *
            (x * selectionMutationSpeedDensity α θ₁ θ₂ x))
        MeasureTheory.volume 0 1 :=
      hA.sub hB
    rw [hfun, intervalIntegral.integral_add hsub hC,
      intervalIntegral.integral_sub hA hB,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp only [selectionMutationPartition]
  unfold selectionMutationMean
  refine hdiv.congr_deriv ?_
  unfold selectionMutationVariance
  rw [hexpand]
  unfold selectionMutationMean
  have hZ2 : (selectionMutationPartition α θ₁ θ₂) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hZne hZne
  field_simp [hZne, hZ2]
  ring

/-- The centered-square integrand is positive away from the mean. -/
private theorem varianceIntegrand_pos_aux (α θ₁ θ₂ x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) (hne : x ≠ selectionMutationMean α θ₁ θ₂) :
    0 < (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
      selectionMutationSpeedDensity α θ₁ θ₂ x := by
  have hsq : (0 : ℝ) < (x - selectionMutationMean α θ₁ θ₂) ^ 2 := by
    have h' : x - selectionMutationMean α θ₁ θ₂ ≠ 0 :=
      sub_ne_zero.mpr hne
    have hsq0 : (x - selectionMutationMean α θ₁ θ₂) ^ 2 ≠ 0 := by
      rw [pow_two]
      exact mul_ne_zero h' h'
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hsq0)
  exact mul_pos hsq
    (selectionSpeedDensity_pos_aux α θ₁ θ₂ x hx0 hx1)

/-- A subinterval avoiding the mean gives the support positive measure. -/
private theorem support_pos_of_Ioo_aux (α θ₁ θ₂ lo hi : ℝ) (hlo0 : 0 < lo)
    (hhi1 : hi < 1) (hlt : lo < hi)
    (havoid : ∀ x ∈ Set.Ioo lo hi, x ≠ selectionMutationMean α θ₁ θ₂) :
    0 < MeasureTheory.volume
      (Function.support (fun x : ℝ => (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
        selectionMutationSpeedDensity α θ₁ θ₂ x) ∩ Set.Ioc 0 1) := by
  have hJ : Set.Ioo lo hi ⊆
      Function.support (fun x : ℝ => (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
        selectionMutationSpeedDensity α θ₁ θ₂ x) ∩ Set.Ioc 0 1 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · have hx0 : (0 : ℝ) < x := by linarith
      have hx1' : x < 1 := by linarith
      have hgt :=
        varianceIntegrand_pos_aux α θ₁ θ₂ x hx0 hx1' (havoid x ⟨hx1, hx2⟩)
      exact Function.mem_support.mpr hgt.ne'
    · constructor <;> linarith
  have hJpos : 0 < MeasureTheory.volume (Set.Ioo lo hi) :=
    (MeasureTheory.Measure.measure_Ioo_pos MeasureTheory.volume).mpr hlt
  exact hJpos.trans_le (MeasureTheory.measure_mono hJ)

/-- Positivity of the stationary variance for positive mutation parameters:
the stationary law is non-degenerate. -/
theorem selectionMutationVariance_pos (α : ℝ) {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) : 0 < selectionMutationVariance α θ₁ θ₂ := by
  have hZpos := selectionMutationPartition_pos α hθ₁ hθ₂
  have hinteg : IntervalIntegrable
      (fun x : ℝ => (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
        selectionMutationSpeedDensity α θ₁ θ₂ x)
      MeasureTheory.volume 0 1 := by
    have hw : ContinuousOn
        (fun x : ℝ => (x - selectionMutationMean α θ₁ θ₂) ^ 2)
        (Set.uIcc 0 1) := by
      have hsub : ContinuousOn
          (fun x : ℝ => x - selectionMutationMean α θ₁ θ₂)
          (Set.uIcc 0 1) :=
        continuousOn_id.sub continuousOn_const
      have hmul : ContinuousOn
          (fun x : ℝ => (x - selectionMutationMean α θ₁ θ₂) *
            (x - selectionMutationMean α θ₁ θ₂))
          (Set.uIcc 0 1) :=
        hsub.mul hsub
      simpa only [pow_two] using hmul
    exact (intervalIntegrable_selectionMutationSpeedDensity α hθ₁
      hθ₂).continuousOn_mul hw
  have hnonneg : Filter.Eventually
      (fun x : ℝ => 0 ≤ (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
        selectionMutationSpeedDensity α θ₁ θ₂ x)
      (MeasureTheory.ae
        (MeasureTheory.volume.restrict (Set.uIoc 0 1))) := by
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    exact mul_nonneg (sq_nonneg _)
      (selectionSpeedDensity_nonneg_aux α θ₁ θ₂ x hx0.le hx1)
  have hpos : 0 < ∫ x in (0 : ℝ)..1,
      (x - selectionMutationMean α θ₁ θ₂) ^ 2 *
        selectionMutationSpeedDensity α θ₁ θ₂ x := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonneg
      hinteg]
    constructor
    · norm_num
    · by_cases hμ : selectionMutationMean α θ₁ θ₂ ≤ 1 / 2
      · exact support_pos_of_Ioo_aux α θ₁ θ₂ (3 / 4) (7 / 8) (by norm_num)
          (by norm_num) (by norm_num) (fun x hx => by
            obtain ⟨hx1, hx2⟩ := hx
            linarith [hμ])
      · have hμ' : 1 / 2 < selectionMutationMean α θ₁ θ₂ :=
          lt_of_not_ge hμ
        exact support_pos_of_Ioo_aux α θ₁ θ₂ (1 / 8) (1 / 4) (by norm_num)
          (by norm_num) (by norm_num) (fun x hx => by
            obtain ⟨hx1, hx2⟩ := hx
            linarith [hμ'])
  unfold selectionMutationVariance
  exact div_pos hpos hZpos

/-- For positive mutation parameters, the stationary mean is strictly increasing in the
selection parameter. -/
theorem strictMono_selectionMutationMean {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁)
    (hθ₂ : 0 < θ₂) : StrictMono (fun α => selectionMutationMean α θ₁ θ₂) := by
  refine strictMono_of_hasDerivAt_pos
    (fun α => hasDerivAt_selectionMutationMean α hθ₁ hθ₂) fun α => ?_
  show 0 < 2 * selectionMutationVariance α θ₁ θ₂
  exact mul_pos (by norm_num) (selectionMutationVariance_pos α hθ₁ hθ₂)

end MathlibExt.Biology.PopulationGenetics.Diffusion

end
