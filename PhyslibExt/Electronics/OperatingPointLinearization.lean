/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import PhyslibExt.Chemistry.Uncertainty.Propagation
import PhyslibExt.Statistics.UncertaintyPropagation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Operating-point linearization (small-signal model)

## i. Overview

The small-signal model of a smooth device law `f` at an operating
point: the remainder of the first-order Taylor approximation is
bounded by half the second-derivative bound times the square of
the deviation, on any segment where the stated bound on the
second derivative (in the Pi sup norm, not an Euclidean Hessian
norm) holds. The bound is attained by a quadratic device law, so
the constant `1/2` is exact. Piecewise device laws inherit nothing
here: each lemma uses exactly the smoothness it states, and the
second-derivative bound itself is only evaluated on the box or
segment in question.

## ii. Key results

- `smallSignal_remainder_le_of_hessian_bound`: the remainder
  bound from a Hessian operator bound on an operating box
  (wrapper around
  `Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le`).
- `smallSignal_remainder_le_of_segment_bound`: the same bound
  from a second-derivative bound on the segment pullback
  (wrapper around
  `Statistics.UncertaintyPropagation.taylor_first_order_bound`).
- `smallSignal_quadratic_attains_factor` and
  `smallSignal_quadratic_attains_bound`: a quadratic law attains
  the factor `1/2`, so it cannot be improved in general.

## iii. Table of contents

- A. The small-signal remainder bound

## iv. References

- A. S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: small-signal models of
  nonlinear devices at an operating point and the quadratic
  remainder of the linearization.

## A. The small-signal remainder bound
-/

@[expose] public section

namespace PhyslibExt.Electronics.OperatingPointLinearization

/-- The one-dimensional segment pullback of the device law along the
perturbation: `g t = i (v0 + t • dv)`, the leaf's `t -> i(v0+t*dv)`. -/
def segmentPullback {n : ℕ} (i : (Fin n → ℝ) → ℝ) (v0 dv : Fin n → ℝ) (t : ℝ) : ℝ :=
  i (v0 + t • dv)

/-- Small-signal remainder of the device law at the operating point `v0`
for perturbation `dv`: `r = i (v0 + dv) - i v0 - Di(v0)[dv]`, where
`Di(v0)[dv]` is `fderiv ℝ i v0 dv`. -/
noncomputable def smallSignalRemainder {n : ℕ} (i : (Fin n → ℝ) → ℝ) (v0 dv : Fin n → ℝ) : ℝ :=
  i (v0 + dv) - i v0 - fderiv ℝ i v0 dv

/-- Box form: with `i` of class `C²` on an open operating regime `U`
containing the box `Set.Icc lo hi` and sup-norm Hessian bound
`‖fderiv ℝ (fderiv ℝ i) y‖ <= M` on the box, the small-signal remainder
satisfies `|r| <= M * ‖dv‖^2 / 2` (Pi sup norm) for `v0, v0 + dv` in the box.
This is the one-dimensional Taylor remainder bound applied along the
segment `v0 + t • dv`. -/
lemma smallSignal_remainder_le_of_hessian_bound {n : ℕ}
    (i : (Fin n → ℝ) → ℝ) (M : ℝ) (lo hi v0 dv : Fin n → ℝ)
    (U : Set (Fin n → ℝ)) (hU : IsOpen U) (hbox : Set.Icc lo hi ⊆ U)
    (hC2 : ContDiffOn ℝ 2 i U)
    (hM : ∀ y ∈ Set.Icc lo hi, ‖fderiv ℝ (fderiv ℝ i) y‖ ≤ M)
    (hv0 : v0 ∈ Set.Icc lo hi) (hvdv : v0 + dv ∈ Set.Icc lo hi) :
    |smallSignalRemainder i v0 dv| ≤ M * ‖dv‖ ^ 2 / 2  := by
  unfold smallSignalRemainder
  refine le_trans
    (Chemistry.Uncertainty.measurementFunction_firstOrder_remainder_le
      hU hbox hC2 hM hv0 hvdv) (le_of_eq (by ring))

/-- Segment form: if `i` is differentiable at `v0`, the pullback
`g t = i (v0 + t • dv)` is `C²` on `ℝ`, and the second-derivative
bound `|g'' t| <= M * ‖dv‖^2` holds on `[0,1]` (sup norm), then
`|r| <= M * ‖dv‖^2 / 2`. No box or global `C²` hypothesis on `i`
itself; only the bound, not the smoothness, is segment-local. -/
lemma smallSignal_remainder_le_of_segment_bound {n : ℕ}
    (i : (Fin n → ℝ) → ℝ) (v0 dv : Fin n → ℝ) (M : ℝ)
    (hdiff : DifferentiableAt ℝ i v0)
    (hC2 : ContDiff ℝ 2 (fun t : ℝ => i (v0 + t • dv)))
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun t : ℝ => i (v0 + t • dv))) t| ≤ M * ‖dv‖ ^ 2) :
    |smallSignalRemainder i v0 dv| ≤ M * ‖dv‖ ^ 2 / 2 := by
  have hmain := Statistics.UncertaintyPropagation.taylor_first_order_bound
    hC2 hseg (x := 0) (δ := 1)
    (Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩)
    (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have hg1 : (fun t : ℝ => i (v0 + t • dv)) 1 = i (v0 + dv) := by simp
  have hg0 : (fun t : ℝ => i (v0 + t • dv)) 0 = i v0 := by simp
  have hchain : deriv (fun t : ℝ => i (v0 + t • dv)) 0 = fderiv ℝ i v0 dv := by
    have h0 : (fun t : ℝ => v0 + t • dv) 0 = v0 := by simp
    have hfi : HasFDerivAt i (fderiv ℝ i v0) ((fun t : ℝ => v0 + t • dv) 0) := by
      rw [h0]
      exact hdiff.hasFDerivAt
    have hid : HasDerivAt (fun t : ℝ => t) 1 (0 : ℝ) := hasDerivAt_id' 0
    have hsm : HasDerivAt (fun t : ℝ => t • dv) dv 0 := by
      have h := hid.smul_const dv
      rwa [one_smul] at h
    have hinner : HasDerivAt (fun t : ℝ => v0 + t • dv) dv 0 := hsm.const_add v0
    have hcomp : HasDerivAt (i ∘ fun t : ℝ => v0 + t • dv)
        ((fderiv ℝ i v0) dv) 0 :=
      HasFDerivAt.comp_hasDerivAt (0 : ℝ) hfi hinner
    exact hcomp.deriv
  have hr : smallSignalRemainder i v0 dv
      = (fun t : ℝ => i (v0 + t • dv)) 1 - (fun t : ℝ => i (v0 + t • dv)) 0
        - deriv (fun t : ℝ => i (v0 + t • dv)) 0 := by
    unfold smallSignalRemainder
    rw [hg1, hg0, hchain]
  rw [hr]
  simpa using hmain

/-- Sharpness: the one-terminal square law at the origin attains the half
factor: its remainder at perturbation `a` is exactly `a ^ 2`, i.e. the
bound `M * ‖dv‖^2 / 2` with `M = 2` and `‖dv‖ = |a|` is an equality. -/
lemma smallSignal_quadratic_attains_factor (a : ℝ) :
    smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0 (fun _ => a)
      = a ^ 2 := by
  have hfd : fderiv ℝ (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0 = 0 := by
    have hproj : HasFDerivAt (fun v : Fin 1 → ℝ => v 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)) 0 :=
      ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1))
    have hmul := hproj.mul hproj
    simp only [Pi.zero_apply, zero_smul, add_zero] at hmul
    have hmul2 : HasFDerivAt (fun v : Fin 1 → ℝ => (v 0) ^ 2)
        (0 : (Fin 1 → ℝ) →L[ℝ] ℝ) 0 := by
      have hfun : (fun v : Fin 1 → ℝ => (v 0)^2)
          = (fun v : Fin 1 → ℝ => v 0) * (fun v : Fin 1 → ℝ => v 0) := by
        funext v
        simp [pow_two, Pi.mul_apply]
      rw [hfun]
      exact hmul
    exact hmul2.fderiv
  unfold smallSignalRemainder
  rw [hfd]
  simp

/-- Sharpness: for the square law the remainder attains the bound
with `M = 2` at every perturbation `a`, so the factor `1/2` in the
remainder bounds cannot be improved in general. -/
lemma smallSignal_quadratic_attains_bound (a : ℝ) :
    |smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0 (fun _ => a)|
      = 2 * ‖(fun _ => a : Fin 1 → ℝ)‖ ^ 2 / 2 := by
  rw [smallSignal_quadratic_attains_factor, abs_of_nonneg (sq_nonneg a)]
  have hnorm : ‖(fun _ => a : Fin 1 → ℝ)‖ = |a| := by
    rw [Pi.norm_def]
    simp
  rw [hnorm, sq_abs]
  ring

end PhyslibExt.Electronics.OperatingPointLinearization
