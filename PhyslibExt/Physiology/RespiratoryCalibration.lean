/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Respiratory calibration design

## i. Overview

For the two-column design with columns given by the sampled volume
derivative and volume, proportional columns make the calibration
parameters non-identifiable: shifting `(R, E)` by `(s, -c * s)`
leaves every sampled datum unchanged.

## ii. Key results

* `resp_proportional_same_data`: proportional columns give the
  same sampled data for the shifted parameter pair.
* `resp_proportional_not_injective`: the calibration map is not
  injective on any admissible domain containing both pairs.

## iii. Table of contents

* A. Proportional-column non-identification.

## iv. References

* The two-column design is the fixed sampled design of the
  respiratory calibration model; no dynamic trajectory assumption
  is used.
-/

@[expose] public section

/-! ## A. Proportional-column non-identification. -/

namespace PhyslibExt.Physiology.RespiratoryCalibration

/-- **Proportional design columns give the same calibration data.**
For the two-column design with columns `vp` and `v`, if
`vp j = c * v j` for every sample `j`, then the parameter pairs
`(R, E)` and `(R + s, E - c * s)` produce identical data at every
sample. -/
lemma resp_proportional_same_data {ι : Type*} (vp v : ι → ℝ)
    (c R E s : ℝ) (hprop : ∀ j, vp j = c * v j) (j : ι) :
    vp j * (R + s) + v j * (E - c * s) = vp j * R + v j * E := by
  rw [hprop j, mul_add, mul_sub]
  have hcs : c * v j * s = v j * (c * s) := by
    rw [mul_assoc, mul_comm (v j) s, ← mul_assoc, mul_comm (c * s) (v j)]
  rw [hcs, add_assoc, add_comm (v j * (c * s)) _, sub_add_cancel]

/-- **Proportional columns are not identified on a domain
containing both pairs.** Under the same proportionality, if both
parameter pairs lie in the admissible domain and `s ≠ 0`, the
calibration map `(R, E) ↦ fun j => vp j * R + v j * E` is not
injective on that domain. -/
lemma resp_proportional_not_injective {ι : Type*} (vp v : ι → ℝ)
    (c R E s : ℝ) (hprop : ∀ j, vp j = c * v j) (hs : s ≠ 0)
    (D : Set (ℝ × ℝ)) (h1 : (R, E) ∈ D) (h2 : (R + s, E - c * s) ∈ D) :
    ¬ Set.InjOn (fun p : ℝ × ℝ => fun j => vp j * p.1 + v j * p.2) D := by
  intro hinj
  have hfun : (fun j => vp j * R + v j * E)
      = (fun j => vp j * (R + s) + v j * (E - c * s)) := by
    funext j
    exact (resp_proportional_same_data vp v c R E s hprop j).symm
  have heq : (R, E) = (R + s, E - c * s) := hinj h1 h2 hfun
  have hR : R = R + s := congrArg Prod.fst heq
  have hRs : R + s = R + 0 := by rw [← hR, add_zero]
  have hs0 : s = 0 := add_left_cancel hRs
  exact hs hs0


end PhyslibExt.Physiology.RespiratoryCalibration
