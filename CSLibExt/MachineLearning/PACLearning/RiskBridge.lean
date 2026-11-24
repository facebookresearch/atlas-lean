/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.FiniteClass
public import Cslib.MachineLearning.PACLearning.VersionSpace

/-!
# Bridge: the risk of the 0-1 loss is CSLib's error

The generalization-bound files state their results for an abstract bounded loss `L f z`, with
the expected risk `risk L ν f = ∫ L f z dν` and the empirical risk
`empiricalRisk L z f = (1/n) ∑ᵢ L f (zᵢ)` (F. Bach, *Learning Theory from First Principles*,
MIT Press (2024), Definitions 2.1 and 2.2). CSLib's PAC library instead uses the 0-1 `error` of a
hypothesis under a joint distribution and the `empiricalMiscount` on a labelled sample. For the
0-1 loss the two coincide:

* `risk_zeroOneLoss_eq_toReal_error`: `risk zeroOneLoss D h = (error D h).toReal`;
* `empiricalRisk_zeroOneLoss_eq_miscount_div`: `empiricalRisk zeroOneLoss S h` is the number of
  sample points `h` gets wrong divided by the sample size.

So the finite-class uniform-deviation bound applies to CSLib's error with `ℓ∞ = 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open CSLibExt.MachineLearning.GeneralizationBounds (risk empiricalRisk)

variable {X Y : Type*}

/-- **The 0-1 loss as an abstract loss.** The loss of hypothesis `h` at the labelled example
`z = (x, y)` is `1` if `h x ≠ y` and `0` otherwise, in the form `L h z` used by the
generalization-bound files (F. Bach, *Learning Theory from First Principles*, MIT Press (2024),
Section 2.1). -/
noncomputable def zeroOneLoss (h : X → Y) (z : X × Y) : ℝ :=
  {p : X × Y | h p.1 ≠ p.2}.indicator (fun _ => 1) z

/-- **The risk of the 0-1 loss is CSLib's error.** For a probability distribution `D` on labelled
examples and a hypothesis `h` whose disagreement set is measurable, the expected 0-1 risk of `h`
is the real number `error D h`. -/
theorem risk_zeroOneLoss_eq_toReal_error [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (h : X → Y)
    (hmeas : MeasurableSet {p : X × Y | h p.1 ≠ p.2}) :
    risk zeroOneLoss D h = (error D h).toReal := by
  simp only [risk, zeroOneLoss]
  rw [integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one, measureReal_def, error]

/-- **The empirical risk of the 0-1 loss is the miscount over the sample size.** On a labelled
sample `S` of size `n`, the empirical 0-1 risk of `h` is CSLib's `empiricalMiscount h S`, the
number of sample points where `h` errs, divided by `n`. -/
theorem empiricalRisk_zeroOneLoss_eq_miscount_div [DecidableEq Y] {n : ℕ} [NeZero n]
    (S : LabeledSample X Y n) (h : X → Y) :
    empiricalRisk zeroOneLoss S h = (empiricalMiscount h S : ℝ) / n := by
  classical
  simp only [empiricalRisk, zeroOneLoss, empiricalMiscount, Set.indicator_apply,
    Set.mem_ofPred_eq]
  rw [Finset.sum_boole]
  simp [div_eq_inv_mul]

end Cslib.MachineLearning.PACLearning
