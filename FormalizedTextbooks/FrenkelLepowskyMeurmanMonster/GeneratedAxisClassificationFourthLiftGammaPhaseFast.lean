/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftGauss

/-! Sparse evaluation of the exact actual grey Gaussian diagonal quadratic phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual grey cocode frame written as its finite binary coefficient matrix. -/
def generatedFourthLiftCocodeFrame : Fin 6 → Fin 12 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1]]

/-- Every frame coordinate is checked against the genuine actual cocode basis. -/
theorem generatedFourth_lift_cocode_frame : xiGrayCocodeBasis =
    generatedFourthLiftCocodeFrame := by decide +kernel

/-- The actual Gaussian diagonal phase has just these eight nonzero monomials. -/
def generatedFourthLiftGammaPhaseFast (t : SpinIndex) : ZMod 2 :=
  t 11 + t 0 * t 1 + t 0 * t 2 + t 0 * t 3 +
    t 1 * t 2 + t 1 * t 3 + t 2 * t 3 + t 10 * t 11

/-- Sparse phase evaluation agrees with the entire actual grey projection and quadratic form. -/
theorem generatedFourth_lift_gamma_phase_fast (t : SpinIndex) :
    xiGrayQuadratic (xiGrayDual (fun i => spinDot (xiGrayCocodeBasis i) t)) =
      generatedFourthLiftGammaPhaseFast t := by
  rw [generatedFourth_lift_cocode_frame]
  have hs : ∀ c : ZMod 2, c ^ 2 = c := by decide +kernel
  simp [xiGrayQuadratic, xiGrayDual, spinDot, generatedFourthLiftCocodeFrame,
    generatedFourthLiftGammaPhaseFast, Finset.sum_filter, Fin.sum_univ_succ]
  ring_nf
  simp only [hs]
  simp only [show (166 : ZMod 2) = 0 from by decide,
    show (333 : ZMod 2) = 1 from by decide, show (416 : ZMod 2) = 0 from by decide,
    show (500 : ZMod 2) = 0 from by decide, show (625 : ZMod 2) = 1 from by decide,
    show (260 : ZMod 2) = 0 from by decide, show (375 : ZMod 2) = 1 from by decide,
    mul_zero, mul_one, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
