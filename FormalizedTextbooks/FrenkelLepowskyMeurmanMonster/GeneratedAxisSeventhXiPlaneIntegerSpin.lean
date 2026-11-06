/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinXi

/-! An exact one-Gaussian integer numerator for the original corrected Xi spin action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- The compact actual relabeling and quadratic sign acting on integer spin vectors. -/
def generatedSeventhXiPlaneIntegerCompact (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun d =>
    let t := generatedSeventhXiPlaneCode.symm (golayLabelCoefficients d)
    nortonUIntegerSign (monsterMonomialQuadratic generatedSeventhXiPlanePhase t) *
      v (nortonUIntegerLabel t)

/-- Its actual inverse applies the same diagonal sign before the forward label map. -/
def generatedSeventhXiPlaneIntegerCompactInverse (v : NortonUIntegerVector) :
    NortonUIntegerVector := fun d =>
  let t := golayLabelCoefficients d
  nortonUIntegerSign (monsterMonomialQuadratic generatedSeventhXiPlanePhase t) *
    v (nortonUIntegerLabel (generatedSeventhXiPlaneCode t))

/-- The compact integer map is the exact real operator on every integer vector. -/
theorem generatedSeventhXiPlane_integer_compact_embed (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneCompactSpin.val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedSeventhXiPlaneIntegerCompact v) := by
  funext t
  change qSign (monsterMonomialQuadratic generatedSeventhXiPlanePhase
      (generatedSeventhXiPlaneCode.symm t)) *
    nortonUIntegerEmbed v (generatedSeventhXiPlaneCode.symm t) = _
  simp only [nortonUIntegerEmbed, generatedSeventhXiPlaneIntegerCompact,
    nortonUIntegerLabel_inverse, Int.cast_mul, nortonUIntegerSign_real]

/-- The inverse integer map is also the exact full source inverse operator. -/
theorem generatedSeventhXiPlane_integer_compact_inverse_embed (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneCompactSpin.val.symm (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedSeventhXiPlaneIntegerCompactInverse v) := by
  funext t
  change qSign (monsterMonomialQuadratic generatedSeventhXiPlanePhase t) *
    nortonUIntegerEmbed v (generatedSeventhXiPlaneCode t) = _
  simp only [nortonUIntegerEmbed, generatedSeventhXiPlaneIntegerCompactInverse,
    nortonUIntegerLabel_inverse, Int.cast_mul, nortonUIntegerSign_real]

/-- The numerator retains the genuine Pauli correction after one original translation Gaussian. -/
def generatedSeventhXiPlaneIntegerSpin (v : NortonUIntegerVector) : NortonUIntegerVector :=
  nortonUIntegerQ generatedSeventhXiPlaneCorrection
    (generatedSeventhXiPlaneIntegerCompact
      (nortonUIntegerXi (generatedSeventhXiPlaneIntegerCompactInverse v)))

private theorem spin_mul_apply (a b : SpinHolomorph) (x : SpinSpace) :
    (a * b).val x = a.val (b.val x) := rfl

private theorem spin_inv_apply (a : SpinHolomorph) (x : SpinSpace) :
    (a⁻¹).val x = a.val.symm x := rfl

/-- This complete integer numerator, divided by eight, is the original corrected spin lift. -/
theorem generatedSeventhXiPlane_integer_spin_embed (v : NortonUIntegerVector) :
    generatedSeventhXiPlaneFiber.val.1.val (nortonUIntegerEmbed v) =
      (1 / 8 : ℝ) • nortonUIntegerEmbed (generatedSeventhXiPlaneIntegerSpin v) := by
  have h := congrArg (fun s : SpinHolomorph => s.val (nortonUIntegerEmbed v))
    generatedSeventhXiPlaneFiber_spin
  simp only [spin_mul_apply, spin_inv_apply] at h
  refine h.trans ?_
  rw [generatedSeventhXiPlane_integer_compact_inverse_embed,
    nortonUIntegerXi_embed, map_smul, generatedSeventhXiPlane_integer_compact_embed,
    map_smul]
  have hq : (spinHolomorphIncl generatedSeventhXiPlaneCorrection).val
      (nortonUIntegerEmbed (generatedSeventhXiPlaneIntegerCompact
        (nortonUIntegerXi (generatedSeventhXiPlaneIntegerCompactInverse v)))) =
      nortonUIntegerEmbed (generatedSeventhXiPlaneIntegerSpin v) :=
    nortonUIntegerQ_embed _ _
  rw [hq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
