/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact phase cancellation for Norton's initial code point and actual dictionary triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual X-row sign of the x400 source code. -/
noncomputable def monsterNortonInitialXSign (d : Fin 2048) (i : Fin 24) : ℝ :=
  qSign (spinDot monsterNortonInitialCode (sourceWordTheta ⟨d.val, by omega⟩) +
    spinDot (golayLabelCoefficients ⟨d.val, by omega⟩)
      (sourceCodeThetaPolynomial monsterNortonInitialCode) +
        golayEncoder monsterNortonInitialCode i)

/-- The actual Y-row translation sign. -/
noncomputable def monsterNortonInitialYSign (d : Fin 2048) (i : Fin 24) : ℝ :=
  qSign (golayEncoder monsterNortonInitialCode i) *
    qSign (spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
      (golayLabelCoefficients ⟨d.val, by omega⟩))

/-- The actual Z-row translation sign, including both quarter weights. -/
noncomputable def monsterNortonInitialZSign (d : Fin 2048) : ℝ :=
  qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
    qSign (spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    qSign (golayMaskWeight (golayEncodedMask (monsterNortonInitialCodeSum d).val) / 4 : ℕ)

/-- Translation by the even code x400 is an involution on the lower code labels. -/
theorem monsterNortonInitialCodeSum_twice (d : Fin 2048) :
    monsterNortonInitialCodeSum (monsterNortonInitialCodeSum d) = d := by
  have h : golayLabelCoefficients
      ⟨(monsterNortonInitialCodeSum (monsterNortonInitialCodeSum d)).val, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ := by
    rw [monsterNortonInitialCodeSum_low, monsterNortonInitialCodeSum_low]
    funext i
    change (golayLabelCoefficients ⟨d.val, by omega⟩ i + monsterNortonInitialCode i) +
      monsterNortonInitialCode i = golayLabelCoefficients ⟨d.val, by omega⟩ i
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have he := golayLabelCoefficients_injective h
  apply Fin.ext
  exact congrArg (fun x : Fin 4096 => x.val) he

/-- The source theta character of x400 is fixed by its own code translation. -/
theorem monsterNortonInitial_theta_sum (d : Fin 2048) :
    spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
      (golayLabelCoefficients ⟨(monsterNortonInitialCodeSum d).val, by omega⟩) =
    spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
      (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [monsterNortonInitialCodeSum_low, spinDot_add_right]
  have hz : spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
      monsterNortonInitialCode = 0 := by
    have h := sourceCodeThetaPolynomial_self_dot 1024
    have hw : ((golayMaskWeight (golayEncodedMask 1024) / 4 : ℕ) : ZMod 2) = 0 := by
      decide +kernel
    exact h.trans hw
  rw [hz, add_zero]

/-- The Y sign is constant on the two translated labels. -/
theorem monsterNortonInitialYSign_sum (d : Fin 2048) (i : Fin 24) :
    monsterNortonInitialYSign (monsterNortonInitialCodeSum d) i =
      monsterNortonInitialYSign d i := by
  unfold monsterNortonInitialYSign
  rw [monsterNortonInitial_theta_sum]

/-- The Z sign is constant on the same pair of labels. -/
theorem monsterNortonInitialZSign_sum (d : Fin 2048) :
    monsterNortonInitialZSign (monsterNortonInitialCodeSum d) =
      monsterNortonInitialZSign d := by
  unfold monsterNortonInitialZSign
  rw [monsterNortonInitialCodeSum_twice, monsterNortonInitial_theta_sum]
  ring

/-- Parker polarization removes precisely the two quarter-weight corrections. -/
theorem monsterNortonInitial_Z_phase (d : Fin 2048) :
    ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) +
      spinDot (sourceWordTheta 1024) (golayLabelCoefficients ⟨d.val, by omega⟩) +
      ((golayMaskWeight (golayEncodedMask (monsterNortonInitialCodeSum d).val) / 4 : ℕ) :
        ZMod 2) = spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterNortonInitialCode := by
  have h := sourceWordTheta_cross_dot ⟨d.val, by omega⟩ 1024
    ⟨(monsterNortonInitialCodeSum d).val, by omega⟩ (monsterNortonInitialCodeSum_low d)
  have hw : ((golayMaskWeight (golayEncodedMask 1024) / 4 : ℕ) : ZMod 2) = 0 := by
    decide +kernel
  change spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterNortonInitialCode +
      spinDot (sourceWordTheta 1024) (golayLabelCoefficients ⟨d.val, by omega⟩) =
    (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
      (golayMaskWeight (golayEncodedMask 1024) / 4 : ℕ) -
      (golayMaskWeight (golayEncodedMask (monsterNortonInitialCodeSum d).val) / 4 : ℕ) at h
  rw [hw, add_zero] at h
  change _ = spinDot (sourceWordTheta ⟨d.val, by omega⟩) (golayLabelCoefficients 1024)
  unfold monsterNortonInitialCode at h
  linear_combination (norm := skip) h
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, sub_zero]

/-- The Z sign is exactly the complementary source theta character. -/
theorem monsterNortonInitialZSign_eq (d : Fin 2048) :
    monsterNortonInitialZSign d =
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩) monsterNortonInitialCode) := by
  unfold monsterNortonInitialZSign
  unfold monsterNortonInitialCode
  rw [← sourceWordTheta_eq_polynomial, ← qSign_add, ← qSign_add]
  exact congrArg qSign (monsterNortonInitial_Z_phase d)


/-- The three source row signs cancel: the X sign is the product of the Y and Z signs. -/
theorem monsterNortonInitialXSign_eq (d : Fin 2048) (i : Fin 24) :
    monsterNortonInitialXSign d i =
      monsterNortonInitialYSign d i * monsterNortonInitialZSign d := by
  rw [monsterNortonInitialZSign_eq]
  unfold monsterNortonInitialXSign monsterNortonInitialYSign
  simp only [qSign_add]
  rw [spinDot_comm monsterNortonInitialCode
      (sourceWordTheta ⟨d.val, by omega⟩),
    spinDot_comm (golayLabelCoefficients ⟨d.val, by omega⟩)
      (sourceCodeThetaPolynomial monsterNortonInitialCode)]
  ring

/-- The X sign is also constant on the translated pair. -/
theorem monsterNortonInitialXSign_sum (d : Fin 2048) (i : Fin 24) :
    monsterNortonInitialXSign (monsterNortonInitialCodeSum d) i =
      monsterNortonInitialXSign d i := by
  rw [monsterNortonInitialXSign_eq, monsterNortonInitialXSign_eq,
    monsterNortonInitialYSign_sum, monsterNortonInitialZSign_sum]

/-- Every Y row coefficient has square one. -/
theorem monsterNortonInitialYSign_square (d : Fin 2048) (i : Fin 24) :
    monsterNortonInitialYSign d i * monsterNortonInitialYSign d i = 1 := by
  unfold monsterNortonInitialYSign
  have h₁ := qSign_sq (golayEncoder monsterNortonInitialCode i)
  have h₂ := qSign_sq (spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
    (golayLabelCoefficients ⟨d.val, by omega⟩))
  calc
    _ = (qSign (golayEncoder monsterNortonInitialCode i) *
      qSign (golayEncoder monsterNortonInitialCode i)) *
      (qSign (spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
        (golayLabelCoefficients ⟨d.val, by omega⟩)) *
      qSign (spinDot (sourceCodeThetaPolynomial monsterNortonInitialCode)
        (golayLabelCoefficients ⟨d.val, by omega⟩))) := by ring
    _ = 1 := by rw [h₁, h₂, one_mul]

/-- Every Z row coefficient has square one. -/
theorem monsterNortonInitialZSign_square (d : Fin 2048) :
    monsterNortonInitialZSign d * monsterNortonInitialZSign d = 1 := by
  rw [monsterNortonInitialZSign_eq]
  exact qSign_sq _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
