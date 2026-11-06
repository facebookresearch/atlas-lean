/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact phase cancellation for even source-code points and actual dictionary triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCodeTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
variable (a : Fin 2048)
variable (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0)

/-- The actual X-row sign of the the given code source code. -/
noncomputable def monsterNortonEvenXSign (d : Fin 2048) (i : Fin 24) : ℝ :=
  qSign (spinDot (monsterNortonEvenCodeVector a) (sourceWordTheta ⟨d.val, by omega⟩) +
    spinDot (golayLabelCoefficients ⟨d.val, by omega⟩)
      (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a)) +
        golayEncoder (monsterNortonEvenCodeVector a) i)

/-- The actual Y-row translation sign. -/
noncomputable def monsterNortonEvenYSign (d : Fin 2048) (i : Fin 24) : ℝ :=
  qSign (golayEncoder (monsterNortonEvenCodeVector a) i) *
    qSign (spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨d.val, by omega⟩))

/-- The actual Z-row translation sign, including both quarter weights. -/
noncomputable def monsterNortonEvenZSign (d : Fin 2048) : ℝ :=
  qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
    qSign (spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨d.val, by omega⟩)) *
    qSign (golayMaskWeight (golayEncodedMask ((monsterNortonEvenCodeSum a) d).val) / 4 : ℕ)

/-- Translation by the even code the given code is an involution on the lower code labels. -/
theorem monsterNortonEvenCodeSum_twice (d : Fin 2048) :
    (monsterNortonEvenCodeSum a) ((monsterNortonEvenCodeSum a) d) = d := by
  have h : golayLabelCoefficients
      ⟨((monsterNortonEvenCodeSum a) ((monsterNortonEvenCodeSum a) d)).val, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ := by
    rw [(monsterNortonEvenCodeSum_low a), (monsterNortonEvenCodeSum_low a)]
    funext i
    change (golayLabelCoefficients ⟨d.val, by omega⟩ i + (monsterNortonEvenCodeVector a) i) +
      (monsterNortonEvenCodeVector a) i = golayLabelCoefficients ⟨d.val, by omega⟩ i
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have he := golayLabelCoefficients_injective h
  apply Fin.ext
  exact congrArg (fun x : Fin 4096 => x.val) he

/-- The source theta character of the given code is fixed by its own code translation. -/
theorem monsterNortonEven_theta_sum
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) :
    spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨((monsterNortonEvenCodeSum a) d).val, by omega⟩) =
    spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (golayLabelCoefficients ⟨d.val, by omega⟩) := by
  rw [(monsterNortonEvenCodeSum_low a), spinDot_add_right]
  have hz : spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
      (monsterNortonEvenCodeVector a) = 0 := by
    have h := sourceCodeThetaPolynomial_self_dot ⟨a.val, by omega⟩
    have hw : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0 := by
      exact ha
    exact h.trans hw
  rw [hz, add_zero]

/-- The Y sign is constant on the two translated labels. -/
theorem monsterNortonEvenYSign_sum
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) (i :
      Fin 24) :
    (monsterNortonEvenYSign a) ((monsterNortonEvenCodeSum a) d) i =
      (monsterNortonEvenYSign a) d i := by
  unfold monsterNortonEvenYSign
  rw [(monsterNortonEven_theta_sum a ha)]

/-- The Z sign is constant on the same pair of labels. -/
theorem monsterNortonEvenZSign_sum
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) :
    (monsterNortonEvenZSign a) ((monsterNortonEvenCodeSum a) d) =
      (monsterNortonEvenZSign a) d := by
  unfold monsterNortonEvenZSign
  rw [(monsterNortonEvenCodeSum_twice a), (monsterNortonEven_theta_sum a ha)]
  ring

/-- Parker polarization removes precisely the two quarter-weight corrections. -/
theorem monsterNortonEven_Z_phase
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) :
    ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) +
      spinDot (sourceWordTheta ⟨a.val, by omega⟩) (golayLabelCoefficients ⟨d.val, by omega⟩) +
      ((golayMaskWeight (golayEncodedMask ((monsterNortonEvenCodeSum a) d).val) / 4 : ℕ) :
        ZMod 2) = spinDot (sourceWordTheta ⟨d.val, by omega⟩) (monsterNortonEvenCodeVector a) := by
  have h := sourceWordTheta_cross_dot ⟨d.val, by omega⟩ ⟨a.val, by omega⟩
    ⟨((monsterNortonEvenCodeSum a) d).val, by omega⟩ ((monsterNortonEvenCodeSum_low a) d)
  have hw : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0 := by
    exact ha
  change spinDot (sourceWordTheta ⟨d.val, by omega⟩) (monsterNortonEvenCodeVector a) +
      spinDot (sourceWordTheta ⟨a.val, by omega⟩) (golayLabelCoefficients ⟨d.val, by omega⟩) =
    (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
      (golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) -
      (golayMaskWeight (golayEncodedMask ((monsterNortonEvenCodeSum a) d).val) / 4 : ℕ) at h
  rw [hw, add_zero] at h
  change _ = spinDot (sourceWordTheta ⟨d.val, by omega⟩) (golayLabelCoefficients ⟨a.val, by omega⟩)
  unfold monsterNortonEvenCodeVector at h
  linear_combination (norm := skip) h
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, sub_zero]

/-- The Z sign is exactly the complementary source theta character. -/
theorem monsterNortonEvenZSign_eq
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) :
    (monsterNortonEvenZSign a) d =
      qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩) (monsterNortonEvenCodeVector a)) := by
  unfold monsterNortonEvenZSign
  unfold monsterNortonEvenCodeVector
  rw [← sourceWordTheta_eq_polynomial, ← qSign_add, ← qSign_add]
  exact congrArg qSign ((monsterNortonEven_Z_phase a ha) d)


/-- The three source row signs cancel: the X sign is the product of the Y and Z signs. -/
theorem monsterNortonEvenXSign_eq
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) (i :
      Fin 24) :
    (monsterNortonEvenXSign a) d i =
      (monsterNortonEvenYSign a) d i * (monsterNortonEvenZSign a) d := by
  rw [(monsterNortonEvenZSign_eq a ha)]
  unfold monsterNortonEvenXSign monsterNortonEvenYSign
  simp only [qSign_add]
  rw [spinDot_comm (monsterNortonEvenCodeVector a)
      (sourceWordTheta ⟨d.val, by omega⟩),
    spinDot_comm (golayLabelCoefficients ⟨d.val, by omega⟩)
      (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))]
  ring

/-- The X sign is also constant on the translated pair. -/
theorem monsterNortonEvenXSign_sum
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) (i :
      Fin 24) :
    (monsterNortonEvenXSign a) ((monsterNortonEvenCodeSum a) d) i =
      (monsterNortonEvenXSign a) d i := by
  rw [(monsterNortonEvenXSign_eq a ha), (monsterNortonEvenXSign_eq a ha),
    (monsterNortonEvenYSign_sum a ha), (monsterNortonEvenZSign_sum a ha)]

/-- Every Y row coefficient has square one. -/
theorem monsterNortonEvenYSign_square (d : Fin 2048) (i : Fin 24) :
    (monsterNortonEvenYSign a) d i * (monsterNortonEvenYSign a) d i = 1 := by
  unfold monsterNortonEvenYSign
  have h₁ := qSign_sq (golayEncoder (monsterNortonEvenCodeVector a) i)
  have h₂ := qSign_sq (spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
    (golayLabelCoefficients ⟨d.val, by omega⟩))
  calc
    _ = (qSign (golayEncoder (monsterNortonEvenCodeVector a) i) *
      qSign (golayEncoder (monsterNortonEvenCodeVector a) i)) *
      (qSign (spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
        (golayLabelCoefficients ⟨d.val, by omega⟩)) *
      qSign (spinDot (sourceCodeThetaPolynomial (monsterNortonEvenCodeVector a))
        (golayLabelCoefficients ⟨d.val, by omega⟩))) := by ring
    _ = 1 := by rw [h₁, h₂, one_mul]

/-- Every Z row coefficient has square one. -/
theorem monsterNortonEvenZSign_square
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (d : Fin 2048) :
    (monsterNortonEvenZSign a) d * (monsterNortonEvenZSign a) d = 1 := by
  rw [(monsterNortonEvenZSign_eq a ha)]
  exact qSign_sq _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
