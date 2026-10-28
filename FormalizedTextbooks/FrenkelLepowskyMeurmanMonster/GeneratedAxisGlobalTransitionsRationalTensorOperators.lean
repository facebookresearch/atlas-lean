/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMonomialInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiExpansion

/-! Exact rational extensions of the original complete tensor operators. Each formula binds every physical coordinate; later sparse pairings evaluate only the needed coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Rational scaled coordinates in the original physical spin labels. -/
abbrev GeneratedAxisGlobalRationalTensor := Fin 4096 → Fin 24 → ℚ

/-- The genuine square-root normalization of an entire rational physical tensor. -/
def generatedAxisGlobalRationalTensorReal (T : GeneratedAxisGlobalRationalTensor) :
    SpinIndex → Fin 24 → ℝ :=
  fun t i => (T (generatedAxisGlobalSpinLabel t) i : ℝ) / Real.sqrt 2

/-- The exact original 64-by-four rational Xi coordinate formula. -/
def generatedAxisGlobalRationalTensorXi (T : GeneratedAxisGlobalRationalTensor)
    (k : Fin 4096) (i : Fin 24) : ℚ :=
  (∑ a : XiGrayIndex, ∑ b : Fin 4,
    (generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase a (golayLabelCoefficients k)) : ℚ) *
      (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℚ) *
        T (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + xiGrayCode a))
          (generatedAxisGlobalXiColumn i b)) / 16

/-- The exact full original source sign uses all four physical tensor inputs. -/
def generatedAxisGlobalRationalTensorSign (a : Fin 4096) (ε : ZMod 2)
    (T : GeneratedAxisGlobalRationalTensor) (k : Fin 4096) (i : Fin 24) : ℚ :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode a e
  ((generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℚ) *
    (generatedAxisGlobalCodeSign e i : ℚ) *
    (generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase a ε d e) : ℚ) *
    (generatedAxisGlobalCodeSign d i : ℚ) *
      (T (generatedAxisGlobalTensorLowLabel d) i - T (generatedAxisGlobalTensorHighLabel d) i) +
  (generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase a e i) : ℚ) *
    (T (generatedAxisGlobalTensorLowLabel e) i + T (generatedAxisGlobalTensorHighLabel e) i)) / 2

/-- The complete original signed monomial spin pullback and spatial permutation. -/
def generatedAxisGlobalRationalTensorMonomial (w : List (Fin 2 × Bool))
    (T : GeneratedAxisGlobalRationalTensor) (k : Fin 4096) (i : Fin 24) : ℚ :=
  let r := generatedFourthMonomialWordPull w (golayLabelCoefficients k)
  (generatedAxisGlobalIntSign r.1 : ℚ) * T (generatedAxisGlobalSpinLabel r.2)
    (((w.map generatedFourthMonomialPermutationLetter).prod).val.symm i)

/-- The entire rational Xi formula is exactly the original real tensor operator. -/
theorem generatedAxisGlobalRationalTensorXi_actual (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation xiSpinLocalFiber (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorXi T) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  calc
    _ = (16 * localTensorRepresentation xiSpinLocalFiber
        (generatedAxisGlobalRationalTensorReal T) (golayLabelCoefficients k) i) / 16 := by ring
    _ = (((∑ a : XiGrayIndex, ∑ b : Fin 4,
        (generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase a (golayLabelCoefficients k)) : ℚ) *
          (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℚ) *
            T (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + xiGrayCode a))
              (generatedAxisGlobalXiColumn i b) : ℚ) : ℝ) / Real.sqrt 2) / 16 := by
      rw [generatedAxisGlobalXi_tensor_tetrad]
      apply congrArg (fun z : ℝ => z / 16)
      simp only [generatedAxisGlobalRationalTensorReal, Rat.cast_sum, Rat.cast_mul,
        Rat.cast_intCast, generatedAxisGlobalIntSign_real]
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      simp only [generatedAxisGlobalRationalTensorReal, generatedAxisGlobalRationalTensorXi,
        generatedAxisGlobalSpinLabel_coeff, Rat.cast_div, Rat.cast_ofNat]
      ring

/-- Every rational original sign coefficient is the actual complete real source coefficient. -/
theorem generatedAxisGlobalRationalTensorSign_actual (T : GeneratedAxisGlobalRationalTensor)
    (a : Fin 4096) (ε : ZMod 2) :
    localTensorRepresentation (generatedFifthSignFiber a ε)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorSign a ε T) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode a e
  have hh := generatedAxisGlobalSign_tensor_coordinate a ε d e
    (golayLabelCoefficients k 11) (golayLabelCoefficients a 11)
    (generatedAxisGlobalSignInputCode_translation a e)
    (generatedAxisGlobalRationalTensorReal T) i
  rw [← generatedAxisGlobalSpinLabel_split k] at hh
  apply (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0))
  rw [hh]
  simp only [generatedAxisGlobalRationalTensorSign, generatedAxisGlobalRationalTensorReal,
    generatedAxisGlobalSpinLabel_coeff, Rat.cast_div, Rat.cast_add, Rat.cast_sub,
    Rat.cast_mul, Rat.cast_intCast, Rat.cast_ofNat, generatedAxisGlobalIntSign_real,
    generatedAxisGlobalCodeSign_real, generatedAxisGlobalTensorLowLabel_encode,
    generatedAxisGlobalTensorHighLabel_encode]
  ring

/-- Every rational monomial coefficient is the literal original full word coefficient. -/
theorem generatedAxisGlobalRationalTensorMonomial_actual (T : GeneratedAxisGlobalRationalTensor)
    (w : List (Fin 2 × Bool)) :
    localTensorRepresentation ((w.map generatedFourthMonomialFiberLetter).prod)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorMonomial w T) := by
  funext t i
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [generatedAxisGlobalMonomial_tensor_coordinate]
  simp only [generatedAxisGlobalRationalTensorReal, generatedAxisGlobalRationalTensorMonomial,
    generatedAxisGlobalSpinLabel_coeff, Rat.cast_mul, Rat.cast_intCast,
    generatedAxisGlobalIntSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
