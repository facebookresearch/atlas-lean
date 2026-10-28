/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialFastTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorXiInverseCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorWord

/-! Complete original signed tensor operators with every denominator explicitly restored. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Every integer physical tensor coordinate, with no change of its source labels. -/
abbrev GeneratedAxisGlobalIntegerTensor := Fin 4096 → Fin 24 → ℤ

/-- The full original rational scaling of an integer physical tensor. -/
def generatedAxisGlobalIntegerTensorRat (Z : GeneratedAxisGlobalIntegerTensor) (D : ℚ) :
    GeneratedAxisGlobalRationalTensor := fun a i => (Z a i : ℚ) / D

private theorem guarded_integer_tensor_term (c z : ℤ) (D : ℚ) (hD : D ≠ 0) :
    (if (z : ℚ) / D = 0 then 0 else (c : ℚ) * ((z : ℚ) / D)) =
      ((if z = 0 then 0 else c*z : ℤ) : ℚ) / D := by
  by_cases hz : z = 0
  · simp [hz]
  · have hq : (z : ℚ) / D ≠ 0 := div_ne_zero (by exact_mod_cast hz) hD
    simp only [hz, hq, ↓reduceIte, Int.cast_mul]
    ring

/-- The entire original monomial pullback, phase, and physical columns. -/
def generatedAxisGlobalIntegerTensorMonomial (k : Fin 8) (Z : GeneratedAxisGlobalIntegerTensor)
    (a : Fin 4096) (i : Fin 24) : ℤ :=
  let z := Z (generatedAxisGlobalSpinLabel (generatedAxisGlobalComparisonMonomialFastPull k a))
    (generatedAxisGlobalComparisonMonomialPhysicalPull k i)
  if z = 0 then 0 else generatedAxisGlobalIntSign (generatedAxisGlobalComparisonMonomialFastPhase k a) * z

/-- Every integer monomial output restores the complete original rational operator. -/
theorem generatedAxisGlobalIntegerTensorMonomial_rat (k : Fin 8) (Z : GeneratedAxisGlobalIntegerTensor)
    (D : ℚ) (hD : D ≠ 0) :
    generatedAxisGlobalComparisonMonomialFastTensor k (generatedAxisGlobalIntegerTensorRat Z D) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerTensorMonomial k Z) D := by
  funext a i
  dsimp only [generatedAxisGlobalComparisonMonomialFastTensor,
    generatedAxisGlobalIntegerTensorRat, generatedAxisGlobalIntegerTensorMonomial]
  exact guarded_integer_tensor_term _ _ D hD

/-- All original forward Gaussian inputs and zero guards, with denominator sixteen restored below. -/
def generatedAxisGlobalIntegerTensorXi (Z : GeneratedAxisGlobalIntegerTensor)
    (k : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : Fin 64, ∑ b : Fin 4,
    let m := generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a)
    let j := generatedAxisGlobalXiColumn i b
    let z := Z m j
    if z = 0 then 0 else generatedSixthGraySign a * generatedSixthSpinGammaFast m * co1XiNumerator i j * z

/-- All original reversed Gaussian inputs and transposed columns, with denominator sixteen restored below. -/
def generatedAxisGlobalIntegerTensorXiInverse (Z : GeneratedAxisGlobalIntegerTensor)
    (k : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : Fin 64, ∑ b : Fin 4,
    let m := generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a)
    let j := generatedAxisGlobalXiColumn i b
    let z := Z m j
    if z = 0 then 0 else generatedSixthGraySign a * generatedSixthSpinGammaFast k * co1XiNumerator j i * z

/-- The full integer forward Gaussian equals the genuine rational Gaussian at every input. -/
theorem generatedAxisGlobalIntegerTensorXi_rat (Z : GeneratedAxisGlobalIntegerTensor)
    (D : ℚ) (hD : D ≠ 0) :
    generatedAxisGlobalRationalTensorXiCached (generatedAxisGlobalIntegerTensorRat Z D) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerTensorXi Z) (16*D) := by
  funext k i
  unfold generatedAxisGlobalRationalTensorXiCached generatedAxisGlobalIntegerTensorRat
    generatedAxisGlobalIntegerTensorXi
  dsimp only
  simp only [Int.cast_sum]
  have ht (a : Fin 64) (b : Fin 4) := guarded_integer_tensor_term
    (generatedSixthGraySign a * generatedSixthSpinGammaFast
      (generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a)) *
      co1XiNumerator i (generatedAxisGlobalXiColumn i b))
    (Z (generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a))
      (generatedAxisGlobalXiColumn i b)) D hD
  simp only [Int.cast_mul] at ht
  simp_rw [ht]
  simp_rw [← Finset.sum_div]
  ring

/-- The full integer inverse Gaussian equals the genuine reversed rational Gaussian at every input. -/
theorem generatedAxisGlobalIntegerTensorXiInverse_rat (Z : GeneratedAxisGlobalIntegerTensor)
    (D : ℚ) (hD : D ≠ 0) :
    generatedAxisGlobalRationalTensorXiInverseCached (generatedAxisGlobalIntegerTensorRat Z D) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerTensorXiInverse Z) (16*D) := by
  funext k i
  unfold generatedAxisGlobalRationalTensorXiInverseCached generatedAxisGlobalIntegerTensorRat
    generatedAxisGlobalIntegerTensorXiInverse
  dsimp only
  simp only [Int.cast_sum]
  have ht (a : Fin 64) (b : Fin 4) := guarded_integer_tensor_term
    (generatedSixthGraySign a * generatedSixthSpinGammaFast k *
      co1XiNumerator (generatedAxisGlobalXiColumn i b) i)
    (Z (generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a))
      (generatedAxisGlobalXiColumn i b)) D hD
  simp only [Int.cast_mul] at ht
  simp_rw [ht]
  simp_rw [← Finset.sum_div]
  ring

/-- Every original sign phase and all four physical input coordinates, with denominator two restored below. -/
def generatedAxisGlobalIntegerTensorSign (a : Fin 4096) (ε : ZMod 2)
    (Z : GeneratedAxisGlobalIntegerTensor) (k : Fin 4096) (i : Fin 24) : ℤ :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode a e
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) * generatedAxisGlobalCodeSign e i *
    generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase a ε d e) * generatedAxisGlobalCodeSign d i *
      (Z (generatedAxisGlobalTensorLowLabel d) i - Z (generatedAxisGlobalTensorHighLabel d) i) +
    generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase a e i) *
      (Z (generatedAxisGlobalTensorLowLabel e) i + Z (generatedAxisGlobalTensorHighLabel e) i)

/-- Every integer sign output restores the complete original four-input rational sign action. -/
theorem generatedAxisGlobalIntegerTensorSign_rat (a : Fin 4096) (ε : ZMod 2)
    (Z : GeneratedAxisGlobalIntegerTensor) (D : ℚ) :
    generatedAxisGlobalRationalTensorSign a ε (generatedAxisGlobalIntegerTensorRat Z D) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerTensorSign a ε Z) (2*D) := by
  funext k i
  dsimp only [generatedAxisGlobalRationalTensorSign, generatedAxisGlobalIntegerTensorSign,
    generatedAxisGlobalIntegerTensorRat]
  push_cast
  ring

/-- The entire original extraspecial translation and its complete central phase. -/
def generatedAxisGlobalIntegerTensorQ (q : Q) (Z : GeneratedAxisGlobalIntegerTensor)
    (k : Fin 4096) (i : Fin 24) : ℤ :=
  generatedAxisGlobalIntSign (spinPhase q (golayLabelCoefficients k)) *
    Z (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + spinTranslation q)) i

/-- Every integer extraspecial output equals the complete genuine rational Q action. -/
theorem generatedAxisGlobalIntegerTensorQ_rat (q : Q) (Z : GeneratedAxisGlobalIntegerTensor) (D : ℚ) :
    generatedAxisGlobalRationalTensorQ q (generatedAxisGlobalIntegerTensorRat Z D) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerTensorQ q Z) D := by
  funext k i
  dsimp only [generatedAxisGlobalRationalTensorQ, generatedAxisGlobalIntegerTensorQ,
    generatedAxisGlobalIntegerTensorRat]
  push_cast
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
