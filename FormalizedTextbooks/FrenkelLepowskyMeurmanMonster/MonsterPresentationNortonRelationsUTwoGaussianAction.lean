/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sixteen-term integer formula for the genuine rank-four translation Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoGaussianHolomorph
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinWord

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The four retained grey bits, read as an actual integral spin label. -/
def monsterNortonUTwoGaussianLabel (a : XiGrayIndex) : Fin 16 :=
  ⟨∑ i : Fin 4, if a (Fin.natAdd 2 i) = 0 then 0 else 2 ^ i.val, by
    have h : ∀ a : XiGrayIndex,
        (∑ i : Fin 4, if a (Fin.natAdd 2 i) = 0 then 0 else 2 ^ i.val) < 16 := by
      decide +kernel
    exact h a⟩

/-- A retained-bit label as an actual spin basis label. -/
def monsterNortonUTwoGaussianSpinLabel (b : Fin 16) : Fin 4096 :=
  ⟨b.val, by omega⟩

/-- Exact signs after summing the two omitted grey directions. -/
def monsterNortonUTwoGaussianSign : Fin 16 → ℤ :=
  ![1, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1]

set_option maxHeartbeats 8000000 in
-- All sixty-four actual code images are checked against their retained-bit labels.
/-- The retained-bit label is the actual translation in the spin coordinate dictionary. -/
theorem monsterNortonUTwoGaussianCode_label (a : XiGrayIndex) :
    monsterNortonUTwoGaussianCode a =
      golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel
        (monsterNortonUTwoGaussianLabel a)) := by
  have h : ∀ a : XiGrayIndex, monsterNortonUTwoGaussianCode a =
      golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel
        (monsterNortonUTwoGaussianLabel a)) := by
    decide +kernel
  exact h a

set_option maxHeartbeats 8000000 in
-- Sixteen exact fibers, each with four integral sign terms, are checked in the ordinary kernel.
/-- The two ignored grey bits contribute twice the displayed sixteen quadratic signs. -/
theorem monsterNortonUTwoGaussian_coefficient (b : Fin 16) :
    (∑ a : XiGrayIndex,
      if monsterNortonUTwoGaussianLabel a = b then xiGraySign a else 0) =
        2 * monsterNortonUTwoGaussianSign b := by
  have h : ∀ b : Fin 16, (∑ a : XiGrayIndex,
      if monsterNortonUTwoGaussianLabel a = b then xiGraySign a else 0) =
        2 * monsterNortonUTwoGaussianSign b := by
    decide +kernel
  exact h b

private theorem weighted_sum (f : Fin 16 → ℤ) :
    (∑ a : XiGrayIndex, xiGraySign a * f (monsterNortonUTwoGaussianLabel a)) =
      2 * ∑ b : Fin 16, monsterNortonUTwoGaussianSign b * f b := by
  classical
  calc
    _ = ∑ a : XiGrayIndex, ∑ b : Fin 16,
        if monsterNortonUTwoGaussianLabel a = b then xiGraySign a * f b else 0 := by
      congr 1
      ext a
      simp
    _ = ∑ b : Fin 16, ∑ a : XiGrayIndex,
        if monsterNortonUTwoGaussianLabel a = b then xiGraySign a * f b else 0 :=
      Finset.sum_comm
    _ = ∑ b : Fin 16, (∑ a : XiGrayIndex,
        if monsterNortonUTwoGaussianLabel a = b then xiGraySign a else 0) * f b := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    _ = 2 * ∑ b : Fin 16, monsterNortonUTwoGaussianSign b * f b := by
      simp only [monsterNortonUTwoGaussian_coefficient, Finset.mul_sum, mul_assoc]

/-- The complete sixteen-term integer numerator of the genuine Gaussian. -/
def monsterNortonUTwoGaussianInteger (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => ∑ b : Fin 16, monsterNortonUTwoGaussianSign b *
    v (nortonUIntegerLabel (golayLabelCoefficients n +
      golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel b)))

private theorem translation_apply (a : XiGrayIndex) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (monsterNortonUTwoGaussianTranslation (Multiplicative.ofAdd a)) f t =
      f (t + monsterNortonUTwoGaussianCode a) := by
  have ht : spinTranslation (monsterNortonUTwoGaussianTranslation
      (Multiplicative.ofAdd a)) = monsterNortonUTwoGaussianCode a := by
    funext i
    exact Fin.append_left _ _ i
  have hm : spinModulation (monsterNortonUTwoGaussianTranslation
      (Multiplicative.ofAdd a)) = 0 := by
    funext i
    exact Fin.append_right _ _ i
  rw [xiSpinOperator_apply, ht]
  simp only [spinPhase, hm]
  change qSign (0 + spinDot 0 t) * f (t + monsterNortonUTwoGaussianCode a) = _
  simp

/-- The collapsed sixteen-term integer formula is exactly the proved real Gaussian. -/
theorem monsterNortonUTwoGaussianInteger_embed (v : NortonUIntegerVector) :
    monsterNortonUTwoGaussian (nortonUIntegerEmbed v) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (monsterNortonUTwoGaussianInteger v) := by
  ext t
  simp only [monsterNortonUTwoGaussian, xiGrayGaussian, LinearMap.smul_apply,
    LinearMap.sum_apply, MonoidHom.comp_apply]
  simp only [xiSpinLinearRepresentation_operator, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, translation_apply, nortonUIntegerEmbed]
  change (1 / 8 : ℝ) * ∑ a : XiGrayIndex,
    qSign (xiGrayQuadratic a) *
      (v (nortonUIntegerLabel (t + monsterNortonUTwoGaussianCode a)) : ℝ) = _
  simp only [monsterNortonUTwoGaussianCode_label, ← xiGraySign_real, ← Int.cast_mul,
    ← Int.cast_sum]
  rw [weighted_sum (fun b => v (nortonUIntegerLabel (t +
    golayLabelCoefficients (monsterNortonUTwoGaussianSpinLabel b))))]
  simp only [Int.cast_mul, Int.cast_ofNat,
    monsterNortonUTwoGaussianInteger, nortonUIntegerLabel_inverse]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
