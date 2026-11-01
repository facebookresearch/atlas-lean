/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Computable integer coordinates for exact certificates of the actual Norton spin word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonLocalWord

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Explicit computable inverse of the twelve-bit source coefficient label. -/
def nortonUIntegerLabel (t : SpinIndex) : Fin 4096 :=
  ⟨∑ j : Fin 12, (t j).val * 2 ^ j.val, by
    obtain ⟨d, rfl⟩ := golayLabelCoefficients_bijective.surjective t
    rw [golayLabelCoefficients_reassemble]
    exact d.isLt⟩

/-- The computable inverse recovers every actual source label. -/
theorem nortonUIntegerLabel_coeff (d : Fin 4096) :
    nortonUIntegerLabel (golayLabelCoefficients d) = d := by
  apply Fin.ext
  exact golayLabelCoefficients_reassemble d

/-- Encoding after the computable inverse recovers every actual spin index. -/
theorem nortonUIntegerLabel_inverse (t : SpinIndex) :
    golayLabelCoefficients (nortonUIntegerLabel t) = t := by
  obtain ⟨d, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [nortonUIntegerLabel_coeff]

/-- Integer spin vectors indexed by the actual twelve-bit source labels. -/
abbrev NortonUIntegerVector := Fin 4096 → ℤ

/-- Embed an integer vector in the actual real spin coordinate space. -/
def nortonUIntegerEmbed (v : NortonUIntegerVector) : SpinSpace :=
  fun t => (v (nortonUIntegerLabel t) : ℝ)

/-- An integral version of the exact binary sign. -/
def nortonUIntegerSign (c : ZMod 2) : ℤ := if c = 0 then 1 else -1

/-- Integral signs embed as the genuine real spin signs. -/
theorem nortonUIntegerSign_real (c : ZMod 2) :
    (nortonUIntegerSign c : ℝ) = qSign c := by simp [nortonUIntegerSign, qSign]

/-- The actual Q numerator, retaining every source central phase. -/
def nortonUIntegerQ (q : Q) (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => let t := golayLabelCoefficients n
    nortonUIntegerSign (spinPhase q t) * v (nortonUIntegerLabel (t + spinTranslation q))

/-- The integer Q action is the actual extraspecial spin operator. -/
theorem nortonUIntegerQ_embed (q : Q) (v : NortonUIntegerVector) :
    spinRepresentation q (nortonUIntegerEmbed v) = nortonUIntegerEmbed (nortonUIntegerQ q v) := by
  ext t
  simp only [monsterMonomialSpinRepresentation_apply, nortonUIntegerEmbed,
    nortonUIntegerQ, nortonUIntegerLabel_inverse, Int.cast_mul, nortonUIntegerSign_real]

/-- The exact inverse Parker lift acts by its signed forward source code relabeling. -/
theorem nortonUIntegerPermutation_inverse_apply (k : Fin 2) (f : SpinSpace) (t : SpinIndex) :
    (monsterSourcePermutationSpin k)⁻¹.val f t =
      qSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) t) *
        f (monsterSourcePermutationCode k t) := rfl

/-- An integer inverse Parker lift, including its genuine quadratic sign. -/
def nortonUIntegerPermutationInverse (k : Fin 2) (v : NortonUIntegerVector) :
    NortonUIntegerVector := fun n => let t := golayLabelCoefficients n
  nortonUIntegerSign (monsterMonomialQuadratic (monsterSourcePermutationPhaseData k) t) *
    v (nortonUIntegerLabel (monsterSourcePermutationCode k t))

/-- Its real embedding is exactly the actual inverse spin lift. -/
theorem nortonUIntegerPermutationInverse_embed (k : Fin 2) (v : NortonUIntegerVector) :
    (monsterSourcePermutationSpin k)⁻¹.val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (nortonUIntegerPermutationInverse k v) := by
  ext t
  simp only [nortonUIntegerPermutation_inverse_apply, nortonUIntegerEmbed,
    nortonUIntegerPermutationInverse, nortonUIntegerLabel_inverse,
    Int.cast_mul, nortonUIntegerSign_real]

/-- The two-term integral numerator of the actual one-coordinate Fourier operator. -/
def nortonUIntegerHadamard (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => let t := golayLabelCoefficients n
    nortonUIntegerSign (t 11) * v n + v (nortonUIntegerLabel (monsterSpinOmegaFlip t))

/-- Its normalization is exactly the source Fourier operator, with denominator sqrt two. -/
theorem nortonUIntegerHadamard_embed (v : NortonUIntegerVector) :
    monsterSpinHadamard (nortonUIntegerEmbed v) =
      (1 / Real.sqrt 2 : ℝ) • nortonUIntegerEmbed (nortonUIntegerHadamard v) := by
  ext t
  simp only [monsterSpinHadamard_apply, nortonUIntegerEmbed, nortonUIntegerHadamard,
    nortonUIntegerLabel_inverse, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
    nortonUIntegerSign_real]
  ring

/-- The integral signed affine part of the genuine y82 spin operator. -/
def nortonUIntegerY82PlusMinus (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => let t := golayLabelCoefficients n
    nortonUIntegerSign
      (monsterMonomialQuadratic (monsterSourceYPhaseMatrix monsterSourceY82Code) t) *
        v (nortonUIntegerLabel (monsterSourceY82Affine t))

/-- Its embedding retains the full proved y82 quadratic phase. -/
theorem nortonUIntegerY82PlusMinus_embed (v : NortonUIntegerVector) :
    monsterSourceY82PlusMinus.val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (nortonUIntegerY82PlusMinus v) := by
  ext t
  simp only [monsterSourceY82PlusMinus_quadratic, nortonUIntegerEmbed,
    nortonUIntegerY82PlusMinus, nortonUIntegerLabel_inverse, Int.cast_mul,
    nortonUIntegerSign_real]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
