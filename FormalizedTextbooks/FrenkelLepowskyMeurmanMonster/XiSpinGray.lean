/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Explicit grey code/cocode frame for Seysen's three-bases element.
Source: Seysen, arXiv:2002.10921v3, §§2.2, 5.3 and 9.3.
The six MOG columns are contiguous blocks of four coordinates.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceCodeAddition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinIrreducible

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Binary coefficient vectors for the six standard grey generators. -/
abbrev XiGrayIndex := Fin 6 → ZMod 2

/-- Labels of g_i=ω_i+ω_∞ in the published Golay generator table. -/
def xiGrayCodeLabel : Fin 6 → Fin 4096 := ![0x400, 0xc0f, 0xc01, 0xc02, 0xc04, 0xc08]

/-- Cocode syndromes of the six individual MOG row-zero positions. -/
def xiGrayCocodeLabel : Fin 6 → Fin 4096 := ![0x800, 0xc0f, 0xc0e, 0xc0d, 0xc0b, 0xc07]

/-- The actual Golay coefficient vector of a standard grey code generator. -/
def xiGrayCodeBasis (i : Fin 6) : SpinIndex := golayLabelCoefficients (xiGrayCodeLabel i)
/-- The actual syndrome vector of a standard grey cocode generator. -/
def xiGrayCocodeBasis (i : Fin 6) : SpinIndex := golayLabelCoefficients (xiGrayCocodeLabel i)

/-- The code frame is checked against actual MOG bits. -/
theorem xiGrayCodeBasis_mask (i : Fin 6) :
    golayEncodedMask (xiGrayCodeLabel i).val = (15 * 2 ^ (4 * i.val)) ^^^ 0x111111 := by
  fin_cases i <;> decide +kernel

/-- The cocode frame is checked against the actual syndrome map. -/
theorem xiGrayCocodeBasis_syndrome (i : Fin 6) :
    xiGrayCocodeBasis i = golaySyndrome (Pi.single (⟨4 * i.val, by omega⟩ : Fin 24) 1) := by
  fin_cases i <;> decide +kernel

theorem xiGrayBasis_pairing (i j : Fin 6) :
    spinDot (xiGrayCocodeBasis i) (xiGrayCodeBasis j) = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Linear code embedding of the six-dimensional grey space. -/
def xiGrayCode : XiGrayIndex →ₗ[ZMod 2] SpinIndex where
  toFun a := ∑ i, a i • xiGrayCodeBasis i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [mul_smul, Finset.smul_sum]

/-- Linear cocode embedding of the dual grey space. -/
def xiGrayCocode : XiGrayIndex →ₗ[ZMod 2] SpinIndex where
  toFun a := ∑ i, a i • xiGrayCocodeBasis i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [mul_smul, Finset.smul_sum]

/-- Binomial weight quadratic form: choose(w(a),2) modulo two. -/
def xiGrayQuadratic (a : XiGrayIndex) : ZMod 2 :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin 6 => i < j), a i * a j

/-- The bilinear form has zero diagonal and one off the diagonal. -/
def xiGrayBilinear (a b : XiGrayIndex) : ZMod 2 :=
  ∑ i, ∑ j, a i * b j * (if i = j then 0 else 1)

/-- Pure translations are the normalized generators tilde{x}_d of §5.3. -/
def xiGrayTranslation : Multiplicative XiGrayIndex →* Q where
  toFun a := ⟨ofAdd (Fin.append (xiGrayCode (toAdd a)) (0 : SpinIndex)), 1⟩
  map_one' := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change Fin.append (xiGrayCode 0) (0 : SpinIndex) = 0
      rw [map_zero]
      ext i
      refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
    · rfl
  map_mul' a b := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change Fin.append (xiGrayCode (toAdd a + toAdd b)) (0 : SpinIndex) =
        Fin.append (xiGrayCode (toAdd a)) (0 : SpinIndex) +
          Fin.append (xiGrayCode (toAdd b)) (0 : SpinIndex)
      rw [map_add]
      ext i
      refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, Pi.zero_apply,
          Pi.add_apply, add_zero]
    · apply toAdd.injective
      change 0 = 0 + 0 + qBeta (Fin.append (xiGrayCode (toAdd a)) (0 : SpinIndex))
        (Fin.append (xiGrayCode (toAdd b)) (0 : SpinIndex))
      simp only [qBeta, Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, zero_add]

/-- Actual commuting cocode generators x_γ. -/
def xiGrayModulation : Multiplicative XiGrayIndex →* Q where
  toFun a := ⟨ofAdd (binaryCocodeEmbedding (xiGrayCocode (toAdd a))), 1⟩
  map_one' := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change binaryCocodeEmbedding (xiGrayCocode 0) = 0
      rw [map_zero, map_zero]
    · rfl
  map_mul' a b := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change binaryCocodeEmbedding (xiGrayCocode (toAdd a + toAdd b)) =
        binaryCocodeEmbedding (xiGrayCocode (toAdd a)) +
          binaryCocodeEmbedding (xiGrayCocode (toAdd b))
      rw [map_add, map_add]
    · apply toAdd.injective
      change 0 = 0 + 0 + qBeta (binaryCocodeEmbedding (xiGrayCocode (toAdd a)))
        (binaryCocodeEmbedding (xiGrayCocode (toAdd b)))
      simp [qBeta, binaryCocodeEmbedding]

@[simp] theorem xiGrayTranslation_translation (a : XiGrayIndex) :
    spinTranslation (xiGrayTranslation (ofAdd a)) = xiGrayCode a := by
  ext i
  exact Fin.append_left _ _ _

@[simp] theorem xiGrayTranslation_modulation (a : XiGrayIndex) :
    spinModulation (xiGrayTranslation (ofAdd a)) = 0 := by
  ext i
  exact Fin.append_right _ _ _

@[simp] theorem xiGrayModulation_translation (a : XiGrayIndex) :
    spinTranslation (xiGrayModulation (ofAdd a)) = 0 := by
  ext i
  exact binaryCocodeEmbedding_left _ _

@[simp] theorem xiGrayModulation_modulation (a : XiGrayIndex) :
    spinModulation (xiGrayModulation (ofAdd a)) = xiGrayCocode a := by
  ext i
  exact binaryCocodeEmbedding_right _ _

@[simp] theorem xiGrayTranslation_operator (a : XiGrayIndex) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (xiGrayTranslation (ofAdd a)) f t = f (t + xiGrayCode a) := by
  simp only [spinOperator, LinearMap.coe_mk, AddHom.coe_mk, spinPhase,
    xiGrayTranslation_translation, xiGrayTranslation_modulation, spinDot_zero_left,
    show toAdd (xiGrayTranslation (ofAdd a)).coeff = 0 from rfl, zero_add, qSign_zero, one_mul]

@[simp] theorem xiGrayModulation_operator (a : XiGrayIndex) (f : SpinSpace) (t : SpinIndex) :
    spinOperator (xiGrayModulation (ofAdd a)) f t = qSign (spinDot (xiGrayCocode a) t) * f t := by
  simp only [spinOperator, LinearMap.coe_mk, AddHom.coe_mk, spinPhase,
    xiGrayModulation_translation, xiGrayModulation_modulation,
    show toAdd (xiGrayModulation (ofAdd a)).coeff = 0 from rfl, zero_add, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
