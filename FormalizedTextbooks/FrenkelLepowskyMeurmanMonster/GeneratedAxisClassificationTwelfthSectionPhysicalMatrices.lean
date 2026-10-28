/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixFixerFrame
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAction

/-! Complete actual physical coordinate matrices of every original signed section letter. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The physical coordinate matrix of a genuine inverse is its full transpose. -/
theorem generatedTwelfth_section_physical_matrix_inv (e : leechIsomSubgroup) :
    leechIsomMatrix e⁻¹ = (leechIsomMatrix e).transpose := by
  ext j k
  exact leechIsom_inverse_coordinate e k j

/-- The genuine identity has the complete identity physical coordinate matrix. -/
theorem generatedTwelfth_section_physical_matrix_one :
    leechIsomMatrix (1 : leechIsomSubgroup) = 1 := by
  ext j k
  simp [leechIsomMatrix, Pi.single_apply, Matrix.one_apply]

/-- Every full original selected-section generator has its actual denominator-two numerator. -/
theorem generatedTwelfth_section_physical_matrix (g : Fin 18) :
    leechIsomMatrix (generatedFifthSectionGenerator g) =
      (1 / 2 : ℝ) • (generatedFifthSectionGeneratorNumerator g).map (Int.castRingHom ℝ) := by
  ext i j
  by_cases h : g.val < 12
  · have hc : golayEncoder (Pi.single (⟨g.val, h⟩ : Fin 12) 1) i =
        (golayGeneratorBit ⟨g.val, h⟩ i : ZMod 2) := by
      simp [golayEncoder, Pi.single_apply, ite_mul]
    by_cases hij : i = j
    · subst j
      by_cases hb : (golayGeneratorMasks ⟨g.val, h⟩).testBit i.val
      all_goals simp [generatedFifthSectionGenerator, generatedFifthSectionGeneratorNumerator,
        leechIsomMatrix, h, golaySignIsometry, golayRealSign_apply, hc,
        golayGeneratorBit, hb, qSign, Matrix.smul_apply, Matrix.map_apply]
    · simp [generatedFifthSectionGenerator, generatedFifthSectionGeneratorNumerator,
        leechIsomMatrix, h, golaySignIsometry, golayRealSign_apply, hij,
        Matrix.smul_apply, Matrix.map_apply]
  · by_cases h' : g.val < 17
    · let k : Fin 5 := ⟨g.val - 12, by omega⟩
      have he : (generatedFifthSelectedOctadPermutation k).val.symm i = j ↔
          i = generatedFifthSelectedOctadForward k j := by
        rw [Equiv.symm_apply_eq, generatedFifthSelectedOctad_forward]
      simp only [generatedFifthSectionGenerator, generatedFifthSectionGeneratorNumerator,
        h, h', ↓reduceDIte, leechIsomMatrix, golayPermutationIsometry,
        golayRealPermute_apply, Pi.single_apply, Matrix.smul_apply, Matrix.map_apply]
      change (if (generatedFifthSelectedOctadPermutation k).val.symm i = j
          then 1 else 0) = (1 / 2 : ℝ) *
        ((if i = generatedFifthSelectedOctadForward k j then 2 else 0 : ℤ) : ℝ)
      by_cases hh : i = generatedFifthSelectedOctadForward k j
      · rw [ite_eq_left (he.mpr hh), ite_eq_left hh]
        norm_num
      · rw [ite_eq_right (fun h => hh (he.mp h)), ite_eq_right hh]
        norm_num
    · have hg : g = 17 := Fin.ext (by omega)
      subst g
      have hh := generatedFifth_xi_spatial_unit i j
      change (co1XiIsometry).val (Pi.single j 1) i = _ at hh
      change (co1XiIsometry).val (Pi.single j 1) i =
        (1 / 2 : ℝ) * (co1XiNumerator i j : ℝ)
      simpa only [div_eq_mul_inv, mul_comm, one_mul] using hh

/-- The full numerator for either orientation of an original section generator. -/
def generatedTwelfthSectionPhysicalNumerator (l : Fin 18 × Bool) :
    Matrix (Fin 24) (Fin 24) ℤ :=
  if l.2 then (generatedFifthSectionGeneratorNumerator l.1).transpose
  else generatedFifthSectionGeneratorNumerator l.1

/-- Every signed original section letter has its complete actual numerator. -/
theorem generatedTwelfth_section_physical_letter_matrix (l : Fin 18 × Bool) :
    leechIsomMatrix ((generatedTwelfthRootOrbitLetter l).val) =
      (1 / 2 : ℝ) • (generatedTwelfthSectionPhysicalNumerator l).map (Int.castRingHom ℝ) := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedTwelfth_section_physical_matrix g
  · change leechIsomMatrix (generatedFifthSectionGenerator g)⁻¹ = _
    rw [generatedTwelfth_section_physical_matrix_inv, generatedTwelfth_section_physical_matrix]
    simp only [generatedTwelfthSectionPhysicalNumerator, ↓reduceIte,
      Matrix.transpose_smul, Matrix.transpose_map]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
