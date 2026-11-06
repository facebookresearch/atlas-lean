/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorColumns
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthLocalOrbit

/-! Literal original permutation words on every physical tensor coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every literal original fiber word has its actual signed spin product. -/
theorem generatedAxisGlobalMonomial_word_spin (w : List (Fin 2 × Bool)) :
    (((w.map generatedFourthMonomialFiberLetter).prod).val.1) =
      (w.map generatedFourthMonomialSpinLetter).prod := by
  change generatedFourthMonomialSpinProjection
    ((w.map generatedFourthMonomialFiberLetter).prod) = _
  rw [map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro l _
  rcases l with ⟨i, b⟩
  cases b with
  | false => rfl
  | true =>
    change generatedFourthMonomialSpinProjection ((monsterSourcePermutationFiber i)⁻¹) = _
    rw [map_inv]
    rfl

/-- Every literal original fiber word has its genuine Golay coordinate permutation. -/
theorem generatedAxisGlobalMonomial_word_spatial (w : List (Fin 2 × Bool)) :
    (((w.map generatedFourthMonomialFiberLetter).prod).val.2) =
      golayPermutationIsometry ((w.map generatedFourthMonomialPermutationLetter).prod) := by
  change generatedFourthMonomialSpatialProjection
    ((w.map generatedFourthMonomialFiberLetter).prod) =
      golayPermutationHom ((w.map generatedFourthMonomialPermutationLetter).prod)
  rw [map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro l _
  exact generatedFourth_monomial_letter_spatial l

/-- Exact tensor pullback of a literal source word, retaining its original spin lift phase. -/
theorem generatedAxisGlobalMonomial_tensor_coordinate (w : List (Fin 2 × Bool))
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation ((w.map generatedFourthMonomialFiberLetter).prod) T t i =
      qSign (generatedFourthMonomialWordPull w t).1 *
        T (generatedFourthMonomialWordPull w t).2
          (((w.map generatedFourthMonomialPermutationLetter).prod).val.symm i) := by
  rw [generatedAxisGlobalTensor_local_coordinate]
  simp_rw [generatedAxisGlobalMonomial_word_spin, generatedFourth_monomial_spin_word_apply]
  have hs (j : Fin 24) :
      ((w.map generatedFourthMonomialFiberLetter).prod).val.2.val (Pi.single j 1) i =
        (Pi.single j 1 : Fin 24 → ℝ)
          (((w.map generatedFourthMonomialPermutationLetter).prod).val.symm i) := by
    rw [generatedAxisGlobalMonomial_word_spatial]
    rfl
  simp_rw [hs]
  simp [Pi.single_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
