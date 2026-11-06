/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthMonomialSpatialProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! Original Parker signs in the complete six fifth-system permutation words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Reverse a literal source letter with its original signed inverse. -/
def generatedFifthMonomialInverseLetter (l : Fin 2 × Bool) : Fin 2 × Bool :=
  (l.1, !l.2)

/-- All letters of each actual selected-coordinate permutation word. -/
def generatedFifthMonomialPermutationWord (k : Fin 6) : List (Fin 2 × Bool) :=
  generatedFifthMonomialTransportWord ++ generatedFifthMonomialSourceWord k ++
    generatedFifthMonomialTransportWord.reverse.map generatedFifthMonomialInverseLetter

/-- The reversed literal letter is its genuine local fiber inverse. -/
theorem generatedFifth_monomial_inverse_letter (l : Fin 2 × Bool) :
    generatedFourthMonomialFiberLetter (generatedFifthMonomialInverseLetter l) =
      (generatedFourthMonomialFiberLetter l)⁻¹ := by
  rcases l with ⟨i, b⟩
  cases b <;> simp [generatedFifthMonomialInverseLetter, generatedFourthMonomialFiberLetter]

/-- The complete literal word is the previously defined genuine spatial fiber. -/
theorem generatedFifth_monomial_permutation_word_fiber (k : Fin 6) :
    ((generatedFifthMonomialPermutationWord k).map generatedFourthMonomialFiberLetter).prod =
      generatedFifthMonomialSpatialFiber k := by
  have hi : ((generatedFifthMonomialTransportWord.reverse.map
      generatedFifthMonomialInverseLetter).map generatedFourthMonomialFiberLetter).prod =
      ((generatedFifthMonomialTransportWord.map generatedFourthMonomialFiberLetter).prod)⁻¹ := by
    rw [List.prod_inv_reverse]
    simp only [List.map_map, List.map_reverse]
    have hm : generatedFifthMonomialTransportWord.map
        (generatedFourthMonomialFiberLetter ∘ generatedFifthMonomialInverseLetter) =
        generatedFifthMonomialTransportWord.map
          ((fun x => x⁻¹) ∘ generatedFourthMonomialFiberLetter) := by
      apply List.map_congr_left
      intro l _
      exact generatedFifth_monomial_inverse_letter l
    rw [hm]
  simp only [generatedFifthMonomialPermutationWord, List.map_append, List.prod_append]
  rw [hi]
  rfl

/-- Every original source word retains precisely its actual signed spin projection. -/
theorem generatedFifth_monomial_spin_word_projection (w : List (Fin 2 × Bool)) :
    generatedFourthMonomialSpinProjection ((w.map generatedFourthMonomialFiberLetter).prod) =
      ((w.map generatedFourthMonomialSpinLetter).prod) := by
  rw [map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b with
  | false => rfl
  | true =>
    change generatedFourthMonomialSpinProjection ((monsterSourcePermutationFiber i)⁻¹) = _
    rw [map_inv]
    rfl

/-- The six genuine words act by their full original signed spin pullbacks. -/
theorem generatedFifth_monomial_permutation_spin_apply (k : Fin 6)
    (x : SpinSpace) (t : SpinIndex) :
    (generatedFifthMonomialSpatialFiber k).val.1.val x t =
      qSign (generatedFourthMonomialWordPull (generatedFifthMonomialPermutationWord k) t).1 *
        x (generatedFourthMonomialWordPull (generatedFifthMonomialPermutationWord k) t).2 := by
  have hp : (generatedFifthMonomialSpatialFiber k).val.1 =
      ((generatedFifthMonomialPermutationWord k).map generatedFourthMonomialSpinLetter).prod := by
    rw [← generatedFifth_monomial_permutation_word_fiber]
    simpa only [generatedFourthMonomialSpinProjection, MonoidHom.coe_mk, OneHom.coe_mk] using
      generatedFifth_monomial_spin_word_projection (generatedFifthMonomialPermutationWord k)
  rw [hp]
  exact generatedFourth_monomial_spin_word_apply _ x t

private theorem tensor_apply_of_monomial (f : localFiberSubgroup)
    (p : golayAutomorphismSubgroup) (w : List (Fin 2 × Bool))
    (hp : f.val.2 = golayPermutationIsometry p)
    (hs : ∀ x : SpinSpace, ∀ t : SpinIndex, f.val.1.val x t =
      qSign (generatedFourthMonomialWordPull w t).1 *
        x (generatedFourthMonomialWordPull w t).2)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation f T t i =
      qSign (generatedFourthMonomialWordPull w t).1 *
        T (generatedFourthMonomialWordPull w t).2 (p.val.symm i) := by
  rw [generatedFourth_local_tensor_columns]
  simp_rw [hs]
  rw [hp]
  change (∑ j : Fin 24, (Pi.single j 1 : Fin 24 → ℝ) (p.val.symm i) *
    (qSign (generatedFourthMonomialWordPull w t).1 *
      T (generatedFourthMonomialWordPull w t).2 j)) = _
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The original physical permutation and Parker phase act on every tensor coordinate. -/
theorem generatedFifth_monomial_permutation_tensor_apply (k : Fin 6)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedFifthMonomialSpatialFiber k) T t i =
      qSign (generatedFourthMonomialWordPull (generatedFifthMonomialPermutationWord k) t).1 *
        T (generatedFourthMonomialWordPull (generatedFifthMonomialPermutationWord k) t).2
          ((generatedFifthMonomialSpatialPermutation k).val.symm i) :=
  tensor_apply_of_monomial _ _ _ (generatedFifth_monomial_spatial k)
    (generatedFifth_monomial_permutation_spin_apply k) T t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
