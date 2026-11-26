/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovUniquenessParent
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for parent triples of generalized Cohn triples

Concrete generalized Cohn triples test both parent constructions for zero and nonzero parameters.
-/

namespace MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessParent

open MetaMathlibExt

private theorem classical_triple :
    IsGenCohnTriple 0 !![1, 1; 1, 2] !![3, 2; 4, 3] !![2, 1; 1, 1] 1 2 1 := by
  have h1 : IsGenMarkovNumber 0 1 := ⟨1, 1, isGenMarkovTriple_one_one_one 0⟩
  have h2 : IsGenMarkovNumber 0 2 := ⟨1, 1, by unfold IsGenMarkovTriple; decide⟩
  refine ⟨⟨?_, 1, rfl, h1, ?_⟩, ⟨?_, 2, rfl, h2, ?_⟩,
    ⟨?_, 1, rfl, h1, ?_⟩, ?_, rfl, rfl, rfl, by unfold IsGenMarkovTriple; decide⟩
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two]
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two]
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, genCohnS]

example :
    (!![1, 1; 1, 2]⁻¹ * (!![2, 1; 1, 1] + genCohnS 0) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 1 ∧
      ((!![1, 1; 1, 2] + genCohnS 0) * !![2, 1; 1, 1]⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 1 := by
  obtain ⟨⟨_, _, _, _, _, _, hL, _⟩, ⟨_, _, _, _, hV, _, _, _⟩⟩ :=
    IsGenCohnTriple.parent classical_triple
  exact ⟨by simpa using hL, by simpa using hV⟩

private theorem nonzero_triple :
    IsGenCohnTriple 1 !![1, 1; 3, 4] !![7, 3; 23, 10] !![3, 1; 5, 2] 1 3 1 := by
  have h1 : IsGenMarkovNumber 1 1 := ⟨1, 1, isGenMarkovTriple_one_one_one 1⟩
  have h3 : IsGenMarkovNumber 1 3 := ⟨1, 1, by unfold IsGenMarkovTriple; decide⟩
  refine ⟨⟨?_, 1, rfl, h1, ?_⟩, ⟨?_, 3, rfl, h3, ?_⟩,
    ⟨?_, 1, rfl, h1, ?_⟩, ?_, rfl, rfl, rfl, by unfold IsGenMarkovTriple; decide⟩
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two]
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two]
  · norm_num [Matrix.det_fin_two]
  · norm_num [Matrix.trace_fin_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, genCohnS]

example :
    (!![1, 1; 3, 4]⁻¹ * (!![3, 1; 5, 2] + genCohnS 1) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 1 ∧
      ((!![1, 1; 3, 4] + genCohnS 1) * !![3, 1; 5, 2]⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 1 := by
  obtain ⟨⟨_, _, _, _, _, _, hL, _⟩, ⟨_, _, _, _, hV, _, _, _⟩⟩ :=
    IsGenCohnTriple.parent nonzero_triple
  exact ⟨by simpa using hL, by simpa using hV⟩

end MathlibExtTest.NumberTheory.GeneralizedMarkovUniquenessParent
