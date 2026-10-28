/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQMatrixAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialQSparseData

/-! Sparse evaluation equals the entire original corrected Q conjugation, including its center. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Sparse original binary and central evaluation on the genuine extraspecial group. -/
def generatedFourthMonomialQMatrixSparse (k : Fin 4) (q : Q) : Q :=
  ⟨ofAdd (generatedFourthMonomialQBinaryLinear k (toAdd q.base)),
    ofAdd (toAdd q.coeff + generatedFourthMonomialQPhaseFast k (toAdd q.base))⟩

/-- The sparse expression is the actual full-Q conjugation of each original corrected word. -/
theorem generatedFourth_monomial_q_matrix_sparse (k : Fin 4) (q : Q) :
    spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1 q =
      generatedFourthMonomialQMatrixSparse k q := by
  rw [generatedFourth_monomial_q_matrix_action, generatedFourth_monomial_q_matrix_value,
    generatedFourth_monomial_q_phase_fast, generatedFourth_monomial_q_binary_linear]
  rfl

/-- Both exact evaluators agree on every actual element, with every central bit retained. -/
theorem generatedFourth_monomial_q_image_sparse (k : Fin 4) (q : Q) :
    generatedFourthMonomialCorrectedQImage k q = generatedFourthMonomialQMatrixSparse k q :=
  (generatedFourth_monomial_corrected_q_image k q).symm.trans
    (generatedFourth_monomial_q_matrix_sparse k q)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
