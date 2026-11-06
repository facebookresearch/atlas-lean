/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingOctadSparseData

/-! Sparse evaluation preserves every slot of a complete finite sum. -/
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Evaluate a full Fourier row by its signed list, retaining all zero coefficients. -/
theorem generatedRootEight_sparse_coefficient_sum (F : Fin 64 → ℤ)
    (es : List (Fin 64 × ℤ)) :
    (∑ f : Fin 64, F f * generatedRootEightSparseCoefficient es f) =
      (es.map (fun e => F e.1 * e.2)).sum := by
  induction es with
  | nil => simp [generatedRootEightSparseCoefficient]
  | cons e es ih =>
    simp only [generatedRootEightSparseCoefficient, mul_add, Finset.sum_add_distrib,
      List.map_cons, List.sum_cons, ih]
    congr 1
    simp [mul_ite, eq_comm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
