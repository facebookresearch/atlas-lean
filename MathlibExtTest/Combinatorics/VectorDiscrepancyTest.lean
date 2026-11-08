/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.VectorDiscrepancy

open scoped BigOperators ENNReal
open MatrixDiscrepancy

namespace MathlibExtTest.VectorDiscrepancy

example : vectorDiscrepancy (fun _ _ : Fin 1 => (1 : ℝ)) ≤
    discrepancy (fun _ _ : Fin 1 => (1 : ℝ)) :=
  vectorDiscrepancy_le_discrepancy (by decide) _

example : ∃ u : Fin 1 → EuclideanSpace ℝ (Fin 1), (∀ j, ‖u j‖ = 1) ∧
    vectorDiscrepancy (fun _ _ : Fin 1 => (1 : ℝ)) =
      ENNReal.ofReal ‖fun _i : Fin 1 => ∑ j, (1 : ℝ) • u j‖ :=
  vectorDiscrepancy_attained (by decide) _

#eval "C24 actual positive-dimensional vector relaxation proofs elaborated"

end MathlibExtTest.VectorDiscrepancy
