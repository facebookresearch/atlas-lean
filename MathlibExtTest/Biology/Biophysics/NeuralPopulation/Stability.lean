/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.NeuralPopulation.Stability

/-! Tests: the boundary witness is Hurwitz with the claimed signs. -/

namespace MathlibExtTest.Biology.Biophysics.NeuralPopulation.Stability

open MathlibExt.Biology.Biophysics.NeuralPopulation.Stability

/-- The negative identity is Hurwitz. -/
example : ((-1 : Matrix (Fin 2) (Fin 2) ℝ)).IsHurwitz :=
  neg_identity_isHurwitz

/-- Its trace and determinant are `-2` and `1`. -/
example : (-1 : Matrix (Fin 2) (Fin 2) ℝ).trace = -2 ∧
    (-1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
  neg_identity_trace_det

end MathlibExtTest.Biology.Biophysics.NeuralPopulation.Stability
