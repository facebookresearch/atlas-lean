/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.CompartmentKinetics.Observability

/-! Tests: numeric determinant and boundary `k21 = 0`. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Observability

open MathlibExt.Biology.Biophysics.CompartmentKinetics.Observability

/-- Determinant at `k21 = 2`, `V1 = 4`: `2 / 16`. -/
example : Matrix.det ((Matrix.of !![(1:ℝ) / 4, 0; (1 / 4) * (-(1 + 1)), (1 / 4) * 2] :
    Matrix (Fin 2) (Fin 2) ℝ)) = 2 / 4 ^ 2 :=
  observability_det

/-- At `k21 = 0` the determinant is zero. -/
example : Matrix.det ((Matrix.of !![(1:ℝ) / 4, 0; (1 / 4) * (-(1 + 1)), (1 / 4) * 0] :
    Matrix (Fin 2) (Fin 2) ℝ)) = 0 / 4 ^ 2 :=
  observability_det

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.Observability
