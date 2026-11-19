/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.Absorption.AUC

/-! Tests: AUC integral values through the APIs. -/

namespace MathlibExtTest.Biology.Biophysics.Absorption.AUC

open MathlibExt.Biology.Biophysics.Absorption.AUC

/-- Distinct rates `ka = 2`, `k = 1`, `F = 1`, `D = 10`: AUC `10`. -/
example : ∫ t in Set.Ici 0, 1 * 10 * 2 * (Real.exp (-1 * t) - Real.exp (-2 * t)) / (2 - 1) =
    1 * 10 / 1 :=
  (auc_distinct_amount (by norm_num) (by norm_num) (by norm_num)).2

/-- Equal rate `ka = 1`: AUC `10`. -/
example : ∫ t in Set.Ici 0, 1 * 10 * 1 * t * Real.exp (-1 * t) = 1 * 10 / 1 :=
  (auc_equal_amount (by norm_num)).2

end MathlibExtTest.Biology.Biophysics.Absorption.AUC
