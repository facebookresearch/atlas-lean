/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-! Tests: clipping into `[0, 2]`. -/

namespace MathlibExtTest.Biology.Biophysics.NeuralPopulation.BoxFlow

open MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-- A value inside the box is unchanged. -/
example : clipBox 2 (1:ℝ) = 1 := clipBox_eq_of_mem zero_le_one one_le_two

end MathlibExtTest.Biology.Biophysics.NeuralPopulation.BoxFlow
