/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Geometry.ThinShellCubeBound

open MathlibExt.Probability.ThinShell
open scoped ENNReal

example : (4 : ℝ≥0∞) / 5 ≤ thinShellVarianceConstant := by
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 5),
    ENNReal.ofReal_ofNat] using fourFifths_le_thinShellVarianceConstant
