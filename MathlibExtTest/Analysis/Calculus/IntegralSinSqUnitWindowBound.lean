/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.IntegralSinSqUnitWindowBound

open MathlibExt.Analysis.Calculus.IntegralSinSqUnitWindowBoundWanted

-- At this left endpoint cos(x²) = -1, so one of the two boundary terms vanishes.
example :
    |∫ t in Real.sqrt Real.pi..(Real.sqrt Real.pi + 1), Real.sin (t ^ 2)| <
      1 / Real.sqrt Real.pi :=
  abs_integral_sin_sq_lt_inv _ rfl _ (Real.sqrt_pos.2 Real.pi_pos)
