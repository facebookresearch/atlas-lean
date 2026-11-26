/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibStepConvolutionFibStepGFMixedTriple

namespace MathlibExtTest.Combinatorics.Enumerative.FibStepConvolutionFibStepGFMixedTriple

open MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

-- Fibonacci and tribonacci factors with a tribonacci third factor.
example : PowerSeries.X ^ 2 * fibStepGF 2 * fibStepGF 3 * fibStepGF 3 =
    fibStepGF 3 * fibStepGF 3 - fibStepGF 3 * fibStepGF 2 :=
  fibStepGF_mixed_triple 2 3 (by decide) (by decide)

-- One-step and Fibonacci factors with a Fibonacci third factor.
example : PowerSeries.X * fibStepGF 1 * fibStepGF 2 * fibStepGF 2 =
    fibStepGF 2 * fibStepGF 2 - fibStepGF 2 * fibStepGF 1 := by
  simpa only [pow_one] using fibStepGF_mixed_triple (m := 1) (p := 2) (by decide) (by decide)

-- The same instance read in the symmetric direction.
example : fibStepGF 3 * fibStepGF 3 - fibStepGF 3 * fibStepGF 2 =
    PowerSeries.X ^ 2 * fibStepGF 2 * fibStepGF 3 * fibStepGF 3 :=
  (fibStepGF_mixed_triple 2 3 (by decide) (by decide)).symm

end MathlibExtTest.Combinatorics.Enumerative.FibStepConvolutionFibStepGFMixedTriple
