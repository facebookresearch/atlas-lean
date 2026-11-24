/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.GenocchiLucasVanishing
import MathlibExt.NumberTheory.GenocchiBernoulli

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open MetaMathlibExt

-- At exponent zero the ordinary convolution contributes zero and the correction term survives.
example : genLucasCoeff 0 = 2 * Real.sqrt 5 := by
  norm_num [genLucasCoeff, genocchiNumber_eq_bernoulli, bernoulli_one]

-- The first admissible exponent gives a two-term cancellation.
example : genLucasCoeff 0 * (-fibBeta) + genLucasCoeff 1 = 0 := by
  simpa [Finset.sum_range_succ] using sum_genLucasCoeff_neg_fibBeta 1 le_rfl

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
