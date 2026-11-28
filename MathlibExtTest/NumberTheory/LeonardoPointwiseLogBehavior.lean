/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPointwiseLogBehavior

namespace MetaMathlibExt

-- Evaluate the recurrence independently of the theorem: both convex cases are strict.
example : genLeonardo 1 1 ^ 2 < genLeonardo 1 0 * genLeonardo 1 2 := by decide
example : genLeonardo 1 3 ^ 2 < genLeonardo 1 2 * genLeonardo 1 4 := by decide

-- At the transition index, both sides are 225.
example : (genLeonardo 1 5 ^ 2, genLeonardo 1 4 * genLeonardo 1 6) = (225, 225) := by decide

-- Check the two exceptional concave cases and the first two indices of the tail.
example : genLeonardo 1 1 * genLeonardo 1 3 < genLeonardo 1 2 ^ 2 := by decide
example : genLeonardo 1 3 * genLeonardo 1 5 < genLeonardo 1 4 ^ 2 := by decide
example : genLeonardo 1 5 * genLeonardo 1 7 < genLeonardo 1 6 ^ 2 := by decide
example : genLeonardo 1 6 * genLeonardo 1 8 < genLeonardo 1 7 ^ 2 := by decide

-- A client uses the public theorem at the first index of the tail.
example : genLeonardo 1 5 * genLeonardo 1 7 ≤ genLeonardo 1 6 ^ 2 :=
  leonardo_logConvex_logConcave_pointwise.2.2 6 (Or.inr (Or.inr le_rfl))

end MetaMathlibExt
