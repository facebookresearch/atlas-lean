/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoLogBalanced

namespace MetaMathlibExt

-- The unnormalized sequence satisfies the log-convexity inequality at index three.
example : genLeonardo 1 3 ^ 2 ≤ genLeonardo 1 2 * genLeonardo 1 4 :=
  leonardo_logBalanced_three.1

-- The factorial-normalized sequence satisfies the reverse inequality over the reals.
example :
    ((genLeonardo 1 2 : ℝ) / Nat.factorial 2) * ((genLeonardo 1 4 : ℝ) / Nat.factorial 4) ≤
      ((genLeonardo 1 3 : ℝ) / Nat.factorial 3) ^ 2 :=
  leonardo_logBalanced_three.2

end MetaMathlibExt
