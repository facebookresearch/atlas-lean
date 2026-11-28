/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperLeonardoLogConcave

namespace MetaMathlibExt

-- Order one at the first covered index and at the following index.
example : hyperLeonardo 1 1 * hyperLeonardo 1 3 ≤ hyperLeonardo 1 2 ^ 2 := by decide
example : hyperLeonardo 1 2 * hyperLeonardo 1 4 ≤ hyperLeonardo 1 3 ^ 2 := by decide

-- The boundary at index two persists after taking partial sums again.
example : hyperLeonardo 2 1 * hyperLeonardo 2 3 ≤ hyperLeonardo 2 2 ^ 2 := by decide
example : hyperLeonardo 3 3 * hyperLeonardo 3 5 ≤ hyperLeonardo 3 4 ^ 2 := by decide

-- Neither lower bound can simply be dropped: the gaps are negative in these two cases.
example : hyperLeonardo 1 1 ^ 2 < hyperLeonardo 1 0 * hyperLeonardo 1 2 := by decide
example : hyperLeonardo 0 3 ^ 2 < hyperLeonardo 0 2 * hyperLeonardo 0 4 := by decide

-- A client of the public API at order two, index three.
example : hyperLeonardo 2 2 * hyperLeonardo 2 4 ≤ hyperLeonardo 2 3 ^ 2 :=
  hyperLeonardo_logConcave (r := 2) (n := 3) (by decide) (by decide)

-- Check the Cassini-type identity independently at the lowest order and middle index.
example : hyperLeonardo 1 0 * hyperLeonardo 1 2 - hyperLeonardo 1 1 ^ 2 =
    hyperLeonardo 1 1 * hyperLeonardo 0 2 - hyperLeonardo 0 1 * hyperLeonardo 1 2 := by decide

-- Both sides can be negative: at order two and middle index two they equal `-10`.
example :
    (hyperLeonardo 2 1 * hyperLeonardo 2 3 - hyperLeonardo 2 2 ^ 2,
      hyperLeonardo 2 2 * hyperLeonardo 1 3 - hyperLeonardo 1 2 * hyperLeonardo 2 3) =
        (-10, -10) := by decide

-- A client of the order-one theorem at the first covered index.
example : hyperLeonardo 1 1 * hyperLeonardo 1 3 ≤ hyperLeonardo 1 2 ^ 2 :=
  hyperLeonardo_one_logConcave 2 (by decide)

end MetaMathlibExt
