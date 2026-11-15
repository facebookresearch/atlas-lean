/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.MinMaxPairs

@[expose] public section

/-- One pair costs three comparisons. -/
example : ([(3, 7)] |>.foldl minmaxStep (10, 0, 0)).2.2 = 3 := rfl

end
