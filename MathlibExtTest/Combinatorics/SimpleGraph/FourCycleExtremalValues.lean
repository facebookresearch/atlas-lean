/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValues

open SimpleGraph
open MathlibExt.Combinatorics.SimpleGraph.FourCycleExtremalValuesWanted

-- The first order where a copy of the forbidden cycle can occur.
example : extremalNumber 4 (cycleGraph 4) = 4 :=
  Option.some.inj (congrArg (fun xs : List ℕ => xs[3]?)
    extremalNumber_cycleGraph_four_one_to_twenty)

-- The final entry of the table.
example : extremalNumber 20 (cycleGraph 4) = 46 :=
  Option.some.inj (congrArg (fun xs : List ℕ => xs[19]?)
    extremalNumber_cycleGraph_four_one_to_twenty)
