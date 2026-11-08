/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.SiftDownCost

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SiftDownCostTests

example {α : Type} [LinearOrder α] (a : Array α) (i : Nat) :
    (TimeM.siftDown a i).ret = Cslib.Algorithms.Lean.siftDown a i :=
  TimeM.ret_siftDown a i

end Cslib.Algorithms.Lean.SiftDownCostTests
