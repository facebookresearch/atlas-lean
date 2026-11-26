/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.OverwriteNewestRegister

/-! # Fixtures for finite overwrite-newest register histories -/

namespace Cslib.Distributed.OverwriteNewestRegister

open Cslib.Semantics.Peripheral.OverwriteSampleRegister (readIds)

-- No value or equality instance is needed to run a history of reads.
example : run ([] : List (Operation Empty)) = ([], none) := rfl

example : run ([.read] : List (Operation Empty)) = ([.read none], none) := rfl

-- The first read consumes the slot; the second returns nothing.
example {α : Type*} (v : α) :
    run [.publish v, .read, .read] = ([.publish 1 v, .read (some (1, v)), .read none], none) :=
  rfl

-- The intervening read consumes publication 1 before publication 2 can overwrite it.
example {α : Type*} (a b : α) :
    run [.publish a, .read, .publish b, .read] =
      ([.publish 1 a, .read (some (1, a)), .publish 2 b, .read (some (2, b))], none) :=
  rfl

private def mixedHistory : List (Operation Bool) :=
  [.publish true, .read, .publish false, .publish true, .read, .publish false]

-- Publication 2 is immediately overwritten by 3; the two successful reads return the same
-- value at distinct, nonconsecutive numbers. Publication 4 remains in the final slot.
example : run mixedHistory =
    ([.publish 1 true, .read (some (1, true)), .publish 2 false, .publish 3 true,
      .read (some (3, true)), .publish 4 false], some (4, false)) := rfl

example : readIds (run mixedHistory).1 = [1, 3] := rfl

example : publications mixedHistory = [true, false, true, false] := rfl

end Cslib.Distributed.OverwriteNewestRegister
