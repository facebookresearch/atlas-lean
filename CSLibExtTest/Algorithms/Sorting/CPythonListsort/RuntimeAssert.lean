/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Init

namespace CPythonListsortTest

/-- An executable regression fails the test build without introducing theorem axioms. -/
def assertTrue (label : String) (value : Bool) : IO Unit := do
  unless value do
    throw (IO.userError (label ++ ": regression failed"))

end CPythonListsortTest
