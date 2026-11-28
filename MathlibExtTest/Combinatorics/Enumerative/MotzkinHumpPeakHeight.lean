/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MotzkinHumpPeakHeight
import Mathlib.Data.Fin.VecNotation

namespace MetaMathlibExt

-- Both adjacent peaks in UDUD are humps of height one.
example :
    let p : Fin 4 → Fin 3 := ![2, 0, 2, 0]
    IsMotzkinPrefix 4 0 p ∧ IsMotzkinHump 4 1 p 0 1 ∧ IsMotzkinHump 4 1 p 2 3 := by
  decide

-- The prefix-height API counts vertical displacement, not steps, and stops at the end.
example :
    let p : Fin 4 → Fin 3 := ![2, 1, 2, 0]
    motzkinPrefixHeight p 0 = 0 ∧ motzkinPrefixHeight p 2 = 1 ∧
      motzkinPrefixHeight p 3 = 2 ∧ motzkinPrefixHeight p 6 = 1 := by
  decide

-- DU is a two-step return at height one and is unavailable at height zero.
example :
    sytHookCount_add_eq_humpCount_sub.walkCount 2 0 0 = 2 ∧
    sytHookCount_add_eq_humpCount_sub.walkCount 2 1 1 = 3 := by
  decide

end MetaMathlibExt
