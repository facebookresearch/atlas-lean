/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.Adleman
import CSLibExt.Computability.Complexity.BoolClosure

namespace MetaMathlibExt.Complexity.KeyTheorems.Adleman.Test

open BitstringEncoding ComplexityTheory

private def headsAgree (q : List Bool × List Bool) : Bool :=
  q.2.headD false == q.1.headD false

example : IsPolyTime (majorityVerifier headsAgree) :=
  isPolyTime_majorityVerifier (isPolyTime_heads (· == ·))

example : majorityVerifier headsAgree ([true],
    ([ [false], [true], [true] ].map delimit).flatten) = true := rfl

example : majorityVerifier headsAgree ([true],
    ([ [true], [false] ].map delimit).flatten) = false := rfl

-- A delimiter represents one trial with no coin bits.
example : majorityVerifier headsAgree ([], [false]) = true := rfl

example : majorityVerifier headsAgree ([], []) = false := rfl

-- The first trial succeeds, and the trailing frame is incomplete.
example : majorityVerifier headsAgree ([], [false, true]) = false := rfl

end MetaMathlibExt.Complexity.KeyTheorems.Adleman.Test
