/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.InfiniteWord.KimberlingBlock

namespace MetaMathlibExt

example : kimberlingMorphism false = [true, true] := rfl
example : kimberlingMorphism true = [true, true, false] := rfl
example : kimberlingBlock 0 = [true] := rfl

example : kimberlingBlock 2 = [true, true, false, true, true, false, true, true] := by
  rw [kimberlingBlock_eq_append (by decide : 2 ≤ 2)]
  rfl

example : (kimberlingBlock 3).length = 22 := by
  rw [kimberlingBlock_eq_append (by decide : 2 ≤ 3)]
  rfl

end MetaMathlibExt
