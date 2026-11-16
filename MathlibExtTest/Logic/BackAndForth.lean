/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.BackAndForth

@[expose] public section

/-- No pairs have been played: the empty position is a partial
isomorphism for any two relations. -/
example {n m : ℕ} (R : Fin n → Fin n → Bool) (S : Fin m → Fin m → Bool) :
    PartialIso R S [] := by
  constructor <;> intro p hp <;> simp at hp

end
