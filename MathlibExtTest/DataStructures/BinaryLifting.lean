/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.DataStructures.BinaryLifting

@[expose] public section

/-- Lifting by zero steps is the identity. -/
example (parent : ℕ → ℕ) (x : ℕ) : up parent x 0 = x := rfl

/-- One step is the parent. -/
example (parent : ℕ → ℕ) (x : ℕ) : up parent x 1 = parent x := rfl

end
