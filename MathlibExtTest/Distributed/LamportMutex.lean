/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.LamportMutex

@[expose] public section

/-- The earliest request in a two-request set is granted. -/
example : IsGranted {(1, 0), (2, 0)} (1, 0) := by decide

/-- Any granted request in that set equals `(1, 0)`. -/
example (r : ℕ × ℕ) (hr : IsGranted {(1, 0), (2, 0)} r) : r = (1, 0) :=
  granted_unique _ r (1, 0) hr (by decide)

end
