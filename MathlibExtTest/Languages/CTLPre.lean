/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.CTLPre

@[expose] public section

/-- The pre-image of the empty set is empty. -/
example (K : Kripke 2) : K.pre ∅ = ∅ := by
  ext s
  simp [Kripke.mem_pre]

end
