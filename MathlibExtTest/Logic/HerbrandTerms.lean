/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.HerbrandTerms

@[expose] public section

/-- A variable is not ground. -/
example : ¬ Term.Ground (Term.var 0) := by
  simp [Term.Ground]

/-- A nullary application is ground. -/
example : Term.Ground (Term.app 0 []) := by
  simp [Term.Ground]

end
