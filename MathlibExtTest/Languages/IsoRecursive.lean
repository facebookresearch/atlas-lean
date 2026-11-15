/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.IsoRecursive

@[expose] public section

/-- The unit term is a value. -/
example : Value Tm.unit := Value.unit

/-- Unfolding a folded unit steps to the unit. -/
example : Step (Tm.unfold (Tm.fold Tm.unit)) Tm.unit :=
  Step.unfoldFold Value.unit

end
