/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92NonAlgebraic

open MathlibExt.GroupTheory.CompleteLatticeOfFormationsKourovka18Problem92Wanted

-- The proved statement is available under its original name.
example : nonAlgebraicCompleteLatticeOfFormations :=
  nonAlgebraicCompleteLatticeOfFormations_holds

-- Unfolded: some set of classes of groups is a complete lattice of formations
-- of finite groups and is not algebraic.
example : ∃ Θ : Set GroupClass, IsCompleteLatticeOfFormations Θ ∧ ¬ IsAlgebraicIn Θ :=
  nonAlgebraicCompleteLatticeOfFormations_holds
