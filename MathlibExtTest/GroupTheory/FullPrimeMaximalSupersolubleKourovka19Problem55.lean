/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.GroupTheory.FullPrimeMaximalSupersolubleKourovka19Problem55

open MathlibExt.GroupTheory.FullPrimeMaximalSupersolubleKourovka19Problem55Wanted
open MathlibExt.GroupTheory.KourovkaNotebookShared

example : ∃ (G : Type) (_ : Group G) (_ : Finite G), Group.IsSolvable G ∧
    MaximalFullPrimeSupersoluble G ∧ ¬ FittingHeightLE G 3 :=
  fittingHeightUnbounded_holds 3
