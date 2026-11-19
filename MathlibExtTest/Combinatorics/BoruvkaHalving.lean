/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.BoruvkaHalving

import Mathlib.Tactic.FinCases

@[expose] public section

/-- Constant merging on two components at most halves the count. -/
example : 2 * (Finset.univ.image (fun _ : Bool => false)).card ≤ Fintype.card Bool :=
  boruvka_halving (fun _ : Bool => false) (fun c => ⟨!c, by simp, rfl⟩)

end
