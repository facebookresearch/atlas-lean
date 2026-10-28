/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Composition of finite literal Coxeter certificates in the original C431 source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431CoxeterRewrites

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A finite chain of checked original-source moves proves equality of its boundary words. -/
theorem y431CoxeterChain_valid {n : ℕ} (words : Fin (n + 1) → List (Fin 9))
    (moves : Fin n → List Y431CoxeterMove)
    (h : ∀ i, y431CoxeterRun (moves i) (words i.castSucc) = some (words i.succ)) :
    y431PositiveWord (words 0) = y431PositiveWord (words (Fin.last n)) := by
  have hc (i : Fin (n + 1)) :
      y431PositiveWord (words i) = y431PositiveWord (words 0) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      exact (y431CoxeterRun_valid _ _ _ (h i)).symm.trans ih
  exact (hc (Fin.last n)).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
