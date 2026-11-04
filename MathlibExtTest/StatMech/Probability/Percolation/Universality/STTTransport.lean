/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.STTTransport

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.STTTransport`

* `starTriangle_reach_iff` on `Fin 4` with `E = ⊥`, corners `0, 1, 2`, centre `3`, and all edges
  open in both cells (`MatchesPattern` holds by `decide`): `0` and `1` are joined in both graphs.
-/

@[expose] public section

open StatMech StatMech.Universality

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.STTTransport

theorem matches_all : MatchesPattern (true, true, true) (true, true, true) :=
  ⟨rfl, rfl, rfl⟩

example : ((⊥ : SimpleGraph (Fin 4)) ⊔ triCell 0 1 2 (true, true, true)).Reachable 0 1 ↔
    ((⊥ : SimpleGraph (Fin 4)) ⊔ starCell 0 1 2 3 (true, true, true)).Reachable 0 1 :=
  starTriangle_reach_iff ⊥ 0 1 2 3 _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) matches_all (fun _ h => h.elim) (by decide) (by decide)

example : ((⊥ : SimpleGraph (Fin 4)) ⊔ starCell 0 1 2 3 (true, true, true)).Reachable 0 1 :=
  starCell_reach_AB ⊥ 0 1 2 3 _ (by decide) (by decide) (by decide)

end MathlibExtTest.StatMech.Probability.Percolation.Universality.STTTransport
