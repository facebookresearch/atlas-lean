/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.BranchLengthScore
import Mathlib.Tactic.NormNum

/-!
# Branch Length Score tests

On the three-species tree `((0 : 1, 1 : 2) : 3, 2 : 4)` (total length `10`): the tree is
well labeled with nonnegative lengths (the non-vacuity witness); the algorithm and the spec
give
`bls {0, 1} = 3` (the two sister branches), `bls {0, 2} = 8` (everything but the branch to `1`),
`bls {2} = 0`, `bls` of all leaves `= 10`; the normalized score of `{0, 2}` is `4 / 5`. A tree
with a repeated label shows why `blsAlg_eq_bls` assumes distinct labels.
-/

namespace Cslib.Bioinformatics.Phylogenetics.BranchLengthScore

open Tree

/-- The tree `((0 : 1, 1 : 2) : 3, 2 : 4)`. -/
noncomputable def t₃ : Tree ℕ := node 3 (node 1 (leaf 0) 2 (leaf 1)) 4 (leaf 2)

theorem t₃_wellLabeled : t₃.WellLabeled := by
  simp [t₃, WellLabeled, leaves]

theorem t₃_nonneg : t₃.NonnegLengths := by
  norm_num [t₃, NonnegLengths]

theorem t₃_total : t₃.totalLength = 10 := by
  norm_num [t₃, totalLength]

theorem t₃_leaves : t₃.leaves = {0, 1, 2} := by
  decide

/-- Two sister species: only their two branches. -/
example : bls {0, 1} t₃ = 3 := by
  rw [← blsAlg_eq_bls _ t₃_wellLabeled]
  norm_num [blsAlg, blsGo, markedCount, t₃]

/-- Species `0` and `2`: every branch except the one to `1`. -/
example : bls {0, 2} t₃ = 8 := by
  rw [← blsAlg_eq_bls _ t₃_wellLabeled]
  norm_num [blsAlg, blsGo, markedCount, t₃]

example : blsFrac {0, 2} t₃ = 4 / 5 := by
  rw [blsFrac, ← blsAlg_eq_bls _ t₃_wellLabeled, t₃_total]
  norm_num [blsAlg, blsGo, markedCount, t₃]

example : bls {2} t₃ = 0 := bls_singleton 2 t₃

example : bls t₃.leaves t₃ = 10 := by
  rw [bls_leaves t₃_wellLabeled, t₃_total]

example : bls {0, 1} t₃ ≤ bls {0, 1, 2} t₃ :=
  bls_mono (by decide) t₃_nonneg

/-- With a repeated label the algorithm and the spec disagree: on `(0 : 1, 0 : 1)` with
`S = {0}` the post-order pass counts two marked leaves, one on each side of each branch, and
returns `2`, while the leaf set is `{0}` and the spec returns `0`. This is why
`blsAlg_eq_bls` assumes distinct labels. -/
example : blsAlg {0} (node 1 (leaf 0) 1 (leaf 0) : Tree ℕ) = 2 := by
  norm_num [blsAlg, blsGo, markedCount]

example : bls {0} (node 1 (leaf 0) 1 (leaf 0) : Tree ℕ) = 0 := bls_singleton 0 _

end Cslib.Bioinformatics.Phylogenetics.BranchLengthScore
