/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthForestRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthInverseActions
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthForestRankData

/-! Local finite descent obligations for the actual fifth-axis binary forest.
The root list and inverse operators are already bound to genuine lattice and
local stabilizer data. The rank inequalities must be kernel checked separately. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact twenty-two roots of the singular forest in genuine coordinate masks. -/
def generatedAxisGlobalFifthForestRootMasks : List ℕ :=
  [0, 3, 5, 16, 106, 284, 2052, 196608, 1, 4, 17, 22, 96, 97, 176, 177, 272, 273,
    274, 2048, 2051, 196612]

/-- The computational root list has exactly the already proved genuine root meanings. -/
theorem generatedAxisGlobalFifthForestRootMasks_eq :
    generatedAxisGlobalFifthForestRootMasks = List.ofFn generatedAxisGlobalFifthForestRootMask :=
  by decide +kernel

/-- Root membership in the finite list is exactly membership in the genuine root family. -/
theorem generatedAxisGlobalFifthForestRootMasks_mem (b : ℕ) :
    b ∈ generatedAxisGlobalFifthForestRootMasks ↔
      ∃ k : Fin 22, generatedAxisGlobalFifthForestRootMask k = b := by
  rw [generatedAxisGlobalFifthForestRootMasks_eq, List.mem_ofFn]

/-- One local arithmetic obligation: a singular mask is a genuine root or has
an actual inverse-generator parent of strictly smaller proposed natural rank. -/
def generatedAxisGlobalFifthForestStep (edge b : ℕ) : Prop :=
  generatedAxisGlobalMaskSingular b = true →
    (edge = 31 ∧ b ∈ generatedAxisGlobalFifthForestRootMasks) ∨
    (edge < 19 ∧ generatedAxisGlobalFifthForestRank
      (generatedAxisGlobalMaskRowsAction
        (generatedAxisGlobalFifthInverseRows ⟨edge % 19, Nat.mod_lt _ (by decide)⟩) b) <
          generatedAxisGlobalFifthForestRank b)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
