/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddForestRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddInverseActions
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddForestRankData

/-! Local finite descent obligations for the actual odd-axis binary forest.
The root list and inverse operators are already bound to genuine lattice and
local stabilizer data. The rank inequalities must be kernel checked separately. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact sixteen roots of the singular forest in genuine coordinate masks. -/
def generatedAxisGlobalOddForestRootMasks : List ℕ :=
  [0, 3, 2049, 4096, 122880, 8388608, 8392710, 1, 17, 19, 258, 1106, 2048, 28672,
    8388609, 8388688]

/-- The computational root list has exactly the already proved genuine root meanings. -/
theorem generatedAxisGlobalOddForestRootMasks_eq :
    generatedAxisGlobalOddForestRootMasks = List.ofFn generatedAxisGlobalOddForestRootMask :=
  by decide +kernel

/-- Root membership in the finite list is exactly membership in the genuine root family. -/
theorem generatedAxisGlobalOddForestRootMasks_mem (b : ℕ) :
    b ∈ generatedAxisGlobalOddForestRootMasks ↔
      ∃ k : Fin 16, generatedAxisGlobalOddForestRootMask k = b := by
  rw [generatedAxisGlobalOddForestRootMasks_eq, List.mem_ofFn]

/-- One local arithmetic obligation: a singular mask is a genuine root or has
an actual inverse-generator parent of strictly smaller proposed natural rank. -/
def generatedAxisGlobalOddForestStep (edge b : ℕ) : Prop :=
  generatedAxisGlobalMaskSingular b = true →
    (edge = 31 ∧ b ∈ generatedAxisGlobalOddForestRootMasks) ∨
    (edge < 14 ∧ generatedAxisGlobalOddForestRank
      (generatedAxisGlobalMaskRowsAction
        (generatedAxisGlobalOddInverseRows ⟨edge % 14, Nat.mod_lt _ (by decide)⟩) b) <
          generatedAxisGlobalOddForestRank b)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
