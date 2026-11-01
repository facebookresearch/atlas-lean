/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddLineLifts

/-! Genuine full odd-axis-fixing lifts for every original binary forest generator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every original sign and source permutation preserves the genuine distinguished line. -/
theorem generatedAxisGlobalOddSpatial_line (k : Fin 14) :
    generatedAxisGlobalOddSpatial k ∈ generatedNormEightLineStabilizer := by
  by_cases h : k.val < 12
  · simp only [generatedAxisGlobalOddSpatial, h, ↓reduceDIte]
    exact generatedAxisGlobalOdd_sign_line _
  · simp only [generatedAxisGlobalOddSpatial, h, ↓reduceDIte]
    exact generatedAxisGlobalOdd_permutation_line _ (generatedAxisGlobalOddPermutation_zero _)

/-- Actual full-axis-fixing lifts with all extraspecial phase corrections retained. -/
def generatedAxisGlobalOddGenerator (k : Fin 14) : generatedOddLocalAxisStabilizer :=
  generatedAxisGlobalOddLineLift ⟨generatedAxisGlobalOddSpatial k,
    generatedAxisGlobalOddSpatial_line k⟩

/-- The lifts retain the original spatial Conway quotient classes. -/
theorem generatedAxisGlobalOddGenerator_projection (k : Fin 14) :
    projH (generatedAxisGlobalOddGenerator k).val =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalOddSpatial k) :=
  generatedAxisGlobalOddLineLift_projection _

/-- Every chosen edge fixes the entire actual odd axis. -/
theorem generatedAxisGlobalOddGenerator_fixed (k : Fin 14) :
    rhoLocal (generatedAxisGlobalOddGenerator k).val generatedOddAxis = generatedOddAxis :=
  (generatedAxisGlobalOddGenerator k).property

/-- Every chosen edge acts by its actual source binary matrix on the genuine Ω orbit. -/
theorem generatedAxisGlobalOddGenerator_binary (k : Fin 14)
    (x : generatedAxisGlobalBinaryOrbit) :
    (generatedAxisGlobalBinaryAct (generatedAxisGlobalOddGenerator k).val x).val =
      generatedAxisGlobalOddBinaryMatrix k *ᵥ x.val := by
  change co1BinaryAction (projH (generatedAxisGlobalOddGenerator k).val) x.val = _
  rw [generatedAxisGlobalOddGenerator_projection, generatedAxisGlobalOddSpatial_binary]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
