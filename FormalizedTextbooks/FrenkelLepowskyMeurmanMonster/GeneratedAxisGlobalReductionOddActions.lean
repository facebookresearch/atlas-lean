/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions

/-! Fourteen genuine spatial actions for the odd-family reduction certificate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Twelve original Golay signs followed by two literal coordinate-zero-fixing permutations. -/
def generatedAxisGlobalOddSpatial (k : Fin 14) : leechIsomSubgroup :=
  if h : k.val < 12 then monsterCo1GeometrySignIsometry ⟨k.val, h⟩
  else golayPermutationIsometry (generatedAxisGlobalOddPermutation ⟨k.val - 12, by omega⟩)

/-- Their matrices in the genuine hyperbolic coordinates of the extraspecial quotient. -/
def generatedAxisGlobalOddBinaryMatrix (k : Fin 14) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  if h : k.val < 12 then monsterCo1GeometrySignBinary ⟨k.val, h⟩
  else generatedAxisGlobalOddPermutationBinary ⟨k.val - 12, by omega⟩

/-- Every matrix is the actual Conway quotient action of the stated original spatial element. -/
theorem generatedAxisGlobalOddSpatial_binary (k : Fin 14) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (QuotientGroup.mk' signsSubgroup (generatedAxisGlobalOddSpatial k)) v =
      generatedAxisGlobalOddBinaryMatrix k *ᵥ v := by
  by_cases h : k.val < 12
  · simp only [generatedAxisGlobalOddSpatial, generatedAxisGlobalOddBinaryMatrix,
      h, ↓reduceDIte]
    exact monsterCo1GeometrySign_binary _ _
  · simp only [generatedAxisGlobalOddSpatial, generatedAxisGlobalOddBinaryMatrix,
      h, ↓reduceDIte]
    exact generatedAxisGlobalOddPermutation_binary _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
