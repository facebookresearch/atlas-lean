/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort1Data
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationPairPhase

/-! Exact inverse physical pair labels retain the preferred vector sign. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The verified inverse coordinate array is injective. -/
theorem generatedFifth_permutation_short1_inverse_injective :
    Function.Injective generatedFifthPermutationShort1Inverse := by
  intro a b h
  apply (generatedFifthMonomialSpatialPermutation 1).val.symm.injective
  simpa only [generatedFifth_permutation_short1_inverse] using h

/-- The genuine ordered source pair of each preferred target pair. -/
def generatedFifthPermutationShort1PairSource (s : Fin 2)
    (p : {p : Fin 24 × Fin 24 // p.1 < p.2}) : generatedFifthXiShortCachedLabel :=
  let a := generatedFifthPermutationShort1Inverse p.val.1
  let b := generatedFifthPermutationShort1Inverse p.val.2
  have hn : a ≠ b := fun h => (ne_of_lt p.property)
    (generatedFifth_permutation_short1_inverse_injective h)
  if h : a < b then Sum.inl (s, ⟨(a, b), h⟩)
  else Sum.inl (s, ⟨(b, a), lt_of_le_of_ne (le_of_not_gt h) hn.symm⟩)

/-- Preferred physical vector sign caused by sorting the inverse pair. -/
def generatedFifthPermutationShort1PairPhysicalSign (s : Fin 2)
    (p : {p : Fin 24 × Fin 24 // p.1 < p.2}) : ℤ :=
  if generatedFifthPermutationShort1Inverse p.val.1 < generatedFifthPermutationShort1Inverse p.val.2
    then 1
  else if s = 0 then -1 else 1


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
