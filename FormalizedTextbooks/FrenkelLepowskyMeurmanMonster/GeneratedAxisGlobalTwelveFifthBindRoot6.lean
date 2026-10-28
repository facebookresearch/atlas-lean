/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent6a
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindIdent6b
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindTriangle

/-! # Fifth forest root 6: both triality images

The two packed identifications (I6+) and (I6-) at the one-xi representative `h₆` of the Fifth
root 6 (`GeneratedAxisGlobalTwelveFifthBindIdent6a`, `GeneratedAxisGlobalTwelveFifthBindIdent6b`)
put both triality images of `h₆ v₅` into the twelve local orbits; the explicit Fifth-axis fixers of
`GeneratedAxisGlobalTwelveFifthBindCosetBinary` transfer both images to the explicit Fifth root
word 6. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- Both triality images at the one-xi representative of the Fifth root 6 lie in the union. -/
theorem generatedAxisGlobalTwelveFifthBind_coset6_bound :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 2) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 2) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hc : generatedAxisGlobalTwelveFifthBindCoset 2 =
      identWordLocal generatedAxisGlobalTwelveFifthBind6pH := by
    rw [generatedAxisGlobalTwelveFifthBindCoset_eq_word, generatedAxisGlobalTwelveFifthBind6pH_eq]
  rw [hc, ← generatedAxisGlobalTwelveFifthBind_rep_four]
  exact ⟨generatedAxisGlobalTwelve_mem_of_transport 4 _ generatedAxisGlobalTwelveFifthBind6a_ident,
    generatedAxisGlobalTwelve_mem_of_transport 4 _ generatedAxisGlobalTwelveFifthBind6b_ident⟩

/-- Fifth forest root 6: both triality images of the explicit root word lie in the union. -/
theorem generatedAxisGlobalTwelveFifthBind_root6_bound :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 6) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 6) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveFifthBindCoset_transfer 2
    generatedAxisGlobalTwelveFifthBind_coset6_bound.1
    generatedAxisGlobalTwelveFifthBind_coset6_bound.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
