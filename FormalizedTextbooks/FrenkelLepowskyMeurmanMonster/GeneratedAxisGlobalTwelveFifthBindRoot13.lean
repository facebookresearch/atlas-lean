/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindRoot13Binary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthDestinationEqualities
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue

/-! Both triality images at Fifth root thirteen lie in the twelve-family union.

Both triality signs of the Odd root-three transition are proved whole-vector Fifth axes, by the
two complete comparison words. Reversing the first: at the Fifth coset given by the inverse of
the first comparison word, the inverse triality image is the Odd root-three word image (Odd
class) and the forward triality image is the inverse triality image of that word, which is the
second comparison image (Fifth class). The binary matching of the module
`GeneratedAxisGlobalTwelveFifthBindRoot13Binary` then transfers both images to Fifth root
thirteen. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The first complete comparison word, inverted, is a genuine whole-vector transporter. -/
theorem generatedAxisGlobalTwelveFifthBind_root13_transport :
    sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis) =
      rhoLocal ((generatedAxisGlobalOddFifthComparisonLocal 0)⁻¹) generatedFifthAxis :=
  generatedAxisGlobalOddFifth_transporter 0

/-- Both triality images at the inverse first comparison word lie in the union. -/
theorem generatedAxisGlobalTwelveFifthBind_root13_comparison_pair :
    sExtra (rhoLocal ((generatedAxisGlobalOddFifthComparisonLocal 0)⁻¹) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal ((generatedAxisGlobalOddFifthComparisonLocal 0)⁻¹) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨h', hn⟩ := generatedAxisGlobalOddRoot03_negative_fifth_destination
  rw [← generatedAxisGlobalTwelveFifthBind_root13_transport]
  constructor
  · have h3 : sExtra (sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3)
        generatedOddAxis)) =
        sExtra.symm (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 3) generatedOddAxis) := by
      apply sExtra.injective
      rw [sExtra_triple, sExtra.apply_symm_apply]
    rw [h3]
    exact generatedAxisGlobalTwelve_mem_of_transport 4 h' hn
  · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport 2 _ rfl

/-- Both triality images at the inverse first comparison coset lie in the union. -/
theorem generatedAxisGlobalTwelveFifthBind_root13_coset_pair :
    sExtra (rhoLocal generatedAxisGlobalTwelveFifthBindRoot13Coset generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveFifthBindRoot13Coset generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have e : generatedAxisGlobalTwelveFifthBindRoot13Coset =
      (generatedAxisGlobalOddFifthComparisonLocal 0)⁻¹ := by
    unfold generatedAxisGlobalTwelveFifthBindRoot13Coset
    rfl
  rw [e]
  exact generatedAxisGlobalTwelveFifthBind_root13_comparison_pair

/-- Both triality images at Fifth root thirteen lie in the twelve-family union. -/
theorem generatedAxisGlobalTwelveFifthBind_root13 :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 13) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 13) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_root_pair_mem _ generatedFifthAxis
    generatedAxisGlobalTwelveFifthBindRoot13Coset (generatedAxisGlobalFifthShortLocalWord 13)
    generatedAxisGlobalTwelveFifthBindRoot13Transport.val
    generatedAxisGlobalTwelveFifthBindRoot13Transport.property
    generatedAxisGlobalTwelveFifthBindRoot13Transport_actual
    generatedAxisGlobalTwelveFifthBind_root13_coset_pair.1
    generatedAxisGlobalTwelveFifthBind_root13_coset_pair.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
