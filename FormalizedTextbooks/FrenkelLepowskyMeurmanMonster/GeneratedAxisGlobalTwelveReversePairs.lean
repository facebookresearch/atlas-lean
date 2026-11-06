/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs

/-! Reverse bindings from a covered family.

If a listed family is covered and one of its actual triality transitions is an explicit
local image of another listed representative, then both triality images at the corresponding
coset of the second family lie in the twelve-family union: one sign returns to the covered
family and the other is the opposite-sign transition of that family. Combined with
`generatedAxisGlobalTwelve_root_pair_mem`, every root of the second family that is related to
such a coset by an actual binary root transport is then bound without a new whole-vector
identification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sExtra_inv_eq_square'' (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- A covered family sends both triality signs of each local image into the union. -/
theorem generatedAxisGlobalTwelve_covered_inverse {i : Fin 12}
    (hcov : GeneratedAxisGlobalTwelveFamilyCovered i) (h : H) :
    sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hm := hcov (inclQ singletonCocodeQ * h)
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange] at hm
  exact generatedAxisGlobalTwelve_union_mem_of_local _ (inclQ singletonCocodeQ) hm rfl

/-- A forward transport from a covered family binds both images at the target coset. -/
theorem generatedAxisGlobalTwelve_reverse_pair_of_positive {i j : Fin 12} {r h : H}
    (hcov : GeneratedAxisGlobalTwelveFamilyCovered i)
    (htr : sExtra (rhoLocal r (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htr]
  refine ⟨?_, ?_⟩
  · rw [← sExtra_inv_eq_square'']
    exact generatedAxisGlobalTwelve_covered_inverse hcov r
  · rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact ⟨i, r, rfl⟩

/-- An inverse transport from a covered family binds both images at the target coset. -/
theorem generatedAxisGlobalTwelve_reverse_pair_of_negative {i j : Fin 12} {r h : H}
    (hcov : GeneratedAxisGlobalTwelveFamilyCovered i)
    (htr : sExtra⁻¹ (rhoLocal r (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [← htr]
  refine ⟨?_, ?_⟩
  · rw [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact ⟨i, r, rfl⟩
  · rw [sExtra_inv_eq_square'' (sExtra⁻¹ _), LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact hcov r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
