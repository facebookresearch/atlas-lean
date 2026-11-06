/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddPrototypeOrbits

/-! Both actual triality images of the Eighth representative lie in the twelve-family union.

The Eighth representative is `sExtra (L8 v_odd)` for the literal local word `L8` and the Odd
representative `v_odd`. Its inverse triality image is therefore literally `L8 v_odd`, a local
image of the Odd representative. Its positive triality image is the inverse image of
`L8 v_odd`; the actual binary root relation between `L8` and Odd root one, together with the
two actual Eighth destinations of that root, puts it in the union. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem sExtra_inv_eq_square' (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- The inverse triality image of the Eighth representative is a local image of the Odd one. -/
theorem generatedAxisGlobalTwelveEighth_inverse_mem :
    sExtra⁻¹ generatedEighthAxis ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply generatedAxisGlobalTwelve_mem_of_transport 2 (localFiberIntoH generatedEighthLocalFiber)
  rw [generatedEighthAxis_local_expression, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val]

/-- Both triality images of the local Odd image `L8 v_odd` lie in the catalogue union. -/
theorem generatedAxisGlobalTwelveEighth_odd_pair_mem :
    sExtra (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hrep : generatedAxisGlobalOddPrototypeAxis 2 =
      generatedAxisGlobalTwelveRepresentative 7 := by
    simp only [generatedAxisGlobalOddPrototypeAxis, generatedAxisGlobalTwelveRepresentative,
      Matrix.cons_val]
  have hp : sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddPrototypeRootIndex 2)) generatedOddAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_positive_orbit 2
    rw [hrep] at hk
    exact generatedAxisGlobalTwelve_mem_of_transport 7 k hk
  have hn : sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddPrototypeRootIndex 2)) generatedOddAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    obtain ⟨k, hk⟩ := generatedAxisGlobalOddPrototype_negative_orbit 2
    rw [hrep] at hk
    exact generatedAxisGlobalTwelve_mem_of_transport 7 k hk
  have hc : (generatedAxisGlobalOddPrototypeTransport 2).val⁻¹ ∈ generatedOddLocalAxisStabilizer :=
    generatedOddLocalAxisStabilizer.inv_mem (generatedAxisGlobalOddPrototypeTransport 2).property
  have hroot : generatedAxisGlobalBinaryAct (generatedAxisGlobalOddPrototypeTransport 2).val⁻¹
      (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedEighthLocalFiber)) =
        generatedAxisGlobalBinaryRoot (generatedAxisGlobalOddSourceRootLocalWord
          (generatedAxisGlobalOddPrototypeRootIndex 2)) := by
    have ha := generatedAxisGlobalOddPrototypeTransport_actual 2
    have hl : generatedAxisGlobalOddPrototypeLocal 2 =
        localFiberIntoH generatedEighthLocalFiber := by
      simp only [generatedAxisGlobalOddPrototypeLocal, Matrix.cons_val]
    rw [hl] at ha
    rw [← ha, ← generatedAxisGlobalBinaryAct_mul, inv_mul_cancel]
    apply Subtype.ext
    change co1BinaryAction (projH 1) _ = _
    rw [map_one, map_one]
    rfl
  exact generatedAxisGlobalTwelve_root_pair_mem generatedAxisGlobalTwelveRepresentative
    generatedOddAxis (generatedAxisGlobalOddSourceRootLocalWord
      (generatedAxisGlobalOddPrototypeRootIndex 2))
    (localFiberIntoH generatedEighthLocalFiber) (generatedAxisGlobalOddPrototypeTransport 2).val⁻¹
    hc hroot hp hn

/-- The positive triality image of the Eighth representative lies in the catalogue union. -/
theorem generatedAxisGlobalTwelveEighth_positive_mem :
    sExtra generatedEighthAxis ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have h := generatedAxisGlobalTwelveEighth_odd_pair_mem.2
  rw [sExtra_inv_eq_square', ← generatedEighthAxis_local_expression] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
