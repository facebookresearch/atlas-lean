/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsNinthDestination
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsNinthBinaryRoot

/-! Both actual triality images of the Ninth representative lie in the twelve-family union.

The Ninth representative is `sExtra (L9 v5)` for the literal local word `L9` and the Fifth
representative `v5`. Its inverse triality image is therefore literally `L9 v5`, a local image
of the Fifth representative. Its positive triality image is the inverse image of `L9 v5`;
the actual binary root relation between `L9` and Fifth root five, together with the two
actual Ninth destinations of that root, puts it in the union. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Inverse triality is triality applied twice. -/
theorem generatedAxisGlobalTwelveNinth_sExtra_inv_eq_square (y : GriessSpace) :
    sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- The inverse triality image of the Ninth representative is a local image of the Fifth one. -/
theorem generatedAxisGlobalTwelveNinth_inverse_mem :
    sExtra⁻¹ generatedNinthAxis ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply generatedAxisGlobalTwelve_mem_of_transport 4 (localFiberIntoH generatedNinthLocalFiber)
  rw [generatedNinthAxis_local_expression, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  simp only [generatedAxisGlobalTwelveRepresentative, Matrix.cons_val]

/-- Both triality images of the local Fifth image `L9 v5` lie in the catalogue union. -/
theorem generatedAxisGlobalTwelveNinth_fifth_pair_mem :
    sExtra (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (localFiberIntoH generatedNinthLocalFiber) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have hp : sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
    generatedAxisGlobalTwelve_fifth_root05_positive
  have hn : sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 5) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
    generatedAxisGlobalTwelve_mem_of_class 8 generatedAxisGlobalFifthRoot05_negative_destination
  have hc : (generatedAxisGlobalNinthRootTransport.val)⁻¹ ∈ generatedFifthLocalAxisStabilizer :=
    generatedFifthLocalAxisStabilizer.inv_mem generatedAxisGlobalNinthRootTransport.property
  have hroot : generatedAxisGlobalBinaryAct (generatedAxisGlobalNinthRootTransport.val)⁻¹
      (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedNinthLocalFiber)) =
        generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 5) := by
    rw [← generatedAxisGlobalNinthRootTransport_actual, ← generatedAxisGlobalBinaryAct_mul,
      inv_mul_cancel]
    apply Subtype.ext
    change co1BinaryAction (projH 1) _ = _
    rw [map_one, map_one]
    rfl
  exact generatedAxisGlobalTwelve_root_pair_mem generatedAxisGlobalTwelveRepresentative
    generatedFifthAxis (generatedAxisGlobalFifthShortLocalWord 5)
    (localFiberIntoH generatedNinthLocalFiber) (generatedAxisGlobalNinthRootTransport.val)⁻¹
    hc hroot hp hn

/-- The positive triality image of the Ninth representative lies in the catalogue union. -/
theorem generatedAxisGlobalTwelveNinth_positive_mem :
    sExtra generatedNinthAxis ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have h := generatedAxisGlobalTwelveNinth_fifth_pair_mem.2
  rw [generatedAxisGlobalTwelveNinth_sExtra_inv_eq_square,
    ← generatedNinthAxis_local_expression] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
