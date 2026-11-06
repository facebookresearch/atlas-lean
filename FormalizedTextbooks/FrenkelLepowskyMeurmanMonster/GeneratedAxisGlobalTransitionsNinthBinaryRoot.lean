/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortInputs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions

/-! A bounded actual binary word attaches the literal ninth prototype to
fifth transition root five. No full singular-forest coverage is required. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original hyperbolic coordinates of the inverse ninth-word image of Ω. -/
def generatedAxisGlobalNinthBinaryPoint : Fin 24 → ZMod 2 :=
  monsterCo1GeometryBinaryMaskDecode (n := 24) 7221600

private theorem xiBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction co1XiIsometry v = omegaOrbitBinaryMatrices 0 *ᵥ v :=
  omegaOrbitIsometry_binary 0 v

private theorem permutationZeroBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 0) v = omegaOrbitBinaryMatrices 3 *ᵥ v :=
  omegaOrbitIsometry_binary 3 v

private theorem permutationOneBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 1) v = omegaOrbitBinaryMatrices 4 *ᵥ v :=
  omegaOrbitIsometry_binary 4 v

set_option maxHeartbeats 10000000 in
-- Check the original nine-factor action on all 24 actual binary coordinates.
/-- The literal ninth local word carries the exact displayed point to Ω. -/
theorem generatedAxisGlobalNinthBinaryPoint_actual :
    co1BinaryAction (projH (localFiberIntoH generatedNinthLocalFiber))
      generatedAxisGlobalNinthBinaryPoint = Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
  change leechBinaryAction generatedNinthLocalFiber.val.2 _ = _
  rw [generatedNinth_local_spatial]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [xiBinary, permutationZeroBinary, permutationOneBinary]
  decide +kernel

private theorem binaryRootOfAction (h : H) (x : Fin 24 → ZMod 2)
    (hx : co1BinaryAction (projH h) x = Multiplicative.toAdd (qQuotHom sourceOmegaQ)) :
    (generatedAxisGlobalBinaryRoot h).val = x := by
  change co1BinaryAction (projH h⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = x
  rw [map_inv, map_inv, ← hx]
  exact LinearEquiv.symm_apply_apply _ _

/-- The displayed coordinate point is the genuine binary root of the literal ninth word. -/
theorem generatedAxisGlobalNinthBinaryRoot_actual :
    (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedNinthLocalFiber)).val =
      generatedAxisGlobalNinthBinaryPoint :=
  binaryRootOfAction _ _ generatedAxisGlobalNinthBinaryPoint_actual

/-- Five genuine full-axis stabilizer lifts transport root five to the ninth binary point. -/
def generatedAxisGlobalNinthRootTransport : generatedFifthLocalAxisStabilizer :=
  generatedAxisGlobalFifthGenerator 4 * generatedAxisGlobalFifthGenerator 15 *
    generatedAxisGlobalFifthGenerator 17 * generatedAxisGlobalFifthGenerator 9 *
    generatedAxisGlobalFifthGenerator 2

set_option maxHeartbeats 10000000 in
-- Five actual binary matrix actions, checked on the complete 24-coordinate point.
/-- The exact five-letter stabilizer word transports the actual fifth root to the ninth root. -/
theorem generatedAxisGlobalNinthRootTransport_actual :
    generatedAxisGlobalBinaryAct generatedAxisGlobalNinthRootTransport.val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 5)) =
        generatedAxisGlobalBinaryRoot (localFiberIntoH generatedNinthLocalFiber) := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalNinthBinaryRoot_actual]
  change (generatedAxisGlobalBinaryAct
    (((generatedAxisGlobalFifthGenerator 4).val * (generatedAxisGlobalFifthGenerator 15).val *
      (generatedAxisGlobalFifthGenerator 17).val * (generatedAxisGlobalFifthGenerator 9).val *
      (generatedAxisGlobalFifthGenerator 2).val)) (generatedAxisGlobalFifthRoot 5)).val = _
  simp only [generatedAxisGlobalBinaryAct_mul]
  simp_rw [generatedAxisGlobalFifthGenerator_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
