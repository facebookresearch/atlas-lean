/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The source three-bases operator in the actual local group and generated G.
Source: Seysen, arXiv:2002.10921v3, §§9.3–9.5. The two concrete operators
are paired only after checking their actions on the actual Leech quotient.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinBinaryAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderXiBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalLocal

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check the 576 entries using the actual grey code/cocode and integral Leech matrices.
/-- The explicit spin action is the actual Leech isometry's binary action. -/
theorem xiSpinBinaryMatrix_leech :
    xiSpinBinaryMatrix = leechHyperbolicInverse *
      co1XiBasisMatrix.map (Int.castRingHom (ZMod 2)) * leechHyperbolicMatrix := by
  decide +kernel

/-- The source spin and Leech operators have equal actions on Q/Z(Q)=Λ/2Λ. -/
theorem xiSpin_leech_compatibility :
    spinBinaryAction xiSpinHolomorph = leechBinaryAction co1XiIsometry := by
  apply LinearEquiv.toLinearMap_injective
  rw [xiSpinBinaryAction_matrix, xiSpinBinaryMatrix_leech]
  apply LinearMap.ext
  intro v
  exact (co1Xi_binaryAction v).symm

/-- The actual three-bases pair in the defining fiber product. -/
noncomputable def xiSpinLocalFiber : localFiberSubgroup :=
  ⟨(xiSpinHolomorph, co1XiIsometry), xiSpin_leech_compatibility⟩

/-- Its image in the actual simultaneous-sign quotient H. -/
noncomputable def xiSpinLocal : H := QuotientGroup.mk' localDiagonalSubgroup xiSpinLocalFiber

/-- The actual three-bases generator in G, via the proved local embedding. -/
noncomputable def xiSpinGenerated : ↥G := localIntoGenerated xiSpinLocal

/-- Both components of the actual fiber element satisfy the source cube relation. -/
theorem xiSpinLocalFiber_cube : xiSpinLocalFiber ^ 3 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact xiSpinHolomorph_cube
  · exact co1XiIsometry_cube

/-- The local source generator satisfies ξ³=1 in the actual quotient H. -/
theorem xiSpinLocal_cube : xiSpinLocal ^ 3 = 1 := by
  change (QuotientGroup.mk' localDiagonalSubgroup xiSpinLocalFiber) ^ 3 = _
  rw [← map_pow, xiSpinLocalFiber_cube, map_one]

/-- The named generated group contains the verified source three-bases operator. -/
theorem xiSpinGenerated_cube : xiSpinGenerated ^ 3 = 1 := by
  rw [xiSpinGenerated, ← map_pow, xiSpinLocal_cube, map_one]

/-- Conjugation by the actual local ξ has the explicit source action on every q in Q. -/
theorem xiSpinLocal_conjugation (q : Q) :
    xiSpinLocal * inclQ q * xiSpinLocal⁻¹ =
      inclQ (xiSpinGImage (xiSpinGammaImage q)) := by
  have h := localFiberIncl_conjugate xiSpinLocalFiber q
  change localFiberIncl (spinConjugation xiSpinHolomorph q) =
    xiSpinLocalFiber * localFiberIncl q * xiSpinLocalFiber⁻¹ at h
  rw [xiSpinHolomorph_conjugation] at h
  have hquot := congrArg (QuotientGroup.mk' localDiagonalSubgroup) h
  rw [map_mul, map_mul, map_inv] at hquot
  exact hquot.symm

/-- The verified source conjugation law holds in the named generated group G. -/
theorem xiSpinGenerated_conjugation (q : Q) :
    xiSpinGenerated * qIntoGenerated q * xiSpinGenerated⁻¹ =
      qIntoGenerated (xiSpinGImage (xiSpinGammaImage q)) := by
  unfold xiSpinGenerated qIntoGenerated
  simp only [MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul, xiSpinLocal_conjugation]

/-- The actual generated-group ξ moves a specific genuine Q element. -/
theorem xiSpinGenerated_ne_one : xiSpinGenerated ≠ 1 := by
  intro hxi
  have h := xiSpinGenerated_conjugation (xiSpinBinaryBasisLift 10)
  rw [hxi, inv_one, one_mul, mul_one] at h
  have hq := qIntoGenerated_injective h
  have hbit : Multiplicative.toAdd
      (xiSpinGImage (xiSpinGammaImage (xiSpinBinaryBasisLift 10))).base 10 = 0 := by
    decide +kernel
  have hc := congrArg (fun q : Q => Multiplicative.toAdd q.base 10) hq
  change 1 = Multiplicative.toAdd
    (xiSpinGImage (xiSpinGammaImage (xiSpinBinaryBasisLift 10))).base 10 at hc
  rw [hbit] at hc
  exact one_ne_zero hc

/-- The source three-bases witness has exact order three in the named G. -/
theorem xiSpinGenerated_order : orderOf xiSpinGenerated = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime xiSpinGenerated_cube xiSpinGenerated_ne_one

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
