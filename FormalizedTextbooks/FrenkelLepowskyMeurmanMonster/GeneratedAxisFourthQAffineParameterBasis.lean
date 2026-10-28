/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQBinaryGenerators

/-! Seven actual Q generators suffice to verify membership of the entire counted affine subgroup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual seven-coordinate group map into the original extraspecial group Q. -/
def generatedFourthQAffineParameterMap : Multiplicative (Fin 7 → ZMod 2) →* Q :=
  (generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
    generatedAxisFourthQAffineParameterBases
    generatedAxisFourthQAffineParameterCharacters).subtype.comp
      generatedFourthQAffineParameterGroupEquiv.symm.toMonoidHom

/-- The seven genuine Q elements obtained from the seven free binary coordinate vectors. -/
def generatedFourthQAffineParameterBasis (i : Fin 7) : Q :=
  generatedFourthQAffineParameterMap (Multiplicative.ofAdd (Pi.single i 1))

/-- If a genuine Q subgroup contains the seven actual generators, it contains the whole family. -/
theorem generatedFourthQAffineParameterBasis_generates (H : Subgroup Q)
    (hH : ∀ i : Fin 7, generatedFourthQAffineParameterBasis i ∈ H) :
    generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases
      generatedAxisFourthQAffineParameterCharacters ≤ H := by
  have htop : H.comap generatedFourthQAffineParameterMap = ⊤ :=
    generatedFourthQBinaryBasis_generates 7 (H.comap generatedFourthQAffineParameterMap) hH
  intro q hq
  let x : generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases
      generatedAxisFourthQAffineParameterCharacters := ⟨q, hq⟩
  have hw : generatedFourthQAffineParameterGroupEquiv x ∈
      H.comap generatedFourthQAffineParameterMap := by
    rw [htop]
    trivial
  have he : generatedFourthQAffineParameterMap
      (generatedFourthQAffineParameterGroupEquiv x) = q := by
    change (generatedFourthQAffineParameterGroupEquiv.symm
      (generatedFourthQAffineParameterGroupEquiv x)).val = q
    rw [MulEquiv.symm_apply_apply]
  change generatedFourthQAffineParameterMap (generatedFourthQAffineParameterGroupEquiv x) ∈ H at hw
  rwa [he] at hw

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
