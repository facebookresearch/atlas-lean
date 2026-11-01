/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineGroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineParameterCard

/-! Seven free binary coordinates describe the actual common affine-state stabilizer as a group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The explicit syndrome-kernel bijection is linear over the binary field. -/
def generatedFourthQParameterLinearEquiv :
    generatedFourthQParameterSpace ≃ₗ[ZMod 2] (Fin 7 → ZMod 2) where
  toEquiv := generatedFourthQParameterEquiv
  map_add' w v := by
    change generatedFourthQParameterProjection *ᵥ (w.val + v.val) =
      generatedFourthQParameterProjection *ᵥ w.val + generatedFourthQParameterProjection *ᵥ v.val
    exact Matrix.mulVec_add _ _ _
  map_smul' c w := by
    change generatedFourthQParameterProjection *ᵥ (c • w.val) =
      c • (generatedFourthQParameterProjection *ᵥ w.val)
    exact (Matrix.toLin' generatedFourthQParameterProjection).map_smul c w.val

/-- Reading the literal translation and modulation coordinates is a binary linear equivalence. -/
def generatedAxisFourthQAffineParameterLinearEquiv :
    generatedAxisFourthQAffineFamilyKernel generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases
      generatedAxisFourthQAffineParameterCharacters 0 ≃ₗ[ZMod 2]
        generatedFourthQParameterSpace where
  toEquiv := generatedAxisFourthQAffineParameterEquiv
  map_add' p q := by
    apply Subtype.ext
    change generatedAxisFourthQAffineParameterEncode (p.val + q.val) =
      generatedAxisFourthQAffineParameterEncode p.val +
        generatedAxisFourthQAffineParameterEncode q.val
    funext i
    induction i using Fin.addCases (m := 2) (n := 12) with
    | left i => fin_cases i <;> rfl
    | right i => simp [generatedAxisFourthQAffineParameterEncode, Fin.append_right]
  map_smul' c p := by
    apply Subtype.ext
    change generatedAxisFourthQAffineParameterEncode (c • p.val) =
      c • generatedAxisFourthQAffineParameterEncode p.val
    funext i
    induction i using Fin.addCases (m := 2) (n := 12) with
    | left i => fin_cases i <;> rfl
    | right i => simp [generatedAxisFourthQAffineParameterEncode, Fin.append_right]

/-- The seven freely chosen binary coordinates give the actual common Q stabilizer group. -/
def generatedFourthQAffineParameterGroupEquiv :
    generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters ≃*
        Multiplicative (Fin 7 → ZMod 2) := by
  let E := generatedAxisFourthQAffineFamilyMulEquiv generatedAxisFourthQAffineParameterPlane
    generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters 0
  let L := generatedAxisFourthQAffineParameterLinearEquiv.trans generatedFourthQParameterLinearEquiv
  exact
    { toFun := fun q => Multiplicative.ofAdd (L (Multiplicative.toAdd (E q)))
      invFun := fun w => E.symm (Multiplicative.ofAdd (L.symm (Multiplicative.toAdd w)))
      left_inv := by intro q; simp
      right_inv := by intro w; simp
      map_mul' := by
        intro q r
        apply Multiplicative.toAdd.injective
        change L (Multiplicative.toAdd (E (q * r))) =
          L (Multiplicative.toAdd (E q)) + L (Multiplicative.toAdd (E r))
        rw [E.map_mul]
        exact L.map_add _ _ }

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
