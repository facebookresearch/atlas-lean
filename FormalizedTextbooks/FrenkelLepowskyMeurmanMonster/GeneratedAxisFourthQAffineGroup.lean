/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCard

/-! Common affine-state stabilizers are binary additive groups via literal spin coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal translation-modulation bijection also respects the actual Q group law. -/
def generatedAxisFourthQAffineFamilyMulEquiv {J : Type*}
    (S : Submodule (ZMod 2) SpinIndex) (a b : J → SpinIndex) (j₀ : J) :
    generatedAxisFourthQAffineFamilyStabilizer S a b ≃*
      Multiplicative (generatedAxisFourthQAffineFamilyKernel S a b j₀) where
  toFun q := Multiplicative.ofAdd (generatedAxisFourthQAffineFamilyEquiv S a b j₀ q)
  invFun p := (generatedAxisFourthQAffineFamilyEquiv S a b j₀).symm
    (Multiplicative.toAdd p)
  left_inv q := (generatedAxisFourthQAffineFamilyEquiv S a b j₀).symm_apply_apply q
  right_inv p := congrArg Multiplicative.ofAdd
    ((generatedAxisFourthQAffineFamilyEquiv S a b j₀).apply_symm_apply
      (Multiplicative.toAdd p))
  map_mul' q r := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (spinTranslation (q.val * r.val), spinModulation (q.val * r.val)) =
      (spinTranslation q.val + spinTranslation r.val, spinModulation q.val + spinModulation r.val)
    exact Prod.ext (spinTranslation_mul q.val r.val) (spinModulation_mul q.val r.val)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
