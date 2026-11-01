/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact cardinality of the common actual Q stabilizer via literal binary coordinates. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamily
public import Mathlib.FieldTheory.Finiteness
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

variable {J : Type*}

/-- Every admissible binary pair determines one actual common stabilizer element,
with central coefficient m·a_ref+b_ref·u. -/
noncomputable def generatedAxisFourthQAffineFamilyEquiv (S : Submodule (ZMod 2) SpinIndex)
    (a b : J → SpinIndex) (j₀ : J) :
    generatedAxisFourthQAffineFamilyStabilizer S a b ≃
      generatedAxisFourthQAffineFamilyKernel S a b j₀ where
  toFun q := ⟨(spinTranslation q.val, spinModulation q.val),
    ((generatedAxisFourthQAffineFamily_mem_iff S a b j₀ q.val).mp q.property).1⟩
  invFun p := ⟨generatedAxisFourthQFromSpin p.val.1 p.val.2
    (spinDot p.val.2 (a j₀) + spinDot (b j₀) p.val.1), by
      apply (generatedAxisFourthQAffineFamily_mem_iff S a b j₀ _).mpr
      constructor
      · simpa only [generatedAxisFourthQFromSpin_translation,
          generatedAxisFourthQFromSpin_modulation] using p.property
      · simp only [generatedAxisFourthQFromSpin_coeff,
          generatedAxisFourthQFromSpin_translation, generatedAxisFourthQFromSpin_modulation]⟩
  left_inv q := by
    apply Subtype.ext
    apply generatedAxisFourthQ_spin_coordinates_injective
    · exact generatedAxisFourthQFromSpin_translation _ _ _
    · exact generatedAxisFourthQFromSpin_modulation _ _ _
    · exact ((generatedAxisFourthQAffineFamily_mem_iff S a b j₀ q.val).mp q.property).2.symm
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact generatedAxisFourthQFromSpin_translation _ _ _
    · exact generatedAxisFourthQFromSpin_modulation _ _ _

/-- The actual common affine-state stabilizer has exactly the cardinality of its binary kernel. -/
theorem generatedAxisFourthQAffineFamily_card (S : Submodule (ZMod 2) SpinIndex)
    (a b : J → SpinIndex) (j₀ : J) :
    Nat.card (generatedAxisFourthQAffineFamilyStabilizer S a b) =
      Nat.card (generatedAxisFourthQAffineFamilyKernel S a b j₀) :=
  Nat.card_congr (generatedAxisFourthQAffineFamilyEquiv S a b j₀)

/-- The exact common stabilizer order is two to the binary dimension of its kernel,
with no assumption on that dimension or on a concrete state family. -/
theorem generatedAxisFourthQAffineFamily_card_pow (S : Submodule (ZMod 2) SpinIndex)
    (a b : J → SpinIndex) (j₀ : J) :
    Nat.card (generatedAxisFourthQAffineFamilyStabilizer S a b) =
      2 ^ Module.finrank (ZMod 2) (generatedAxisFourthQAffineFamilyKernel S a b j₀) := by
  rw [generatedAxisFourthQAffineFamily_card S a b j₀]
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using
    (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := generatedAxisFourthQAffineFamilyKernel S a b j₀))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
