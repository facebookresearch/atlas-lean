/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRootWord
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryCover
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthForestCover

/-! The fourteen genuine binary roots are the roots of explicit original local words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual Ω root of each explicit original local word is its checked norm-eight root. -/
theorem generatedAxisGlobalFifthRootLocalWord_root (k : Fin 14) :
    generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthRootLocalWord k) =
      generatedAxisGlobalFifthRoot k := by
  apply Subtype.ext
  change co1BinaryAction (projH (generatedAxisGlobalFifthRootLocalWord k)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = generatedAxisGlobalFifthRootBinary k
  rw [map_inv, ← generatedAxisGlobalFifthRootLocalWord_binary k,
    ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl


/-- Checked finite descent edges give coverage using the explicit original local word roots. -/
theorem generatedAxisGlobalFifthRootLocalWord_cover_of_forest
    (hedges : ∀ b : Fin (2 ^ 24), ∃ e : ℕ, generatedAxisGlobalFifthForestStep e b.val) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 14, ∃ c : H,
      c ∈ generatedFifthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c
          (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthRootLocalWord i)) = x := by
  intro x
  obtain ⟨i, c, hc, he⟩ := generatedAxisGlobalFifthBinary_cover_of_forest hedges x
  exact ⟨i, c, hc, by rw [generatedAxisGlobalFifthRootLocalWord_root]; exact he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
