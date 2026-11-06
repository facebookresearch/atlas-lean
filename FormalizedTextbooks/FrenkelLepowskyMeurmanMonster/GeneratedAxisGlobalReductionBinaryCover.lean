/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionSigns

/-! Transporting a verified binary stabilizer-orbit cover to actual local
transition decompositions. Roots are the actual inverse images of Ω under
the supplied local representatives, rather than arbitrary bit patterns. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual Ω point in its binary Conway orbit. -/
noncomputable def generatedAxisGlobalBinaryOmega : generatedAxisGlobalBinaryOrbit :=
  ⟨toAdd (qQuotHom sourceOmegaQ), 1, by
    change co1BinaryAction 1 _ = _
    rw [map_one]
    rfl⟩

/-- The binary root attached to a genuine local transition representative. -/
noncomputable def generatedAxisGlobalBinaryRoot (r : H) : generatedAxisGlobalBinaryOrbit :=
  generatedAxisGlobalBinaryAct r⁻¹ generatedAxisGlobalBinaryOmega

private theorem binaryActOne (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalBinaryAct 1 x = x := by
  apply Subtype.ext
  change co1BinaryAction (projH 1) x.val = x.val
  rw [map_one, map_one]
  rfl

/-- A genuine binary orbit cover produces the actual binary-normalizer
N_x0--C decomposition, including the correct inverse on the stabilizer factor. -/
theorem generatedAxisGlobal_decompose_of_binary_cover {κ : Type*}
    (C : Subgroup H) (r : κ → H)
    (hcover : ∀ x : generatedAxisGlobalBinaryOrbit, ∃ j c,
      c ∈ C ∧ generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot (r j)) = x)
    (h : H) :
    ∃ j n c, projH n ∈ co1OmegaFrameStabilizer ∧ c ∈ C ∧ h = n * r j * c := by
  obtain ⟨j, c, hc, he⟩ := hcover (generatedAxisGlobalBinaryRoot h)
  have ht := congrArg (generatedAxisGlobalBinaryAct h) he
  have hn : projH (h * c * (r j)⁻¹) ∈ co1OmegaFrameStabilizer := by
    have ht' : generatedAxisGlobalBinaryAct (h * c * (r j)⁻¹)
        generatedAxisGlobalBinaryOmega = generatedAxisGlobalBinaryOmega := by
      simpa only [generatedAxisGlobalBinaryRoot, ← generatedAxisGlobalBinaryAct_mul,
        mul_inv_cancel, binaryActOne, mul_assoc] using ht
    exact congrArg Subtype.val ht'
  refine ⟨j, h * c * (r j)⁻¹, c⁻¹, hn, C.inv_mem hc, ?_⟩
  group

/-- A binary descent forest with actual transition roots gives the two
full-Ω decompositions used by the source's τ and τ⁻¹ checks. -/
theorem generatedAxisGlobal_decompose_of_binary_descent {κ : Type*}
    (C : Subgroup H) (r : κ → H)
    (label : generatedAxisGlobalBinaryOrbit → κ)
    (rank : generatedAxisGlobalBinaryOrbit → ℕ)
    (hedge : ∀ x, x = generatedAxisGlobalBinaryRoot (r (label x)) ∨ ∃ y c,
      c ∈ C ∧ rank y < rank x ∧ label y = label x ∧
        generatedAxisGlobalBinaryAct c y = x)
    (h : H) :
    ∃ j n c, n ∈ localOmegaStabilizer ∧ c ∈ C ∧
      (h = n * r j * c ∨ h = n * (inclQ singletonCocodeQ * r j) * c) := by
  apply generatedAxisGlobal_decompose_two_signs C r
  · intro h'
    apply generatedAxisGlobal_decompose_of_binary_cover C r
    intro x
    obtain ⟨c, hc, he⟩ := generatedAxisGlobalBinary_cover_of_descent C
      (fun j => generatedAxisGlobalBinaryRoot (r j)) label rank hedge x
    exact ⟨label x, c, hc, he⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
