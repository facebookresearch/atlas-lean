/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFirstFamily
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinaryCover

/-! Unconditional three-root coverage of the actual binary Ω orbit by the
actual first-axis stabilizer. This replaces the first published union-find
certificate with genuine monomial transitivity and exact local group maps. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every genuine binary Ω point is the inverse image of Ω by an actual local element. -/
theorem generatedAxisGlobalBinaryRoot_surjective :
    Function.Surjective generatedAxisGlobalBinaryRoot := by
  rintro ⟨x, g, hg⟩
  obtain ⟨h, hh⟩ := projH_surjective g⁻¹
  refine ⟨h, Subtype.ext ?_⟩
  change co1BinaryAction (projH h⁻¹) (toAdd (qQuotHom sourceOmegaQ)) = x
  rw [map_inv, hh, inv_inv]
  exact hg

/-- The actual first-axis stabilizer covers the entire genuine binary Ω
orbit from three genuine local roots, with no assumed orbit-size table. -/
theorem generatedAxisGlobalFirstFamily_binary_cover
    (x : generatedAxisGlobalBinaryOrbit) :
    ∃ i : Fin 3, ∃ c : localAxisStabilizer 0,
      generatedAxisGlobalBinaryAct c.val
        (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFirstInputLocal i)) = x := by
  obtain ⟨h, rfl⟩ := generatedAxisGlobalBinaryRoot_surjective x
  obtain ⟨i, n, c, he⟩ := generatedAxisGlobalFirstFamily_decompose h
  have hn : generatedAxisGlobalBinaryAct n.val⁻¹ generatedAxisGlobalBinaryOmega =
      generatedAxisGlobalBinaryOmega := by
    apply Subtype.ext
    change co1BinaryAction (projH n.val⁻¹) (toAdd (qQuotHom sourceOmegaQ)) = _
    exact localOmegaStabilizer_projection_mem n⁻¹
  refine ⟨i, c⁻¹, ?_⟩
  have hi : h⁻¹ = c.val⁻¹ * (generatedAxisGlobalFirstInputLocal i)⁻¹ * n.val⁻¹ := by
    rw [he]
    group
  simp only [generatedAxisGlobalBinaryRoot]
  rw [hi, generatedAxisGlobalBinaryAct_mul, generatedAxisGlobalBinaryAct_mul, hn]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
