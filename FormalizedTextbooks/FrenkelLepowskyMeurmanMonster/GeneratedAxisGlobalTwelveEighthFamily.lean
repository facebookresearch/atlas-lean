/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthDecompose
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthOmegaBinding

/-! Triality coverage of the actual Eighth family by the twelve-family catalogue, reduced to
bindings of thirty-six of the thirty-seven forest roots.

The Ω root is bound unconditionally. Its inverse triality image is literally the local Odd
image `L8 v_odd` of the Odd representative, since the Eighth representative is
`sExtra (L8 v_odd)`. Its positive image is the inverse image of `L8 v_odd`, which lies in the
catalogue union by the actual binary root relation with Odd root one and the two actual Eighth
destinations of that root. Each remaining root is an explicit hypothesis: an explicit local
element in the same stabilizer binary orbit with both triality images in the union. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A binding of the Eighth forest root `j`: an explicit local element whose binary root lies
in the stabilizer orbit of the root mask, with both triality images in the catalogue union. -/
def GeneratedAxisGlobalTwelveEighthRootBound (j : Fin 37) : Prop :=
  ∃ h c : H, c ∈ generatedEighthLocalAxisStabilizer ∧
    co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val ∧
    sExtra (rhoLocal h generatedEighthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (rhoLocal h generatedEighthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative

private theorem sExtra_inv_eq_square'' (y : GriessSpace) : sExtra⁻¹ y = sExtra (sExtra y) := by
  apply sExtra.injective
  rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- The Ω root of the Eighth forest is bound by the identity element. -/
theorem generatedAxisGlobalTwelveEighthRootBound_zero :
    GeneratedAxisGlobalTwelveEighthRootBound 0 := by
  refine ⟨1, 1, Subgroup.one_mem _, ?_, ?_, ?_⟩
  · change co1BinaryAction (projH 1) (monsterCo1GeometryBinaryMaskDecode (n := 24) 2048) =
      co1BinaryAction (projH 1⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ))
    rw [inv_one, map_one, map_one, generatedAxisGlobalTwelveEighthOmega_mask]
  · rw [map_one, LinearEquiv.coe_one, id_eq]
    exact generatedAxisGlobalTwelveEighth_positive_mem
  · rw [map_one, LinearEquiv.coe_one, id_eq]
    exact generatedAxisGlobalTwelveEighth_inverse_mem

/-- A positive literal transport from a listed family into the Eighth class binds an Eighth
root: if `sExtra (w v_i) = m v8` and the other image of `w v_i` lies in the union, then `m` has
both triality images in the union. -/
theorem generatedAxisGlobalTwelveEighthRootBound_of_positive_transport (j : Fin 37) (i : Fin 12)
    (w m c : H) (hc : c ∈ generatedEighthLocalAxisStabilizer)
    (hroot : co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot m).val)
    (htr : sExtra (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal m generatedEighthAxis)
    (hother : sExtra⁻¹ (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveEighthRootBound j := by
  refine ⟨m, c, hc, hroot, ?_, ?_⟩
  · rw [← htr, ← sExtra_inv_eq_square'']
    exact hother
  · rw [← htr, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport i w rfl

/-- An inverse literal transport from a listed family into the Eighth class binds an Eighth
root: if `sExtra⁻¹ (w v_i) = m v8` and the other image of `w v_i` lies in the union, then `m`
has both triality images in the union. -/
theorem generatedAxisGlobalTwelveEighthRootBound_of_negative_transport (j : Fin 37) (i : Fin 12)
    (w m c : H) (hc : c ∈ generatedEighthLocalAxisStabilizer)
    (hroot : co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveEighthRootMask j)) =
        (generatedAxisGlobalBinaryRoot m).val)
    (htr : sExtra⁻¹ (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal m generatedEighthAxis)
    (hother : sExtra (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveEighthRootBound j := by
  refine ⟨m, c, hc, hroot, ?_, ?_⟩
  · rw [← htr, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport i w rfl
  · rw [← htr, sExtra_inv_eq_square'', sExtra_inv_eq_square'', sExtra_triple]
    exact hother

/-- Bindings of the thirty-six non-Ω forest roots give complete Eighth-family coverage. -/
theorem generatedAxisGlobalTwelve_eighth_covered_of
    (hb : ∀ j : Fin 37, j ≠ 0 → GeneratedAxisGlobalTwelveEighthRootBound j) :
    GeneratedAxisGlobalTwelveFamilyCovered 7 := by
  have hall (j : Fin 37) :
      sExtra (rhoLocal (generatedAxisGlobalTwelveEighthRootWord j) generatedEighthAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
        sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveEighthRootWord j) generatedEighthAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    have hj : GeneratedAxisGlobalTwelveEighthRootBound j := by
      by_cases h0 : j = 0
      · subst h0
        exact generatedAxisGlobalTwelveEighthRootBound_zero
      · exact hb j h0
    obtain ⟨h, c, hc, hroot, hpos, hneg⟩ := hj
    exact generatedAxisGlobalTwelveEighth_root_of_binding _ j h c hc hroot hpos hneg
  intro h
  exact generatedAxisGlobalTwelveEighth_triality_of_actual_destinations _
    (fun j => (hall j).1) (fun j => (hall j).2) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
