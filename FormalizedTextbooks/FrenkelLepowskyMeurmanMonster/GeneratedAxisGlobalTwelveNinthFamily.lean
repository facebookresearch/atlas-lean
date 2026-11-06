/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthDecompose
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthOmegaBinding

/-! Triality coverage of the actual Ninth family by the twelve-family catalogue, reduced to
bindings of seven of the eight forest roots.

The Ω root is bound unconditionally. Its inverse triality image is literally the local Fifth
image `L9 v5` of the Fifth representative, since the Ninth representative is `sExtra (L9 v5)`.
Its positive image is the inverse image of `L9 v5`, which lies in the catalogue union by the
actual binary root relation between `L9` and Fifth root five and the two actual Ninth
destinations of that root. Each remaining root is an explicit hypothesis: an explicit local
element in the same stabilizer binary orbit with both triality images in the union. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A binding of the Ninth forest root `j`: an explicit local element whose binary root lies
in the stabilizer orbit of the root mask, with both triality images in the catalogue union. -/
def GeneratedAxisGlobalTwelveNinthRootBound (j : Fin 8) : Prop :=
  ∃ h c : H, c ∈ generatedNinthLocalAxisStabilizer ∧
    co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j)) =
        (generatedAxisGlobalBinaryRoot h).val ∧
    sExtra (rhoLocal h generatedNinthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
    sExtra⁻¹ (rhoLocal h generatedNinthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative

/-- The Ω root of the Ninth forest is bound by the identity element. -/
theorem generatedAxisGlobalTwelveNinthRootBound_zero :
    GeneratedAxisGlobalTwelveNinthRootBound 0 := by
  refine ⟨1, 1, Subgroup.one_mem _, ?_, ?_, ?_⟩
  · change co1BinaryAction (projH 1) (monsterCo1GeometryBinaryMaskDecode (n := 24) 2048) =
      co1BinaryAction (projH 1⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ))
    rw [inv_one, map_one, map_one, generatedAxisGlobalTwelveNinthOmega_mask]
  · rw [map_one, LinearEquiv.coe_one, id_eq]
    exact generatedAxisGlobalTwelveNinth_positive_mem
  · rw [map_one, LinearEquiv.coe_one, id_eq]
    exact generatedAxisGlobalTwelveNinth_inverse_mem

/-- A positive literal transport from a listed family into the Ninth class binds a Ninth root:
if `sExtra (w v_i) = m v9` and the other image of `w v_i` lies in the union, then `m` has
both triality images in the union, and an actual whole-axis fixer matching root masks transfers
this to the forest root. -/
theorem generatedAxisGlobalTwelveNinthRootBound_of_positive_transport (j : Fin 8) (i : Fin 12)
    (w m c : H) (hc : c ∈ generatedNinthLocalAxisStabilizer)
    (hroot : co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j)) =
        (generatedAxisGlobalBinaryRoot m).val)
    (htr : sExtra (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal m generatedNinthAxis)
    (hother : sExtra⁻¹ (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveNinthRootBound j := by
  refine ⟨m, c, hc, hroot, ?_, ?_⟩
  · rw [← htr, ← generatedAxisGlobalTwelveNinth_sExtra_inv_eq_square]
    exact hother
  · rw [← htr, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport i w rfl

/-- An inverse literal transport from a listed family into the Ninth class binds a Ninth root:
if `sExtra⁻¹ (w v_i) = m v9` and the other image of `w v_i` lies in the union, then `m` has
both triality images in the union. -/
theorem generatedAxisGlobalTwelveNinthRootBound_of_negative_transport (j : Fin 8) (i : Fin 12)
    (w m c : H) (hc : c ∈ generatedNinthLocalAxisStabilizer)
    (hroot : co1BinaryAction (projH c)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalTwelveNinthRootMask j)) =
        (generatedAxisGlobalBinaryRoot m).val)
    (htr : sExtra⁻¹ (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal m generatedNinthAxis)
    (hother : sExtra (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveNinthRootBound j := by
  refine ⟨m, c, hc, hroot, ?_, ?_⟩
  · rw [← htr, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact generatedAxisGlobalTwelve_mem_of_transport i w rfl
  · rw [← htr, generatedAxisGlobalTwelveNinth_sExtra_inv_eq_square,
      generatedAxisGlobalTwelveNinth_sExtra_inv_eq_square, sExtra_triple]
    exact hother

/-- Bindings of the seven non-Ω forest roots give complete Ninth-family coverage. -/
theorem generatedAxisGlobalTwelve_ninth_covered_of
    (hb : ∀ j : Fin 8, j ≠ 0 → GeneratedAxisGlobalTwelveNinthRootBound j) :
    GeneratedAxisGlobalTwelveFamilyCovered 8 := by
  have hall (j : Fin 8) :
      sExtra (rhoLocal (generatedAxisGlobalTwelveNinthRootWord j) generatedNinthAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
        sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveNinthRootWord j) generatedNinthAxis) ∈
          generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
    have hj : GeneratedAxisGlobalTwelveNinthRootBound j := by
      by_cases h0 : j = 0
      · subst h0
        exact generatedAxisGlobalTwelveNinthRootBound_zero
      · exact hb j h0
    obtain ⟨h, c, hc, hroot, hpos, hneg⟩ := hj
    exact generatedAxisGlobalTwelveNinth_root_of_binding _ j h c hc hroot hpos hneg
  intro h
  exact generatedAxisGlobalTwelveNinth_triality_of_actual_destinations _
    (fun j => (hall j).1) (fun j => (hall j).2) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
