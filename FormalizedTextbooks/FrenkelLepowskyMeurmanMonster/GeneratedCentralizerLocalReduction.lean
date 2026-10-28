/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Remove the recognized actual Leech action, leaving only diagonal short signs. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalLift

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A signed physical short image identifies its unique actual local short label. -/
theorem generatedCentral_signed_short_label (e : leechIsomSubgroup)
    (r s : GriessShortIndex)
    (hs : e.val (griessShortVector r) = griessShortVector s ∨
      e.val (griessShortVector r) = -griessShortVector s) :
    s = griessShortPermutation e r := by
  rcases hs with hs | hs <;> rcases griessShortPermutation_vector e r with hp | hp
  · exact centralizer_shortVector_line_unique s _ 1 (by simpa using hs.symm.trans hp)
  · exact centralizer_shortVector_line_unique s _ (-1) (by simpa using hs.symm.trans hp)
  · exact centralizer_shortVector_line_unique s _ (-1)
      (by simpa using congrArg Neg.neg (hs.symm.trans hp))
  · exact centralizer_shortVector_line_unique s _ 1
      (by simpa using congrArg Neg.neg (hs.symm.trans hp))

/-- The actual local short representation sends each basis unit to its signed permuted unit. -/
theorem generatedLocal_short_unit (f : localFiberSubgroup) (r : GriessShortIndex) :
    localShortRepresentation f (shortCoordinateUnit r) =
      qSign (localShortPhase f r) • shortCoordinateUnit (griessShortPermutation f.val.2 r) := by
  funext i
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective i
  change localShortOperator f (shortCoordinateUnit r) (griessShortPermutation f.val.2 s) = _
  rw [localShortOperator_image]
  by_cases h : s = r
  · subst s
    simp [shortCoordinateUnit]
  · have hp : griessShortPermutation f.val.2 s ≠ griessShortPermutation f.val.2 r :=
      (griessShortPermutation f.val.2).injective.ne h
    simp [shortCoordinateUnit, h, hp]

/-- Embedding pure short coordinates commutes with real scalar multiplication. -/
theorem generatedCentral_short_embed_smul (c : ℝ) (X : GriessShortIndex → ℝ) :
    (generatedCentralPlusEmbed 0 (c • X)).val = c • (generatedCentralPlusEmbed 0 X).val := by
  exact congrArg (fun x : generatedCentralShort => x.val.val)
    (generatedCentralShortCoordinates.symm.map_smul c X)

/-- A real sign on a short basis unit is the constructed binary central character. -/
theorem generatedCentral_short_unit_binary_sign (X : GriessShortIndex → ℝ)
    (r : GriessShortIndex) (h : X = shortCoordinateUnit r ∨ X = -shortCoordinateUnit r) :
    ∃ c : ZMod 2, X = qSign c • shortCoordinateUnit r := by
  rcases h with h | h
  · exact ⟨0, by simpa only [qSign_zero, one_smul] using h⟩
  · exact ⟨1, by simpa only [qSign_one, neg_one_smul] using h⟩

/-- Removing a genuine local lift leaves only a matrix-fixing action with diagonal short signs. -/
theorem generatedCentralizer_reduce_to_short_signs (g : generatedCentralizer) :
    ∃ h : H,
      (∀ A : Sym24, ((generatedLocalIntoCentralizer h)⁻¹ * g).val.val
        (generatedCentralPlusEmbed A 0).val = (generatedCentralPlusEmbed A 0).val) ∧
      (∀ r : GriessShortIndex, ∃ c : ZMod 2,
        generatedCentralizerShortAction ((generatedLocalIntoCentralizer h)⁻¹ * g)
          (shortCoordinateUnit r) = qSign c • shortCoordinateUnit r) := by
  obtain ⟨R, hTR, hRT, hR, ⟨p, hp⟩, he⟩ := generatedCentralizer_short_spatial_recognition g
  let e : leechIsomSubgroup := ⟨shortCoordinateOrthogonalEquiv R hTR hRT, he⟩
  obtain ⟨f, hf⟩ := generatedCentral_localFiber_lift e
  let h : H := QuotientGroup.mk f
  let l := generatedLocalIntoCentralizer h
  have hm (A : Sym24) : generatedCentralizerMatrixAction l A =
      generatedCentralizerMatrixAction g A := by
    apply Subtype.ext
    change (generatedCentralizerMatrixAction
      (generatedLocalIntoCentralizer (QuotientGroup.mk f)) A).val = _
    rw [generatedLocal_matrix_action, hf, conwayMatrixAction_eq_conjugate]
    rw [generatedCentral_orthogonal_equiv_matrix R hTR hRT he]
    exact (hR A).symm
  have hgm (A : Sym24) : g.val.val (generatedCentralPlusEmbed A 0).val =
      l.val.val (generatedCentralPlusEmbed A 0).val := by
    rw [generatedCentralizerMatrixAction_embed, generatedCentralizerMatrixAction_embed, hm]
  have hperm (r : GriessShortIndex) : p r = griessShortPermutation f.val.2 r := by
    rw [hf]
    apply generatedCentral_signed_short_label e r (p r)
    exact (hp r).2
  refine ⟨h, ?_, ?_⟩
  · intro A
    change l.val.val.symm (g.val.val (generatedCentralPlusEmbed A 0).val) = _
    rw [hgm, LinearEquiv.symm_apply_apply]
  · intro r
    obtain ⟨c, hc⟩ := generatedCentral_short_unit_binary_sign
      (generatedCentralizerShortAction g (shortCoordinateUnit r)) (p r) (hp r).1
    let d := localShortPhase f r
    have hl : generatedCentralizerShortAction l (shortCoordinateUnit r) =
        qSign d • shortCoordinateUnit (p r) := by
      change generatedCentralizerShortAction
        (generatedLocalIntoCentralizer (QuotientGroup.mk f)) (shortCoordinateUnit r) = _
      rw [generatedLocal_short_action, generatedLocal_short_unit, ← hperm]
    have hg : g.val.val (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val =
        qSign c • (generatedCentralPlusEmbed 0 (shortCoordinateUnit (p r))).val := by
      rw [generatedCentralizerShortAction_embed, hc, generatedCentral_short_embed_smul]
    have hla : l.val.val (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val =
        qSign d • (generatedCentralPlusEmbed 0 (shortCoordinateUnit (p r))).val := by
      rw [generatedCentralizerShortAction_embed, hl, generatedCentral_short_embed_smul]
    have hli : l.val.val.symm (generatedCentralPlusEmbed 0 (shortCoordinateUnit (p r))).val =
        qSign d • (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val := by
      apply l.val.val.injective
      rw [LinearEquiv.apply_symm_apply, map_smul, hla, smul_smul, qSign_sq, one_smul]
    have hr : (l⁻¹ * g).val.val (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val =
        qSign (c + d) • (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val := by
      change l.val.val.symm
        (g.val.val (generatedCentralPlusEmbed 0 (shortCoordinateUnit r)).val) = _
      rw [hg, map_smul, hli, smul_smul, qSign_add]
    refine ⟨c + d, ?_⟩
    have hb := (generatedCentralizerShortAction_embed (l⁻¹ * g) (shortCoordinateUnit r)).symm.trans
      (hr.trans (generatedCentral_short_embed_smul (qSign (c + d)) (shortCoordinateUnit r)).symm)
    have hcoord := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.1) hb
    rw [generatedCentralPlusEmbed_encode, generatedCentralPlusEmbed_encode] at hcoord
    exact hcoord

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
