/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleIndependentShortPhase

/-! Complete signed-short transport inside the actual simultaneous local
first-axis/Omega stabilizer. The hypotheses concern genuine monomial label maps. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both signed axes on an independent short base lie in one actual simultaneous orbit. -/
theorem generatedFeasible_independent_short_signed (p : Fin 276) (r : GriessShortIndex)
    (hfirst : (griessShortQ r).base ≠ (griessShortQ (Sum.inl (0, p))).base)
    (hsum : Multiplicative.toAdd (griessShortQ r).base ≠
      Multiplicative.toAdd sourceOmegaQ.base +
        Multiplicative.toAdd (griessShortQ (Sum.inl (0, p))).base)
    (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer p ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) = conwayShortAxis r d := by
  obtain ⟨q, hq, hphase⟩ := generatedFeasible_independent_short_phase p r hfirst hsum (d - c)
  refine ⟨⟨inclQ q, hq⟩, ?_⟩
  change localGriessRepresentation (localFiberIncl q) (conwayShortAxis r c) = _
  rw [generatedAxis_localFiber_image, hphase, sub_add_cancel]
  have hl : griessShortPermutation (localFiberIncl q).val.2 r = r := by
    change griessShortPermutation 1 r = r
    rw [map_one]
    rfl
  rw [hl]

/-- A genuine monomial label transport fixing the first label lifts to any
requested signed-short transport while fixing both the first axis and Omega. -/
theorem generatedFeasible_monomial_independent_signed (p : Fin 276)
    (r s : GriessShortIndex) (e : leechIsomSubgroup) (he : e ∈ golayMonomialSubgroup)
    (hp : griessShortPermutation e (Sum.inl (0, p)) = Sum.inl (0, p))
    (hrs : griessShortPermutation e r = s)
    (hfirst : (griessShortQ s).base ≠ (griessShortQ (Sum.inl (0, p))).base)
    (hsum : Multiplicative.toAdd (griessShortQ s).base ≠
      Multiplicative.toAdd sourceOmegaQ.base +
        Multiplicative.toAdd (griessShortQ (Sum.inl (0, p))).base)
    (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer p ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) = conwayShortAxis s d := by
  let a : co1OmegaFrameStabilizer :=
    ⟨QuotientGroup.mk e, generatedAxis_monomial_fixes_omega e he⟩
  obtain ⟨h, hh⟩ := localOmegaProjection_surjective a
  have hproj : projH h.val = QuotientGroup.mk e := congrArg Subtype.val hh
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfc : projH (localFiberIntoH f) = QuotientGroup.mk e :=
    (congrArg projH hf).trans hproj
  have hl (t : GriessShortIndex) :
      griessShortPermutation f.val.2 t = griessShortPermutation e t := by
    have hco : co1ShortPermutation (projH (localFiberIntoH f)) =
        griessShortPermutation f.val.2 := co1ShortPermutation_mk f.val.2
    rw [← hco, hfc, co1ShortPermutation_mk]
  have hlf := (hl (Sum.inl (0, p))).trans hp
  obtain ⟨q, hqΩ, hphase⟩ := generatedAxis_short_localOmega_phase
    (Sum.inl (0, p)) (localShortPhase f (Sum.inl (0, p)))
  let f' : localFiberSubgroup := localFiberIncl q * f
  have hfp : griessShortPermutation f'.val.2 (Sum.inl (0, p)) = Sum.inl (0, p) := by
    change griessShortPermutation (1 * f.val.2) (Sum.inl (0, p)) = _
    simpa only [one_mul] using hlf
  have hfr : griessShortPermutation f'.val.2 r = s := by
    change griessShortPermutation (1 * f.val.2) r = s
    simpa only [one_mul] using (hl r).trans hrs
  have hzero : localShortPhase f' (Sum.inl (0, p)) = 0 := by
    change localShortPhase (localFiberIncl q * f) _ = 0
    rw [localShortPhase_mul, hlf, hphase]
    exact CharTwo.add_self_eq_zero _
  have hfirstmem : localFiberIntoH f' ∈ localAxisStabilizer p := by
    rw [localAxisStabilizer_mk_iff]
    exact ⟨hfp, hzero⟩
  have hΩmem : localFiberIntoH f' ∈ localOmegaStabilizer := by
    change inclQ q * localFiberIntoH f ∈ localOmegaStabilizer
    rw [hf]
    exact localOmegaStabilizer.mul_mem hqΩ h.property
  let h' : ↥(localAxisStabilizer p ⊓ localOmegaStabilizer) :=
    ⟨localFiberIntoH f', hfirstmem, hΩmem⟩
  have himage : rhoLocal h'.val (conwayShortAxis r c) =
      conwayShortAxis s (localShortPhase f' r + c) := by
    change localGriessRepresentation f' _ = _
    rw [generatedAxis_localFiber_image, hfr]
  obtain ⟨k, hk⟩ := generatedFeasible_independent_short_signed p s hfirst hsum
    (localShortPhase f' r + c) d
  refine ⟨k * h', ?_⟩
  change rhoLocal (k.val * h'.val) (conwayShortAxis r c) = _
  rw [rhoLocal.map_mul, LinearEquiv.mul_apply, himage]
  exact hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
