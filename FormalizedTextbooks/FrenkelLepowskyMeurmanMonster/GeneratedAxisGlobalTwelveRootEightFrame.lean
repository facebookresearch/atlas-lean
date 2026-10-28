/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentLetters
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightForestRoots
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceFiber
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionCo1FrameOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaClass

/-! Monomial words fix the binary Ω class.

Every letter of the identification alphabet other than the source Xi (an extraspecial element,
a source Golay sign lift, or a source permutation letter) projects into the stabilizer of the
binary Ω class in `Co1`. Hence so does every Xi-free word. This is the frame condition needed
to read off the binary root of a transporter of the form `monomial * root word`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- Every genuine Golay sign isometry fixes the binary Ω class. -/
theorem rootEightFrame_golaySign (d : golayCode) :
    QuotientGroup.mk' signsSubgroup (golaySignIsometry d) ∈ co1OmegaFrameStabilizer := by
  have hint : leechIntegralAction (golaySignIsometry d) (leechCoordinateFrameLattice 0) =
      leechCoordinateFrameLattice 0 ∨
      leechIntegralAction (golaySignIsometry d) (leechCoordinateFrameLattice 0) =
        -leechCoordinateFrameLattice 0 := by
    by_cases h0 : d.val 0 = 0
    · left
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      simp only [golayIntegerSign]
      split_ifs with hi
      · rfl
      · have hne : i ≠ 0 := fun h => hi (h ▸ h0)
        simp [leechCoordinateFrameLattice, leechCoordinateFrameVector, hne]
    · right
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      simp only [golayIntegerSign]
      split_ifs with hi
      · have hne : i ≠ 0 := fun h => h0 (h ▸ hi)
        simp [leechCoordinateFrameLattice, leechCoordinateFrameVector, hne]
      · rfl
  have hred : leechModTwoAction (golaySignIsometry d)
      (leechReduction (leechCoordinateFrameLattice 0)) =
      leechReduction (leechCoordinateFrameLattice 0) := by
    change leechQuotientAut (leechIntegralAction (golaySignIsometry d))
      (leechReduction (leechCoordinateFrameLattice 0)) = _
    rw [leechQuotientAut_reduce]
    rcases hint with h | h
    · rw [h]
    · rw [h, leechReduction_neg]
  change co1BinaryAction (QuotientGroup.mk' signsSubgroup (golaySignIsometry d))
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = Multiplicative.toAdd (qQuotHom sourceOmegaQ)
  rw [sourceOmegaQ_eq_frame_class]
  change leechBinaryAction (golaySignIsometry d)
    (leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0))) = _
  rw [leechBinaryAction_coordinates, hred]

set_option maxRecDepth 100000 in
-- Evaluate the eight Golay sign and permutation source letters on the Ω mask.
/-- The source sign and permutation letters fix the Ω mask. -/
theorem rootEightFrame_oddRows : ∀ l : Fin 10, 2 ≤ l.val →
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) 2048 = 2048 := by
  decide +kernel

/-- The source sign and permutation letters fix the binary Ω class. -/
theorem rootEightFrame_oddLetter (l : Fin 10) (hl : 2 ≤ l.val) :
    projH (generatedAxisGlobalOddSourceLocalLetter l) ∈ co1OmegaFrameStabilizer := by
  change co1BinaryAction (projH (generatedAxisGlobalOddSourceLocalLetter l))
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = Multiplicative.toAdd (qQuotHom sourceOmegaQ)
  rw [rootEightForest_omega_mask, generatedAxisGlobalOddSourceLocalLetter_binary,
    rootEightFrame_oddRows l hl]

/-- Every letter other than the source Xi fixes the binary Ω class. -/
theorem rootEightFrame_identLetter (l : IdentLetter) (hl : l ≠ IdentLetter.xi) :
    projH (identWordLocal [l]) ∈ co1OmegaFrameStabilizer := by
  rw [identWordLocal_singleton]
  cases l with
  | xi => exact absurd rfl hl
  | sign a ε =>
    change projH (localFiberIntoH (generatedFifthSignFiber a ε)) ∈ co1OmegaFrameStabilizer
    rw [generatedFifth_sign_fiber_local, generatedFifth_sign_local_projection]
    exact rootEightFrame_golaySign _
  | mono m =>
    obtain ⟨i, b⟩ := m
    fin_cases i <;> cases b
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 6)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact rootEightFrame_oddLetter 6 (by decide)
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 7)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact rootEightFrame_oddLetter 7 (by decide)
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 8)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact rootEightFrame_oddLetter 8 (by decide)
    · change projH (localFiberIntoH (generatedAxisGlobalOddSourceFiberLetter 9)) ∈
        co1OmegaFrameStabilizer
      rw [generatedAxisGlobalOddSourceFiberLetter_local]
      exact rootEightFrame_oddLetter 9 (by decide)
  | qel g =>
    change projH (inclQ g) ∈ co1OmegaFrameStabilizer
    rw [projH_inclQ]
    exact co1OmegaFrameStabilizer.one_mem

/-- Every Xi-free word fixes the binary Ω class. -/
theorem rootEightFrame_identWord (ls : List IdentLetter) (hls : ∀ l ∈ ls, l ≠ IdentLetter.xi) :
    projH (identWordLocal ls) ∈ co1OmegaFrameStabilizer := by
  induction ls with
  | nil =>
    have h1 : identWordLocal [] = 1 := by simp [identWordLocal, identWordFiber]
    rw [h1, map_one]
    exact co1OmegaFrameStabilizer.one_mem
  | cons l ls ih =>
    rw [show l :: ls = [l] ++ ls from rfl, identWordLocal_append, map_mul]
    exact co1OmegaFrameStabilizer.mul_mem (rootEightFrame_identLetter l (hls l (by simp)))
      (ih fun m hm => hls m (by simp [hm]))

/-- A frame-fixing left factor does not change the actual binary root. -/
theorem rootEightFrame_binaryRoot (n r : H) (hn : projH n ∈ co1OmegaFrameStabilizer) :
    generatedAxisGlobalBinaryRoot (n * r) = generatedAxisGlobalBinaryRoot r := by
  apply Subtype.ext
  change co1BinaryAction (projH (n * r)⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
    co1BinaryAction (projH r⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ))
  have hn' : co1BinaryAction (projH n⁻¹) (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) =
      Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
    have h1 := co1OmegaFrameStabilizer.inv_mem hn
    rw [← map_inv] at h1
    exact h1
  rw [mul_inv_rev, map_mul, map_mul, LinearEquiv.mul_apply, hn']

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
