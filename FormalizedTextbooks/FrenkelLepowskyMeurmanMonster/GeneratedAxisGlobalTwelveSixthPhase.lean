/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthTransfer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortLetters
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionSigns

/-! The Q-phase of an identification prefix and exact-sign transfers.

Conjugation by the local element of an identification word acts on the extraspecial group; its
value on the Ω element is computed by folding canonical mask data of the letters (the odd source
letter caches, the exact source sign evaluator, and the extraspecial letters). If it fixes Ω, the
word lies in the actual local Ω stabilizer; if it sends Ω to `z Ω` and the word is Xi-free, the
word times the singleton cocode element lies there. A transport `sExtra^{±1} ((m · r) · v) ∈ U`
through such a prefix `m` therefore gives the triality image of `r · v` of the same sign in the
first case and of the opposite sign in the second. This makes the binding of both sides of an
identification exact at cells without phase merge. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Canonical mask data of a source sign, from its exact evaluator on the coordinate units. -/
def sixthPhaseSignData (a : Fin 4096) : QMaskData :=
  ⟨fun i => (qmEncode (generatedAxisGlobalSignFullImage a (qCoordinateGenerator i))).1,
    fun i => rowsOf (fun j =>
      (qmEncode (generatedAxisGlobalSignFullImage a (qCoordinateGenerator j))).1) i,
    maskOfBits (fun i =>
      (qmEncode (generatedAxisGlobalSignFullImage a (qCoordinateGenerator i))).2)⟩

/-- Canonical mask data of an identification letter. -/
def sixthPhaseData : IdentLetter → QMaskData
  | .xi => sourceLetterData 0
  | .mono l => sourceLetterData (monoLetterIndex l)
  | .sign a _ => sixthPhaseSignData a
  | .qel g => qLetterDataZ (qmEncode g).1

/-- Letters whose sign phase is the source one (`ε = 0`); all other letters qualify. -/
def SixthPhaseLetter : IdentLetter → Prop
  | .sign _ ε => ε = 0
  | _ => True

/-- The canonical data of a qualifying letter are valid for its conjugation action. -/
theorem sixthPhaseData_valid (l : IdentLetter) (hl : SixthPhaseLetter l) :
    (sixthPhaseData l).Valid (spinConjugation l.fiber.val.1) := by
  cases l with
  | xi => exact xiLetterData_valid
  | mono m => exact monoLetterData_valid m
  | sign a ε =>
    have hε : ε = 0 := hl
    subst hε
    refine QMaskData.valid_of_images _ _ (generatedAxisGlobalSignFull_QImage a) _ ?_ ?_
    · intro i
      simp only [sixthPhaseData, sixthPhaseSignData, testBit_maskOfBits]
    · intro i
      rfl
  | qel g => exact qLetterDataZ_valid g

/-- The conjugation action of a qualifying word on signed masks is the fold of its letter data. -/
theorem sixthPhase_word (ls : List IdentLetter) (hls : ∀ l ∈ ls, SixthPhaseLetter l)
    (p : ℕ × Bool) :
    spinConjugation (identWordFiber ls).val.1 (qmElt p) =
      qmElt (qmWord (ls.map sixthPhaseData) p) := by
  induction ls with
  | nil =>
    change spinConjugation 1 (qmElt p) = qmElt p
    rw [map_one]
    rfl
  | cons x ls ih =>
    change spinConjugation (x.fiber.val.1 * (identWordFiber ls).val.1) (qmElt p) = _
    rw [map_mul, MulAut.mul_apply, ih (fun l hl => hls l (List.mem_cons_of_mem _ hl)),
      (sixthPhaseData x).step_spec _ (sixthPhaseData_valid x (hls x (List.mem_cons_self ..)))]
    rfl

/-- The unsigned Ω mask is the source Ω element. -/
theorem sixthPhase_omega : qmElt (2048, false) = sourceOmegaQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    rw [qmElt_base]
    ext i
    have h : ∀ i : Fin 24, monsterCo1GeometryBinaryMaskDecode (n := 24) 2048 i =
        toAdd sourceOmegaQ.base i := by decide +kernel
    exact h i
  · apply toAdd.injective
    rw [qmElt_coeff]
    rfl

/-- A qualifying word whose data fix the Ω mask lies in the actual local Ω stabilizer. -/
theorem sixthPhase_mem (ls : List IdentLetter) (hls : ∀ l ∈ ls, SixthPhaseLetter l)
    (h : qmWord (ls.map sixthPhaseData) (2048, false) = (2048, false)) :
    identWordLocal ls ∈ localOmegaStabilizer := by
  unfold identWordLocal
  rw [localOmegaStabilizer_fiber_iff, ← sixthPhase_omega, sixthPhase_word ls hls, h]

/-- A qualifying Xi-free word whose data send the Ω mask to its negative lies in the actual local
Ω stabilizer after the singleton cocode element. -/
theorem sixthPhase_flip_mem (ls : List IdentLetter) (hls : ∀ l ∈ ls, SixthPhaseLetter l)
    (hxi : ∀ l ∈ ls, l ≠ IdentLetter.xi)
    (h : qmWord (ls.map sixthPhaseData) (2048, false) = (2048, true)) :
    identWordLocal ls * inclQ singletonCocodeQ ∈ localOmegaStabilizer := by
  rcases generatedAxisGlobal_binary_normalizer_split (identWordLocal ls)
      (sixthFrame_identWord ls hxi) with h0 | h1
  · exfalso
    unfold identWordLocal at h0
    rw [localOmegaStabilizer_fiber_iff, ← sixthPhase_omega, sixthPhase_word ls hls, h] at h0
    have hc := congrArg (fun q : Q => toAdd q.coeff) h0
    simp only [qmElt_coeff] at hc
    exact absurd hc (by decide)
  · exact h1

private theorem sixthPhase_singleton_square :
    inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
  rw [← map_mul]
  change inclQ (cocodeQ _ * cocodeQ _) = 1
  rw [cocodeQ_square, map_one]

/-- A local Ω stabilizer prefix keeps the positive triality image in a local orbit union. -/
theorem sixthPhase_forward_of_mem {ι : Type*} (u : ι → GriessSpace) (n r : H) (v : GriessSpace)
    (hn : n ∈ localOmegaStabilizer)
    (hmem : sExtra (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u := by
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨n, hn⟩ (rhoLocal r v)
  rw [map_mul, LinearEquiv.mul_apply, ← hk] at hmem
  exact generatedAxisGlobalTwelve_union_mem_of_local u k hmem rfl

/-- A local Ω stabilizer prefix keeps the inverse triality image in a local orbit union. -/
theorem sixthPhase_inverse_of_mem {ι : Type*} (u : ι → GriessSpace) (n r : H) (v : GriessSpace)
    (hn : n ∈ localOmegaStabilizer)
    (hmem : sExtra⁻¹ (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u) :
    sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelve_omega_inverse_orbit ⟨n, hn⟩ (rhoLocal r v)
  rw [map_mul, LinearEquiv.mul_apply, ← hk] at hmem
  exact generatedAxisGlobalTwelve_union_mem_of_local u k hmem rfl

/-- A flipped prefix exchanges the positive image for the inverse one. -/
theorem sixthPhase_forward_of_flip {ι : Type*} (u : ι → GriessSpace) (n r : H) (v : GriessSpace)
    (hn : n * inclQ singletonCocodeQ ∈ localOmegaStabilizer)
    (hmem : sExtra (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u) :
    sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u := by
  have he : n * r = (n * inclQ singletonCocodeQ) * (inclQ singletonCocodeQ * r) := by
    rw [mul_assoc, ← mul_assoc (inclQ singletonCocodeQ), sixthPhase_singleton_square, one_mul]
  rw [he] at hmem
  have h1 := sixthPhase_forward_of_mem u _ _ v hn hmem
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobal_singleton_triality_exchange] at h1
  exact generatedAxisGlobalTwelve_union_mem_of_local u _ h1 rfl

/-- A flipped prefix exchanges the inverse image for the positive one. -/
theorem sixthPhase_inverse_of_flip {ι : Type*} (u : ι → GriessSpace) (n r : H) (v : GriessSpace)
    (hn : n * inclQ singletonCocodeQ ∈ localOmegaStabilizer)
    (hmem : sExtra⁻¹ (rhoLocal (n * r) v) ∈ generatedLocalOrbitUnion u) :
    sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u := by
  have he : n * r = (n * inclQ singletonCocodeQ) * (inclQ singletonCocodeQ * r) := by
    rw [mul_assoc, ← mul_assoc (inclQ singletonCocodeQ), sixthPhase_singleton_square, one_mul]
  rw [he] at hmem
  have h1 := sixthPhase_inverse_of_mem u _ _ v hn hmem
  rw [map_mul, LinearEquiv.mul_apply, generatedAxisGlobalTwelve_singleton_inverse_exchange] at h1
  exact generatedAxisGlobalTwelve_union_mem_of_local u _ h1 rfl

/-- Exact transfer of a positive image through an Xi-free identification prefix `M`: the sign of
the image of `r · v` is read off from the computed Q-phase of `M`. -/
theorem sixthPhase_transfer_forward {ι : Type*} (u : ι → GriessSpace) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (r : H)
    (v : GriessSpace) (hmem : sExtra (rhoLocal (identWordLocal M * r) v) ∈
      generatedLocalOrbitUnion u) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :=
  ⟨fun h => sixthPhase_forward_of_mem u _ r v (sixthPhase_mem M hM h) hmem,
    fun h => sixthPhase_forward_of_flip u _ r v (sixthPhase_flip_mem M hM hxi h) hmem⟩

/-- Exact transfer of an inverse image through an Xi-free identification prefix `M`. -/
theorem sixthPhase_transfer_inverse {ι : Type*} (u : ι → GriessSpace) (M : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (r : H)
    (v : GriessSpace) (hmem : sExtra⁻¹ (rhoLocal (identWordLocal M * r) v) ∈
      generatedLocalOrbitUnion u) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra⁻¹ (rhoLocal r v) ∈ generatedLocalOrbitUnion u) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra (rhoLocal r v) ∈ generatedLocalOrbitUnion u) :=
  ⟨fun h => sixthPhase_inverse_of_mem u _ r v (sixthPhase_mem M hM h) hmem,
    fun h => sixthPhase_inverse_of_flip u _ r v (sixthPhase_flip_mem M hM hxi h) hmem⟩

/-- One identification binds the other side exactly: from `sExtra⁻¹ (h · v_k) = (M ++ T) · v`
with an Xi-free prefix `M`, the triality image of `T · v` of the sign given by the Q-phase of `M`
lies in the catalogue union. -/
theorem sixthPhase_of_inverse_identity (k : Fin 12) (h : H) (M T : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (v : GriessSpace)
    (he : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative k)) =
      rhoLocal (identWordLocal (M ++ T)) v) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra (rhoLocal (identWordLocal T) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra⁻¹ (rhoLocal (identWordLocal T) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  have hmem := sixthPartner_forward_mem k h _ v he
  rw [identWordLocal_append] at hmem
  exact sixthPhase_transfer_forward _ M hM hxi _ v hmem

/-- One identification binds the other side exactly: from `sExtra (h · v_k) = (M ++ T) · v`
with an Xi-free prefix `M`, the triality image of `T · v` of the sign given by the Q-phase of `M`
lies in the catalogue union. -/
theorem sixthPhase_of_forward_identity (k : Fin 12) (h : H) (M T : List IdentLetter)
    (hM : ∀ l ∈ M, SixthPhaseLetter l) (hxi : ∀ l ∈ M, l ≠ IdentLetter.xi) (v : GriessSpace)
    (he : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative k)) =
      rhoLocal (identWordLocal (M ++ T)) v) :
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, false) →
      sExtra⁻¹ (rhoLocal (identWordLocal T) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) ∧
    (qmWord (M.map sixthPhaseData) (2048, false) = (2048, true) →
      sExtra (rhoLocal (identWordLocal T) v) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  have hmem := sixthPartner_inverse_mem k h _ v he
  rw [identWordLocal_append] at hmem
  exact sixthPhase_transfer_inverse _ M hM hxi _ v hmem

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
