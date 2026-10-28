/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSixthPhase
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPhaseRoots

/-! Triangle bindings for the open Fifth vectors.

Triality has order three, so the two triality images of a Fifth coset vector `x` and `x` itself
form a triangle `{x, sExtra x, sExtra⁻¹ x}`. This module turns one identification per triangle
into both images wherever the triangle allows it:

* a *self* identification `sExtra^{±1} (L · v₅) = (M ++ L) · v₅` whose Xi-free prefix `M` has
  computed Q-phase fixing Ω binds both images at `L · v₅` (`sixthPhase_of_forward_identity`);
* a forward identification into a family whose coverage is known binds the inverse image too,
  since `sExtra⁻¹ x = sExtra (sExtra x)`;
* a merged Fifth root is bound by either image at any coset in its C₅ orbit, in particular by
  partner identifications whose Fifth side is a frame-fixing prefix times a Fifth coset word.

The concrete phase-fixing prefixes of the numerically found Fifth self identifications (roots 1
and 6) and the binary data of the Seventh partner coset of root 3 are certified here. No
identification is asserted: all identification statements are hypotheses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-! ## Phase-fixing prefixes -/

/-- Admissible prefix letters: no Xi, and source signs of phase zero. -/
def generatedAxisGlobalTwelveFifthBindPrefixLetter : IdentLetter → Bool
  | .xi => false
  | .sign _ ε => decide (ε = 0)
  | _ => true

/-- An admissible prefix whose computed Q-phase fixes the Ω mask. -/
def GeneratedAxisGlobalTwelveFifthBindFixPrefix (M : List IdentLetter) : Prop :=
  M.all generatedAxisGlobalTwelveFifthBindPrefixLetter = true ∧
    qmWord (M.map sixthPhaseData) (2048, false) = (2048, false)

theorem generatedAxisGlobalTwelveFifthBindPrefix_letters {M : List IdentLetter}
    (h : M.all generatedAxisGlobalTwelveFifthBindPrefixLetter = true) :
    (∀ l ∈ M, SixthPhaseLetter l) ∧ ∀ l ∈ M, l ≠ IdentLetter.xi := by
  rw [List.all_eq_true] at h
  constructor
  · intro l hl
    have hl' := h l hl
    cases l with
    | xi => exact True.intro
    | sign a ε =>
      change ε = 0
      simpa [generatedAxisGlobalTwelveFifthBindPrefixLetter] using hl'
    | mono m => exact True.intro
    | qel g => exact True.intro
  · intro l hl he
    subst he
    have hl' := h _ hl
    simp [generatedAxisGlobalTwelveFifthBindPrefixLetter] at hl'

/-! ## Self identifications -/

/-- A forward Fifth self identification `sExtra (L · v₅) = (M ++ L) · v₅`. -/
def GeneratedAxisGlobalTwelveFifthBindSelfForward (L M : List IdentLetter) : Prop :=
  sExtra (rhoLocal (identWordLocal L) (generatedAxisGlobalTwelveRepresentative 4)) =
    rhoLocal (identWordLocal (M ++ L)) (generatedAxisGlobalTwelveRepresentative 4)

/-- An inverse Fifth self identification `sExtra⁻¹ (L · v₅) = (M ++ L) · v₅`. -/
def GeneratedAxisGlobalTwelveFifthBindSelfInverse (L M : List IdentLetter) : Prop :=
  sExtra⁻¹ (rhoLocal (identWordLocal L) (generatedAxisGlobalTwelveRepresentative 4)) =
    rhoLocal (identWordLocal (M ++ L)) (generatedAxisGlobalTwelveRepresentative 4)

/-- A forward self identification through a phase-fixing prefix binds both images. -/
theorem generatedAxisGlobalTwelveFifthBind_pair_of_selfForward {L M : List IdentLetter}
    (hM : GeneratedAxisGlobalTwelveFifthBindFixPrefix M)
    (he : GeneratedAxisGlobalTwelveFifthBindSelfForward L M) :
    sExtra (rhoLocal (identWordLocal L) (generatedAxisGlobalTwelveRepresentative 4)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (identWordLocal L) (generatedAxisGlobalTwelveRepresentative 4)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, hx⟩ := generatedAxisGlobalTwelveFifthBindPrefix_letters hM.1
  exact ⟨generatedAxisGlobalTwelve_mem_of_transport 4 _ he,
    (sixthPhase_of_forward_identity 4 _ M L hl hx _ he).1 hM.2⟩

/-- An inverse self identification through a phase-fixing prefix binds both images. -/
theorem generatedAxisGlobalTwelveFifthBind_pair_of_selfInverse {L M : List IdentLetter}
    (hM : GeneratedAxisGlobalTwelveFifthBindFixPrefix M)
    (he : GeneratedAxisGlobalTwelveFifthBindSelfInverse L M) :
    sExtra (rhoLocal (identWordLocal L) (generatedAxisGlobalTwelveRepresentative 4)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (identWordLocal L) (generatedAxisGlobalTwelveRepresentative 4)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hl, hx⟩ := generatedAxisGlobalTwelveFifthBindPrefix_letters hM.1
  exact ⟨(sixthPhase_of_inverse_identity 4 _ M L hl hx _ he).1 hM.2,
    generatedAxisGlobalTwelve_mem_of_transport 4 _ he⟩

/-! ## Forward identifications into covered families -/

private theorem fifthBind_inv_eq (x : GriessSpace) : sExtra⁻¹ x = sExtra (sExtra x) := by
  rw [LinearEquiv.coe_inv]
  apply sExtra.injective
  rw [LinearEquiv.apply_symm_apply, sExtra_triple]

/-- A forward identification into a family whose coverage is known binds both images. -/
theorem generatedAxisGlobalTwelveFifthBind_pair_of_forward_covered (x : GriessSpace) (k : Fin 12)
    (hk : GeneratedAxisGlobalTwelveFamilyCovered k)
    (he : ∃ g : H, sExtra x = rhoLocal g (generatedAxisGlobalTwelveRepresentative k)) :
    sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := he
  refine ⟨generatedAxisGlobalTwelve_mem_of_transport k g hg, ?_⟩
  rw [fifthBind_inv_eq, hg]
  exact hk g

/-- Two identifications bind both images. -/
theorem generatedAxisGlobalTwelveFifthBind_pair_of_identities (x : GriessSpace) (j k : Fin 12)
    (hp : ∃ g : H, sExtra x = rhoLocal g (generatedAxisGlobalTwelveRepresentative j))
    (hn : ∃ g : H, sExtra⁻¹ x = rhoLocal g (generatedAxisGlobalTwelveRepresentative k)) :
    sExtra x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ x ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨g, hg⟩ := hp
  obtain ⟨g', hg'⟩ := hn
  exact ⟨generatedAxisGlobalTwelve_mem_of_transport j g hg,
    generatedAxisGlobalTwelve_mem_of_transport k g' hg'⟩

/-! ## Merged roots -/

/-- At a merged root, the inverse image gives the forward image. -/
theorem generatedAxisGlobalTwelveFifthBind_merged_of_inverse (j : Fin 7)
    (h : sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord
      (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord
      (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨m, hm⟩ := generatedAxisGlobalFifthMergedRoot_orbit j
  rw [hm]
  exact generatedLocalOrbitUnion_local _ m h

/-- A merged root is bound by either image at any coset in its C₅ orbit. -/
theorem generatedAxisGlobalTwelveFifthBind_merged_of_orbit (j : Fin 7) (g c : H)
    (hc : rhoLocal c generatedFifthAxis = generatedFifthAxis)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot
      (generatedAxisGlobalFifthShortLocalWord (generatedAxisGlobalFifthMergedRoot j))) =
      generatedAxisGlobalBinaryRoot g)
    (hmem : sExtra (rhoLocal g generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal g generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord
      (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rcases generatedAxisGlobalTwelve_root_relation_pair generatedFifthAxis g _ c hc hroot with
    ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ | ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  · rcases hmem with h | h
    · exact generatedAxisGlobalTwelve_union_mem_of_local _ k h hk
    · exact generatedAxisGlobalTwelveFifthBind_merged_of_inverse j
        (generatedAxisGlobalTwelve_union_mem_of_local _ k' h hk')
  · rcases hmem with h | h
    · exact generatedAxisGlobalTwelveFifthBind_merged_of_inverse j
        (generatedAxisGlobalTwelve_union_mem_of_local _ k h hk)
    · exact generatedAxisGlobalTwelve_union_mem_of_local _ k' h hk'

/-- A merged root is bound by either image at a frame-fixing prefix times a coset word in its
C₅ orbit. -/
theorem generatedAxisGlobalTwelveFifthBind_merged_of_prefixed (j : Fin 7) (pre T : List IdentLetter)
    (c : H) (hpre : ∀ l ∈ pre, l ≠ IdentLetter.xi)
    (hc : rhoLocal c generatedFifthAxis = generatedFifthAxis)
    (hroot : generatedAxisGlobalBinaryAct c (generatedAxisGlobalBinaryRoot
      (generatedAxisGlobalFifthShortLocalWord (generatedAxisGlobalFifthMergedRoot j))) =
      generatedAxisGlobalBinaryRoot (identWordLocal T))
    (hmem : sExtra (rhoLocal (identWordLocal (pre ++ T)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∨
      sExtra⁻¹ (rhoLocal (identWordLocal (pre ++ T)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord
      (generatedAxisGlobalFifthMergedRoot j)) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply generatedAxisGlobalTwelveFifthBind_merged_of_orbit j (identWordLocal (pre ++ T)) c hc _ hmem
  rw [identWordLocal_append, sixthFrame_binaryRoot _ _ (sixthFrame_identWord pre hpre)]
  exact hroot

private theorem fifthBind_rho_one : rhoLocal (1 : H) generatedFifthAxis = generatedFifthAxis := by
  rw [map_one, LinearEquiv.coe_one, id_eq]

private theorem fifthBind_binaryAct_one (x : generatedAxisGlobalBinaryOrbit) :
    generatedAxisGlobalBinaryAct 1 x = x := by
  apply Subtype.ext
  change co1BinaryAction (projH 1) x.val = x.val
  rw [map_one, map_one]
  rfl

/-- Merged root 4 from an inverse partner identification landing on a frame-fixing prefix times
the Fifth root word 4 (the shape of gninth's Ninth root 7 transport). -/
theorem generatedAxisGlobalTwelveFifthBind_root4_of_inverse_ident (i : Fin 12) (w : H)
    (pre : List IdentLetter) (hpre : ∀ l ∈ pre, l ≠ IdentLetter.xi)
    (he : sExtra⁻¹ (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal (identWordLocal (pre ++ generatedAxisGlobalTwelveFifthBindRootLetters 4))
        (generatedAxisGlobalTwelveRepresentative 4)) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 4) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelveFifthBind_merged_of_prefixed 2 pre
    (generatedAxisGlobalTwelveFifthBindRootLetters 4) 1 hpre fifthBind_rho_one ?_
    (Or.inl (sixthPartner_forward_mem i w _ _ he))
  rw [← generatedAxisGlobalTwelveFifthBindRoot_eq_word]
  exact fifthBind_binaryAct_one _

/-- Merged root 4 from a forward partner identification of the same shape. -/
theorem generatedAxisGlobalTwelveFifthBind_root4_of_forward_ident (i : Fin 12) (w : H)
    (pre : List IdentLetter) (hpre : ∀ l ∈ pre, l ≠ IdentLetter.xi)
    (he : sExtra (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal (identWordLocal (pre ++ generatedAxisGlobalTwelveFifthBindRootLetters 4))
        (generatedAxisGlobalTwelveRepresentative 4)) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 4) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  refine generatedAxisGlobalTwelveFifthBind_merged_of_prefixed 2 pre
    (generatedAxisGlobalTwelveFifthBindRootLetters 4) 1 hpre fifthBind_rho_one ?_
    (Or.inr (sixthPartner_inverse_mem i w _ _ he))
  rw [← generatedAxisGlobalTwelveFifthBindRoot_eq_word]
  exact fifthBind_binaryAct_one _

/-! ## Root 3 through the two-xi Seventh partner coset -/

/-- The two-xi Fifth coset word of the Seventh partner transport (`F5r3b`, root 3 orbit). -/
def generatedAxisGlobalTwelveFifthBindRoot3Letters : List IdentLetter :=
  [.xi, .xi, .mono (0, true), .xi, .xi, .mono (1, true)]

private theorem fifthBind_xiBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction co1XiIsometry v = omegaOrbitBinaryMatrices 0 *ᵥ v :=
  omegaOrbitIsometry_binary 0 v

private theorem fifthBind_permutationZeroBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 0) v = omegaOrbitBinaryMatrices 3 *ᵥ v :=
  omegaOrbitIsometry_binary 3 v

private theorem fifthBind_permutationOneBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 1) v = omegaOrbitBinaryMatrices 4 *ᵥ v :=
  omegaOrbitIsometry_binary 4 v

private theorem fifthBind_xi_inv : co1XiIsometry⁻¹ = co1XiIsometry * co1XiIsometry := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, ← pow_three']
  exact co1XiIsometry_cube

private theorem fifthBind_binaryRoot_val (f : localFiberSubgroup) :
    (generatedAxisGlobalBinaryRoot (localFiberIntoH f)).val =
      leechBinaryAction f⁻¹.val.2 (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) := by
  change co1BinaryAction (projH (localFiberIntoH f)⁻¹)
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← map_inv]
  rfl

set_option maxHeartbeats 20000000 in
-- Ten binary matrix-vector products on one complete binary point.
/-- The exact binary root of the Seventh partner coset word. -/
theorem generatedAxisGlobalTwelveFifthBindRoot3Letters_root :
    (generatedAxisGlobalBinaryRoot
      (identWordLocal generatedAxisGlobalTwelveFifthBindRoot3Letters)).val =
      monsterCo1GeometryBinaryMaskDecode 7392240 := by
  unfold identWordLocal
  rw [fifthBind_binaryRoot_val]
  have hs : (identWordFiber generatedAxisGlobalTwelveFifthBindRoot3Letters)⁻¹.val.2 =
      omegaOrbitPermutationIsometry 1 * (co1XiIsometry * co1XiIsometry) *
        (co1XiIsometry * co1XiIsometry) * omegaOrbitPermutationIsometry 0 *
        (co1XiIsometry * co1XiIsometry) * (co1XiIsometry * co1XiIsometry) := by
    have h : (identWordFiber generatedAxisGlobalTwelveFifthBindRoot3Letters)⁻¹.val.2 =
        (co1XiIsometry * (co1XiIsometry * ((omegaOrbitPermutationIsometry 0)⁻¹ *
          (co1XiIsometry * (co1XiIsometry * ((omegaOrbitPermutationIsometry 1)⁻¹ * 1))))))⁻¹ :=
      rfl
    rw [h]
    simp only [mul_one, mul_inv_rev, inv_inv, fifthBind_xi_inv, mul_assoc]
  rw [hs]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [fifthBind_xiBinary, fifthBind_permutationZeroBinary, fifthBind_permutationOneBinary]
  decide +kernel

/-- An explicit product of genuine Fifth-axis fixers carrying root 3 to the partner coset. -/
def generatedAxisGlobalTwelveFifthBindRoot3Transport : generatedFifthLocalAxisStabilizer :=
  generatedAxisGlobalFifthGenerator 12 * generatedAxisGlobalFifthGenerator 18 *
    generatedAxisGlobalFifthGenerator 16 * generatedAxisGlobalFifthGenerator 17 *
    generatedAxisGlobalFifthGenerator 4 * generatedAxisGlobalFifthGenerator 16

set_option maxHeartbeats 20000000 in
-- Six actual generator binary matrices on one complete binary point.
/-- The transport carries the binary root of the Fifth root word 3 to the partner coset. -/
theorem generatedAxisGlobalTwelveFifthBindRoot3Transport_actual :
    generatedAxisGlobalBinaryAct generatedAxisGlobalTwelveFifthBindRoot3Transport.val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 3)) =
      generatedAxisGlobalBinaryRoot
        (identWordLocal generatedAxisGlobalTwelveFifthBindRoot3Letters) := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFifthBindRoot3Letters_root]
  change (generatedAxisGlobalBinaryAct
    ((generatedAxisGlobalFifthGenerator 12).val * (generatedAxisGlobalFifthGenerator 18).val *
      (generatedAxisGlobalFifthGenerator 16).val * (generatedAxisGlobalFifthGenerator 17).val *
      (generatedAxisGlobalFifthGenerator 4).val * (generatedAxisGlobalFifthGenerator 16).val)
    (generatedAxisGlobalFifthRoot 3)).val = _
  simp only [generatedAxisGlobalBinaryAct_mul]
  simp_rw [generatedAxisGlobalFifthGenerator_binary]
  decide +kernel

/-- Merged root 3 from a forward partner identification landing on a frame-fixing prefix times
the two-xi coset word (the shape of gforest's Seventh cell 3 transport). -/
theorem generatedAxisGlobalTwelveFifthBind_root3_of_forward_ident (i : Fin 12) (w : H)
    (pre : List IdentLetter) (hpre : ∀ l ∈ pre, l ≠ IdentLetter.xi)
    (he : sExtra (rhoLocal w (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal (identWordLocal (pre ++ generatedAxisGlobalTwelveFifthBindRoot3Letters))
        (generatedAxisGlobalTwelveRepresentative 4)) :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 3) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveFifthBind_merged_of_prefixed 1 pre
    generatedAxisGlobalTwelveFifthBindRoot3Letters
    generatedAxisGlobalTwelveFifthBindRoot3Transport.val hpre
    generatedAxisGlobalTwelveFifthBindRoot3Transport.property
    generatedAxisGlobalTwelveFifthBindRoot3Transport_actual
    (Or.inr (sixthPartner_inverse_mem i w _ _ he))

/-! ## The numerically found phase-fixing self prefixes -/

/-- Prefix of the forward self identification at the root 1 representative (gident's pilot). -/
def generatedAxisGlobalTwelveFifthBindPrefix1p : List IdentLetter :=
  [.qel (qmElt (4073160, false)), .sign 1024 0]

/-- Prefix of the inverse self identification at the root 1 representative. -/
def generatedAxisGlobalTwelveFifthBindPrefix1n : List IdentLetter :=
  [.qel (qmElt (6293364, false)), .sign 32 0]

/-- Prefix of the forward self identification at the root 6 representative. -/
def generatedAxisGlobalTwelveFifthBindPrefix6p : List IdentLetter :=
  [.qel (qmElt (1430880, false)), .sign 1024 0, .mono (0, false), .mono (1, true),
    .mono (0, false), .mono (1, true), .mono (0, false), .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, false), .mono (0, true), .mono (0, true), .mono (0, true), .mono (1, true),
    .mono (0, true), .mono (1, true), .mono (0, false), .mono (0, false), .mono (0, false),
    .mono (1, true), .mono (0, true), .mono (1, false), .mono (0, false), .mono (0, false),
    .mono (0, false), .mono (1, false), .mono (0, true), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false)]

/-- Prefix of the inverse self identification at the root 6 representative. -/
def generatedAxisGlobalTwelveFifthBindPrefix6n : List IdentLetter :=
  [.qel (qmElt (2729936, false)), .sign 768 0, .mono (0, false), .mono (1, true),
    .mono (0, true), .mono (0, true), .mono (1, true), .mono (0, true), .mono (1, true),
    .mono (0, false), .mono (0, false), .mono (1, false), .mono (0, true), .mono (1, false),
    .mono (0, true), .mono (1, false), .mono (0, false), .mono (1, false), .mono (0, true),
    .mono (1, false), .mono (0, false)]

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the root 1 forward prefix fixes Ω. -/
theorem generatedAxisGlobalTwelveFifthBindPrefix1p_fix :
    GeneratedAxisGlobalTwelveFifthBindFixPrefix generatedAxisGlobalTwelveFifthBindPrefix1p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the root 1 inverse prefix fixes Ω. -/
theorem generatedAxisGlobalTwelveFifthBindPrefix1n_fix :
    GeneratedAxisGlobalTwelveFifthBindFixPrefix generatedAxisGlobalTwelveFifthBindPrefix1n :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the root 6 forward prefix fixes Ω. -/
theorem generatedAxisGlobalTwelveFifthBindPrefix6p_fix :
    GeneratedAxisGlobalTwelveFifthBindFixPrefix generatedAxisGlobalTwelveFifthBindPrefix6p :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The computed Q-phase of the root 6 inverse prefix fixes Ω. -/
theorem generatedAxisGlobalTwelveFifthBindPrefix6n_fix :
    GeneratedAxisGlobalTwelveFifthBindFixPrefix generatedAxisGlobalTwelveFifthBindPrefix6n :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## The coset self identifications and their consequences -/

/-- (I1+), gident's pilot: `sExtra (h₁ · v₅) = (Q · σ₁₀₂₄ · h₁) · v₅`. -/
abbrev GeneratedAxisGlobalTwelveFifthBindIdent1p : Prop :=
  GeneratedAxisGlobalTwelveFifthBindSelfForward (generatedAxisGlobalTwelveFifthBindCosetLetters 1)
    generatedAxisGlobalTwelveFifthBindPrefix1p

/-- (I1-): `sExtra⁻¹ (h₁ · v₅) = (Q · σ₃₂ · h₁) · v₅`. -/
abbrev GeneratedAxisGlobalTwelveFifthBindIdent1n : Prop :=
  GeneratedAxisGlobalTwelveFifthBindSelfInverse (generatedAxisGlobalTwelveFifthBindCosetLetters 1)
    generatedAxisGlobalTwelveFifthBindPrefix1n

/-- (I6s+): `sExtra (h₆ · v₅) = (Q · σ₁₀₂₄ · π · h₆) · v₅`. -/
abbrev GeneratedAxisGlobalTwelveFifthBindIdent6p : Prop :=
  GeneratedAxisGlobalTwelveFifthBindSelfForward (generatedAxisGlobalTwelveFifthBindCosetLetters 2)
    generatedAxisGlobalTwelveFifthBindPrefix6p

/-- (I6s-): `sExtra⁻¹ (h₆ · v₅) = (Q · σ₇₆₈ · π · h₆) · v₅`. -/
abbrev GeneratedAxisGlobalTwelveFifthBindIdent6n : Prop :=
  GeneratedAxisGlobalTwelveFifthBindSelfInverse (generatedAxisGlobalTwelveFifthBindCosetLetters 2)
    generatedAxisGlobalTwelveFifthBindPrefix6n

/-- Either self identification at the root 1 representative binds both of its images. -/
theorem generatedAxisGlobalTwelveFifthBind_coset1_of_ident
    (h : GeneratedAxisGlobalTwelveFifthBindIdent1p ∨ GeneratedAxisGlobalTwelveFifthBindIdent1n) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 1) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 1) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [generatedAxisGlobalTwelveFifthBindCoset_eq_word,
    ← generatedAxisGlobalTwelveFifthBind_rep_four]
  rcases h with h | h
  · exact generatedAxisGlobalTwelveFifthBind_pair_of_selfForward
      generatedAxisGlobalTwelveFifthBindPrefix1p_fix h
  · exact generatedAxisGlobalTwelveFifthBind_pair_of_selfInverse
      generatedAxisGlobalTwelveFifthBindPrefix1n_fix h

/-- Either self identification at the root 6 representative binds both of its images. -/
theorem generatedAxisGlobalTwelveFifthBind_coset6_of_ident
    (h : GeneratedAxisGlobalTwelveFifthBindIdent6p ∨ GeneratedAxisGlobalTwelveFifthBindIdent6n) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 2) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 2) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [generatedAxisGlobalTwelveFifthBindCoset_eq_word,
    ← generatedAxisGlobalTwelveFifthBind_rep_four]
  rcases h with h | h
  · exact generatedAxisGlobalTwelveFifthBind_pair_of_selfForward
      generatedAxisGlobalTwelveFifthBindPrefix6p_fix h
  · exact generatedAxisGlobalTwelveFifthBind_pair_of_selfInverse
      generatedAxisGlobalTwelveFifthBindPrefix6n_fix h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
