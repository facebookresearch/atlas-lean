/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightLink
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightFrame
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootEightPhase

/-! Binding wrappers for the identification wave: once an identification lemma is proved, these
statements turn it into the open root-eight hypotheses of
`generatedAxisGlobalTwelve_rootEight_covered_of_open`, with no further work.

* A transport from the root-eight side, `sExtra^e (r_k x0) = g · rep_j`, binds the image
  directly.
* A transport from another family onto a frame translate `n * r_k` of a root word (`n` an
  Xi-free monomial word, so its projection fixes the binary Ω class) binds both images at root
  word `k`, given the source family's opposite triality image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option backward.isDefEq.respectTransparency false

/-- A forward identification from the root-eight side binds the forward image. -/
theorem generatedAxisGlobalTwelveRootEight_positive_of_transport (k : Fin 23) (j : Fin 12)
    (g : H)
    (htrans : sExtra (rhoLocal (rootEightForestRootWord k)
      (generatedAxisGlobalTwelveRepresentative 9)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra (rhoLocal (rootEightForestRootWord k) (generatedAxisGlobalTwelveRepresentative 9)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_transport j g htrans

/-- An inverse identification from the root-eight side binds the inverse image. -/
theorem generatedAxisGlobalTwelveRootEight_negative_of_transport (k : Fin 23) (j : Fin 12)
    (g : H)
    (htrans : sExtra.symm (rhoLocal (rootEightForestRootWord k)
      (generatedAxisGlobalTwelveRepresentative 9)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) :
    sExtra⁻¹ (rhoLocal (rootEightForestRootWord k) (generatedAxisGlobalTwelveRepresentative 9)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  rw [LinearEquiv.coe_inv]
  exact generatedAxisGlobalTwelve_mem_of_transport j g htrans

/-- Known triality images at a frame translate `n * r_k` bind root word `k`. -/
theorem generatedAxisGlobalTwelveRootEight_root_pair_of_frame (k : Fin 23) (n : H)
    (hn : projH n ∈ co1OmegaFrameStabilizer)
    (hpos : sExtra (rhoLocal (n * rootEightForestRootWord k)
      (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal (n * rootEightForestRootWord k)
      (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply generatedAxisGlobalTwelve_root_pair_mem _ (generatedAxisGlobalTwelveRepresentative 9)
    (n * rootEightForestRootWord k) (rootEightForestRootWord k) 1
    (by rw [map_one, LinearEquiv.coe_one, id_eq]) _ hpos hneg
  rw [rootEightFrame_binaryRoot n _ hn]
  apply Subtype.ext
  change co1BinaryAction (projH 1) _ = _
  rw [map_one, map_one]
  rfl

/-- A forward whole transport of a listed family onto a frame translate of root word `k`, with
the source family's inverse image in the union, binds both images at root word `k`. -/
theorem generatedAxisGlobalTwelveRootEight_root_pair_of_forward_frame (j : Fin 12) (x : H)
    (k : Fin 23) (n : H) (hn : projH n ∈ co1OmegaFrameStabilizer)
    (htrans : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal (n * rootEightForestRootWord k) (generatedAxisGlobalTwelveRepresentative 9))
    (hsrc : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hp, hm⟩ :=
    generatedAxisGlobalTwelveRootEight_pair_of_forward_transport j x _ htrans hsrc
  exact generatedAxisGlobalTwelveRootEight_root_pair_of_frame k n hn hp hm

/-- An inverse whole transport of a listed family onto a frame translate of root word `k`, with
the source family's forward image in the union, binds both images at root word `k`. -/
theorem generatedAxisGlobalTwelveRootEight_root_pair_of_inverse_frame (j : Fin 12) (x : H)
    (k : Fin 23) (n : H) (hn : projH n ∈ co1OmegaFrameStabilizer)
    (htrans : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal (n * rootEightForestRootWord k) (generatedAxisGlobalTwelveRepresentative 9))
    (hsrc : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨hp, hm⟩ :=
    generatedAxisGlobalTwelveRootEight_pair_of_inverse_transport j x _ htrans hsrc
  exact generatedAxisGlobalTwelveRootEight_root_pair_of_frame k n hn hp hm

/-- The forward-frame binding with the transporter given as an Xi-free monomial word in the
identification alphabet followed by root word `k`. -/
theorem generatedAxisGlobalTwelveRootEight_root_pair_of_forward_word (j : Fin 12) (x : H)
    (k : Fin 23) (ls : List IdentLetter) (hls : ∀ l ∈ ls, l ≠ IdentLetter.xi)
    (htrans : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal (identWordLocal ls * rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9))
    (hsrc : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveRootEight_root_pair_of_forward_frame j x k _
    (rootEightFrame_identWord ls hls) htrans hsrc

/-- The inverse-frame binding with the transporter given as an Xi-free monomial word in the
identification alphabet followed by root word `k`. -/
theorem generatedAxisGlobalTwelveRootEight_root_pair_of_inverse_word (j : Fin 12) (x : H)
    (k : Fin 23) (ls : List IdentLetter) (hls : ∀ l ∈ ls, l ≠ IdentLetter.xi)
    (htrans : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) =
      rhoLocal (identWordLocal ls * rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9))
    (hsrc : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative j)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveRootEight_root_pair_of_inverse_frame j x k _
    (rootEightFrame_identWord ls hls) htrans hsrc

/-- Root-eight family coverage from explicit whole-vector identifications of the 22 forward
images at the non-identity root words and of the 15 inverse images at the unmerged ones. -/
theorem generatedAxisGlobalTwelve_rootEight_covered_of_identifications
    (hpositive : ∀ k : Fin 23, k ≠ 0 → ∃ j : Fin 12, ∃ g : H,
      sExtra (rhoLocal (rootEightForestRootWord k) (generatedAxisGlobalTwelveRepresentative 9)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative j))
    (hnegative : ∀ k ∈ rootEightForestNegativeOpen, ∃ j : Fin 12, ∃ g : H,
      sExtra.symm (rhoLocal (rootEightForestRootWord k)
        (generatedAxisGlobalTwelveRepresentative 9)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) :
    GeneratedAxisGlobalTwelveFamilyCovered 9 := by
  apply generatedAxisGlobalTwelve_rootEight_covered_of_open
  · intro k hk
    obtain ⟨j, g, h⟩ := hpositive k hk
    exact generatedAxisGlobalTwelveRootEight_positive_of_transport k j g h
  · intro k hk
    obtain ⟨j, g, h⟩ := hnegative k hk
    exact generatedAxisGlobalTwelveRootEight_negative_of_transport k j g h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
