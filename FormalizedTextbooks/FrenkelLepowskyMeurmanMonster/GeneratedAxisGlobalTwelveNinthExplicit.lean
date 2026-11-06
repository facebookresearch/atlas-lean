/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveNinthBindings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords

/-! Explicit Ninth root words and the identification interface.

For each of the eight type-four Ninth forest roots we fix an explicit word in the ten original odd
source letters, compute its actual binary root, and match that root to the forest root mask by an
explicit word in the six Ninth letters. Hence each root binding
`GeneratedAxisGlobalTwelveNinthRootBound j` reduces to the two triality images of one explicit
vector `rhoLocal (generatedAxisGlobalTwelveNinthExplicitWord j) generatedNinthAxis`, and Ninth
family coverage reduces to fourteen explicit identifications (roots `1, ..., 7`, both signs). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original odd source-letter words for the eight Ninth roots (the head letter acts last). -/
def generatedAxisGlobalTwelveNinthExplicitLetters : Fin 8 → List (Fin 10) :=
  ![[], [0], [0, 8, 0], [0, 6], [0, 6, 6], [0, 8, 7], [0, 7, 0, 7, 1], [0, 8, 7, 0, 6, 6, 1, 6]]

/-- The explicit local root word. -/
def generatedAxisGlobalTwelveNinthExplicitWord (j : Fin 8) : H :=
  ((generatedAxisGlobalTwelveNinthExplicitLetters j).map generatedAxisGlobalOddSourceLocalLetter).prod

/-- The binary roots of the explicit root words. -/
def generatedAxisGlobalTwelveNinthExplicitMask : Fin 8 → ℕ :=
  ![2048, 4196352, 4194316, 4200448, 4851712, 7346176, 4790272, 702464]

/-- Words in the six Ninth letters carrying each forest root mask to the explicit binary root. -/
def generatedAxisGlobalTwelveNinthExplicitMatch : Fin 8 → List (Fin 6) :=
  ![[], [4, 2, 2, 4, 4, 4, 2, 2, 4, 5, 1, 0], [2, 2, 1, 1, 5, 0, 4, 2, 2, 4, 0, 4],
    [2, 0, 4, 0, 5, 4, 4, 4, 2, 0], [4, 5, 1, 0, 5, 1, 2, 2, 2], [1, 1, 2, 4, 4, 0, 5, 0],
    [5, 1, 2, 2, 2, 0, 1], [1, 2]]

private theorem ninthExplicitProduct_binary (ls : List (Fin 10)) (b : ℕ) :
    co1BinaryAction (projH ((ls.map generatedAxisGlobalOddSourceLocalLetter).prod))
      (monsterCo1GeometryBinaryMaskDecode b) =
      monsterCo1GeometryBinaryMaskDecode
        (ls.foldr (fun l x => generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalOddSourceRows l) x) b) := by
  induction ls generalizing b with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, LinearEquiv.mul_apply]
    rw [ih, generatedAxisGlobalOddSourceLocalLetter_binary]

set_option maxHeartbeats 4000000 in
-- Replay the eight explicit words on their binary roots.
/-- Every explicit word carries its binary root to the actual Ω mask. -/
theorem generatedAxisGlobalTwelveNinthExplicitLetters_certificate : ∀ j : Fin 8,
    (generatedAxisGlobalTwelveNinthExplicitLetters j).foldr (fun l x =>
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddSourceRows l) x)
        (generatedAxisGlobalTwelveNinthExplicitMask j) = 2048 := by
  decide +kernel

/-- The actual binary root of each explicit word is its displayed mask. -/
theorem generatedAxisGlobalTwelveNinthExplicitWord_root (j : Fin 8) :
    (generatedAxisGlobalBinaryRoot (generatedAxisGlobalTwelveNinthExplicitWord j)).val =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveNinthExplicitMask j) := by
  have hw : co1BinaryAction (projH (generatedAxisGlobalTwelveNinthExplicitWord j))
      (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveNinthExplicitMask j)) =
      Multiplicative.toAdd (qQuotHom sourceOmegaQ) := by
    rw [generatedAxisGlobalTwelveNinthExplicitWord, ninthExplicitProduct_binary,
      generatedAxisGlobalTwelveNinthExplicitLetters_certificate,
      generatedAxisGlobalTwelveNinthOmega_mask]
  change co1BinaryAction (projH (generatedAxisGlobalTwelveNinthExplicitWord j)⁻¹)
    (Multiplicative.toAdd (qQuotHom sourceOmegaQ)) = _
  rw [map_inv, ← hw, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- The explicit word of the Ω root is the identity. -/
theorem generatedAxisGlobalTwelveNinthExplicitWord_zero :
    generatedAxisGlobalTwelveNinthExplicitWord 0 = 1 := rfl

set_option maxHeartbeats 4000000 in
-- Replay the eight matching words on the forest root masks.
/-- Each matching word carries the forest root mask to the explicit binary root. -/
theorem generatedAxisGlobalTwelveNinthExplicitMatch_certificate : ∀ j : Fin 8,
    generatedNinthLowerSpinThreeProjectionMaskWord (generatedAxisGlobalTwelveNinthExplicitMatch j)
      (generatedAxisGlobalTwelveNinthRootMask j) = generatedAxisGlobalTwelveNinthExplicitMask j := by
  decide +kernel

/-- A Ninth root binding from the two triality images of the explicit root vector. -/
theorem generatedAxisGlobalTwelveNinthRootBound_of_explicit (j : Fin 8)
    (hpos : sExtra (rhoLocal (generatedAxisGlobalTwelveNinthExplicitWord j) generatedNinthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveNinthExplicitWord j) generatedNinthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveNinthRootBound j :=
  generatedAxisGlobalTwelveNinthRootBound_of_word j _ (generatedAxisGlobalTwelveNinthExplicitMatch j)
    (generatedAxisGlobalTwelveNinthWord_root_mask j _ _ _
      (generatedAxisGlobalTwelveNinthExplicitWord_root j)
      (generatedAxisGlobalTwelveNinthExplicitMatch_certificate j)) hpos hneg

/-- A Ninth root binding from two explicit identification equations. -/
theorem generatedAxisGlobalTwelveNinthRootBound_of_explicit_eq (j : Fin 8) (kp kn : Fin 12)
    (gp gn : H)
    (hpos : sExtra (rhoLocal (generatedAxisGlobalTwelveNinthExplicitWord j) generatedNinthAxis) =
      rhoLocal gp (generatedAxisGlobalTwelveRepresentative kp))
    (hneg : sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveNinthExplicitWord j) generatedNinthAxis) =
      rhoLocal gn (generatedAxisGlobalTwelveRepresentative kn)) :
    GeneratedAxisGlobalTwelveNinthRootBound j :=
  generatedAxisGlobalTwelveNinthRootBound_of_explicit j
    (generatedAxisGlobalTwelve_mem_of_transport kp gp hpos)
    (generatedAxisGlobalTwelve_mem_of_transport kn gn hneg)

/-- Ninth family coverage from the fourteen explicit identifications (roots `1, ..., 7`). -/
theorem generatedAxisGlobalTwelve_ninth_covered_of_explicit
    (hpos : ∀ j : Fin 8, j ≠ 0 →
      sExtra (rhoLocal (generatedAxisGlobalTwelveNinthExplicitWord j) generatedNinthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : ∀ j : Fin 8, j ≠ 0 →
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveNinthExplicitWord j) generatedNinthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 8 :=
  generatedAxisGlobalTwelve_ninth_covered_of fun j hj =>
    generatedAxisGlobalTwelveNinthRootBound_of_explicit j (hpos j hj) (hneg j hj)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
