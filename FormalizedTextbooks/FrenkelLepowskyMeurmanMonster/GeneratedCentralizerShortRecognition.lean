/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual centralizer's matrix and short actions recognize a genuine Leech isometry. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerJordan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerFixedProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerShortSquare
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ShortCoordinateRecognitionMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual fixed-space square has the original short-coordinate outer-square matrix. -/
theorem generatedCentral_short_square_coordinates (X : GriessShortIndex → ℝ) :
    (generatedCentralPlusCoordinates (generatedCentralPlusProduct
      (generatedCentralPlusEmbed 0 X) (generatedCentralPlusEmbed 0 X))).1.val =
      shortCoordinateSquare X := generatedCentral_short_square_encode X

/-- Actual product preservation links the short-coordinate square to spatial conjugation. -/
theorem generatedCentralizerShortAction_square (g : generatedCentralizer)
    (R : Matrix (Fin 24) (Fin 24) ℝ)
    (hR : ∀ A : Sym24, (generatedCentralizerMatrixAction g A).val = R * A.val * R.transpose)
    (X : GriessShortIndex → ℝ) :
    shortCoordinateSquare (generatedCentralizerShortAction g X) =
      R * shortCoordinateSquare X * R.transpose := by
  have hs : generatedCentralizerPlusEquiv g (generatedCentralPlusEmbed 0 X) =
      generatedCentralPlusEmbed 0 (generatedCentralizerShortAction g X) :=
    Subtype.ext (generatedCentralizerShortAction_embed g X)
  have hc := congrArg (fun x : generatedCentralPlus =>
      (generatedCentralPlusCoordinates x).1.val)
    (generatedCentralPlusProduct_covariant g
      (generatedCentralPlusEmbed 0 X) (generatedCentralPlusEmbed 0 X))
  rw [generatedCentralizerPlusCoordinates_action, hs, generatedCentral_short_square_coordinates,
    hR, generatedCentral_short_square_coordinates] at hc
  exact hc.symm

/-- Every element of the actual centralizer determines a genuine Leech lattice isometry
and the same signed label permutation on the short-coordinate space. -/
theorem generatedCentralizer_short_spatial_recognition (g : generatedCentralizer) :
    ∃ R : Matrix (Fin 24) (Fin 24) ℝ,
      ∃ hTR : R.transpose * R = 1, ∃ hRT : R * R.transpose = 1,
      (∀ A : Sym24, (generatedCentralizerMatrixAction g A).val = R * A.val * R.transpose) ∧
      (∃ p : Equiv.Perm GriessShortIndex, ∀ r,
        (generatedCentralizerShortAction g (shortCoordinateUnit r) = shortCoordinateUnit (p r) ∨
          generatedCentralizerShortAction g (shortCoordinateUnit r) = -shortCoordinateUnit (p r)) ∧
        (R *ᵥ griessShortVector r = griessShortVector (p r) ∨
          R *ᵥ griessShortVector r = -griessShortVector (p r))) ∧
      shortCoordinateOrthogonalEquiv R hTR hRT ∈ leechIsomSubgroup := by
  obtain ⟨R, hTR, hRT, hR⟩ := generatedCentralizer_orthogonal_matrix_action g
  have hr := shortCoordinateRecognition_matrix_square (generatedCentralizerShortAction g) R
    (generatedCentralizerShortAction_pairing g) hTR hRT
    (generatedCentralizerShortAction_square g R hR)
  exact ⟨R, hTR, hRT, hR, hr⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
