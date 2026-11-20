/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeightedBounds
import Code.Onsager.KWMultiaffineBounded
import Code.Onsager.SpinCoefficientTarget










namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

noncomputable def ons_weightedSpinCharacterSum
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) : ℂ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
      ∏ edge ∈ F, weight edge

theorem ons_weightedSpinCharacterSum_const
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L (fun _ => (x : ℂ)) a b =
      (ons_spinCharacterSum L x a b : ℂ) := by
  unfold ons_weightedSpinCharacterSum ons_spinCharacterSum
  push_cast
  apply Finset.sum_congr rfl
  intro F hF
  simp



def ons_weightedRootIdentity (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ (a b : Fin 2)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (q : ℝ),
    0 ≤ q →
    (∀ edge, ‖weight edge‖ ≤ q) →
    q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹ →
    ons_detWalkRoot
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_weightedSpinCharacterSum L weight a b

theorem ons_spinCoefficientIdentity_of_weightedRoot
    (L : ℕ) [Fact (2 < L)]
    (hweighted : ons_weightedRootIdentity L)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
    ons_spinCoefficientIdentity L x := by
  intro a b
  have hbound : ∀ edge : Sym2 (ZMod L × ZMod L),
      ‖(x : ℂ)‖ ≤ x := by
    intro edge
    simp [abs_of_pos hx.1]
  have hroot := hweighted a b (fun _ => (x : ℂ)) x hx.1.le
    hbound (by simpa [ons_ShermanRadius] using hx.2)
  have hsq := ons_KWmatWeightedPhase_detWalkRoot_sq
    L (fun _ => (x : ℂ)) a b x hx.1.le hbound
      (by simpa [ons_ShermanRadius] using hx.2)
  rw [ons_KWmatWeightedPhase_const,
    ons_weightedSpinCharacterSum_const] at hroot
  calc
    (ons_spinCharacterSum L x a b : ℂ) ^ 2 =
        ons_detWalkRoot (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) ^ 2 := by rw [hroot]
    _ = _ := hsq

noncomputable def ons_spinShermanRadius (L : ℕ) : ℝ :=
  if h : 2 < L then
    letI : NeZero L := ⟨by omega⟩
    ons_ShermanRadius L
  else 1

theorem ons_spinShermanRadius_pos (L : ℕ) :
    0 < ons_spinShermanRadius L := by
  by_cases h : 2 < L
  · letI : NeZero L := ⟨by omega⟩
    simpa [ons_spinShermanRadius, h] using ons_ShermanRadius_pos L
  · simp [ons_spinShermanRadius, h]

theorem ons_spinKacWardIdentities_of_weightedRoot
    (hweighted : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_weightedRootIdentity L)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_small
    ons_spinShermanRadius ons_spinShermanRadius_pos
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  intro x hx
  rw [ons_spinKacWardAt_iff_coefficientIdentity]
  have hx' : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L) := by
    simpa [ons_spinShermanRadius, hL] using hx
  exact ons_spinCoefficientIdentity_of_weightedRoot L (hweighted L hL) hx'

end StatMech.Onsager
