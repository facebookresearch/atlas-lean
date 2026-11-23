/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWWeightedBounds
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWMultiaffineBounded
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinCoefficientTarget

/-!

# The edge-weighted root identity

The edge-weighted form of the Kac-Ward identity, whose constant-weight case gives the spin Kac-Ward
identities.

## i. Overview

With independent edge weights, the character-weighted even-subgraph sum is
`∑_F χ_{a,b}(hom F) ∏_{e ∈ F} w_e`. The edge-weighted root identity states that, for weights bounded
below Sherman's radius, the walk-series square root of the twisted edge-weighted Kac-Ward
determinant equals this sum. Specializing to constant weights `x` and squaring gives the spin
Kac-Ward identities for small `x`, hence for all `x`.

## ii. Key results

- `ons_weightedSpinCharacterSum` : the edge-weighted character sum
- `ons_weightedRootIdentity` : the edge-weighted root identity
- `ons_spinKacWardIdentities_of_weightedRoot` : the root identity implies the spin Kac-Ward
  identities

## iii. Table of contents

- A. Edge-weighted character sums
- B. The root identity

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

/-! ## A. Edge-weighted character sums -/

/-- The edge-weighted spin-character sum `∑_F χ_{a,b}(hom F) ∏_{e ∈ F} w_e` over even subgraphs of
the torus. -/
noncomputable def ons_weightedSpinCharacterSum
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) : ℂ :=
  ∑ F ∈ evenSubgraphs (onsTorusGraph L),
    (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
      ∏ edge ∈ F, weight edge

lemma ons_weightedSpinCharacterSum_const
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L (fun _ => (x : ℂ)) a b =
      (ons_spinCharacterSum L x a b : ℂ) := by
  unfold ons_weightedSpinCharacterSum ons_spinCharacterSum
  push_cast
  apply Finset.sum_congr rfl
  intro F hF
  simp

/-! ## B. The root identity -/

/-- The edge-weighted root identity on the `L × L` torus: for every spin structure and every edge
weight bounded by `q` below Sherman's radius, the walk-series square root of the twisted
edge-weighted Kac-Ward determinant equals the edge-weighted character sum. -/
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

lemma ons_spinCoefficientIdentity_of_weightedRoot
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

/-- Sherman's radius for `L > 2`, and `1` otherwise. -/
noncomputable def ons_spinShermanRadius (L : ℕ) : ℝ :=
  if h : 2 < L then
    letI : NeZero L := ⟨by omega⟩
    ons_ShermanRadius L
  else 1

lemma ons_spinShermanRadius_pos (L : ℕ) :
    0 < ons_spinShermanRadius L := by
  by_cases h : 2 < L
  · let : NeZero L := ⟨by omega⟩
    simpa [ons_spinShermanRadius, h] using ons_ShermanRadius_pos L
  · simp [ons_spinShermanRadius, h]

lemma ons_spinKacWardIdentities_of_weightedRoot
    (hweighted : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_weightedRootIdentity L)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_small
    ons_spinShermanRadius ons_spinShermanRadius_pos
  intro L hL
  let : Fact (2 < L) := ⟨hL⟩
  intro x hx
  rw [ons_spinKacWardAt_iff_coefficientIdentity]
  have hx' : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L) := by
    simpa [ons_spinShermanRadius, hL] using hx
  exact ons_spinCoefficientIdentity_of_weightedRoot L (hweighted L hL) hx'

end StatMech.Onsager
