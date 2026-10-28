/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryNonPairClasses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleIndependentShortTransport

/-! Actual binary independence for every nonpair secondary input.
The only short line in the first/Omega binary plane is its original plus-pair mate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Genuine preferred short classes have distinct actual extraspecial binary bases. -/
theorem generatedFeasible_short_base_injective :
    Function.Injective (fun r : GriessShortIndex => (griessShortQ r).base) := by
  intro r s h
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact congrArg toAdd h

/-- The actual plus-pair vector is the initial frame vector minus the actual minus-pair vector. -/
theorem generatedFeasible_pair_mate_integral :
    griessShortLatticeVector (Sum.inl (1, generatedFeasiblePhysicalRootPair)) =
      leechCoordinateFrameLattice 0 -
        griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
  apply Subtype.ext
  funext i
  simp only [griessShortLatticeVector, griessShortIntegral,
    generatedFeasiblePhysicalRootPair_coordinates, leechCoordinateFrameLattice,
    leechCoordinateFrameVector, Submodule.coe_sub, Pi.sub_apply]
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp_all

/-- The original Omega base plus the minus-pair base is exactly the plus-pair base. -/
theorem generatedFeasible_pair_mate_base :
    toAdd (griessShortQ (Sum.inl (1, generatedFeasiblePhysicalRootPair))).base =
      toAdd sourceOmegaQ.base +
        toAdd (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base := by
  have hs : griessShortClass (Sum.inl (1, generatedFeasiblePhysicalRootPair)) =
      leechReduction (leechCoordinateFrameLattice 0) +
        griessShortClass (Sum.inl (0, generatedFeasiblePhysicalRootPair)) := by
    unfold griessShortClass
    rw [generatedFeasible_pair_mate_integral, map_sub, sub_eq_add_neg,
      ← map_neg, leechReduction_neg]
  change leechHyperbolicCoordinates (griessShortClass _) =
    toAdd sourceOmegaQ.base + leechHyperbolicCoordinates (griessShortClass _)
  rw [hs, map_add]
  have hΩ : toAdd sourceOmegaQ.base =
      leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0)) :=
    sourceOmegaQ_eq_frame_class
  rw [hΩ]

/-- No nonpair sector contains any coordinate-pair preferred label. -/
theorem generatedFeasibleSecondaryNonPair_ne_pair (k : Fin 3) (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels k) (a : Fin 2) (p : Fin 276) :
    r ≠ Sum.inl (a, p) := by
  intro he
  subst r
  fin_cases k <;> obtain ⟨z, _, he⟩ := Finset.mem_map.mp hr <;> cases he

/-- Every actual nonpair input is outside the first/Omega binary plane. -/
theorem generatedFeasibleSecondaryNonPair_independent (k : Fin 3) (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels k) :
    (griessShortQ r).base ≠
        (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base ∧
      toAdd (griessShortQ r).base ≠ toAdd sourceOmegaQ.base +
        toAdd (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base := by
  constructor
  · intro h
    exact generatedFeasibleSecondaryNonPair_ne_pair k r hr 0 _
      (generatedFeasible_short_base_injective h)
  · intro h
    rw [← generatedFeasible_pair_mate_base] at h
    exact generatedFeasibleSecondaryNonPair_ne_pair k r hr 1 _
      (generatedFeasible_short_base_injective (toAdd.injective h))

/-- Both signed axes of every actual nonpair input are connected inside the simultaneous
first-axis and Omega stabilizer. -/
theorem generatedFeasibleSecondaryNonPair_signed (k : Fin 3) (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleSecondaryNonPairLabels k) (c d : ZMod 2) :
    ∃ h : ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer),
      rhoLocal h.val (conwayShortAxis r c) = conwayShortAxis r d := by
  have hi := generatedFeasibleSecondaryNonPair_independent k r hr
  exact generatedFeasible_independent_short_signed _ r hi.1 hi.2 c d

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
