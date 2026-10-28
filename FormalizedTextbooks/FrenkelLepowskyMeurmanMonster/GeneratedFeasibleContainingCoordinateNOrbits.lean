/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingCoordinatePhasePartition

/-! Actual simultaneous orbits of the two containing coordinate triality prototypes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original simultaneous first-axis and Omega stabilizer. -/
abbrev GeneratedFeasibleContainingN :=
  ↥(localAxisStabilizer generatedFeasiblePhysicalRootPair ⊓ localOmegaStabilizer)

/-- The genuine simultaneous vector orbit of any original Griess vector. -/
def generatedFeasibleContainingCoordinateNOrbit (x : GriessSpace) : Set GriessSpace :=
  Set.range (fun n : GeneratedFeasibleContainingN => rhoLocal n.val x)

/-- Actual triality transports a simultaneous word to another simultaneous word. -/
theorem generatedFeasibleContaining_N_triality_word (n : GeneratedFeasibleContainingN) :
    ∃ k : GeneratedFeasibleContainingN, ∀ x : GriessSpace,
      rhoLocal k.val (sExtra x) = sExtra (rhoLocal n.val x) := by
  let n' : localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair :=
    ⟨⟨n.val, n.property.1⟩, n.property.2⟩
  obtain ⟨k, hk⟩ := localFeasibleTransition_triality_conjugate _ n'
  have hw : extraIntoGenerated * localIntoGenerated n.val =
      localIntoGenerated k.val.val * extraIntoGenerated := by
    calc
      _ = (extraIntoGenerated * localIntoGenerated n.val * extraIntoGenerated⁻¹) *
        extraIntoGenerated := by group
      _ = _ := by rw [hk]
  refine ⟨⟨k.val.val, k.val.property, k.property⟩, ?_⟩
  intro x
  have he := congrArg (fun g : G => g.val x) hw
  change sExtra (rhoLocal n.val x) = rhoLocal k.val.val (sExtra x) at he
  exact he.symm

/-- The actual triality image of a whole simultaneous orbit is the whole image orbit. -/
theorem generatedFeasibleContaining_N_triality_image (x : GriessSpace) :
    sExtra '' generatedFeasibleContainingCoordinateNOrbit x =
      generatedFeasibleContainingCoordinateNOrbit (sExtra x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    obtain ⟨k, hk⟩ := generatedFeasibleContaining_N_triality_word n
    exact ⟨k, hk x⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := generatedFeasibleContaining_N_triality_word n
    obtain ⟨l, hl⟩ := generatedFeasibleContaining_N_triality_word k
    refine ⟨rhoLocal l.val x, ⟨l, rfl⟩, ?_⟩
    have ht : sExtra (sExtra (rhoLocal n.val (sExtra x))) = rhoLocal l.val x := by
      rw [← hk, ← hl, sExtra_triple]
    apply sExtra.injective
    apply sExtra.injective
    rw [sExtra_triple, ht]

/-- Triality preserves the exact cardinality of every actual simultaneous orbit. -/
theorem generatedFeasibleContaining_N_triality_card (x : GriessSpace) :
    Nat.card (generatedFeasibleContainingCoordinateNOrbit (sExtra x)) =
      Nat.card (generatedFeasibleContainingCoordinateNOrbit x) := by
  rw [← generatedFeasibleContaining_N_triality_image]
  exact (Nat.card_congr (sExtra.toEquiv.image
    (generatedFeasibleContainingCoordinateNOrbit x))).symm

/-- The first original coordinate phase prototype has exactly 4928 simultaneous images. -/
theorem generatedFeasibleContainingCoordinateFirstNOrbit_card :
    Nat.card (generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingOctadDestination) = 4928 := by
  rw [generatedFeasibleContainingOctadDestination, generatedFeasibleContaining_N_triality_card]
  exact generatedFeasibleContainingOctadOrbit_card

/-- The second original coordinate phase prototype has exactly 4928 simultaneous images. -/
theorem generatedFeasibleContainingCoordinateSecondNOrbit_card :
    Nat.card (generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingTrialitySquare) = 4928 := by
  rw [generatedFeasibleContainingTrialitySquare, generatedFeasibleContaining_N_triality_card]
  exact generatedFeasibleContainingCoordinateFirstNOrbit_card

/-- The entire original preferred mate coordinate is invariant under the simultaneous group. -/
theorem generatedFeasibleContaining_N_mate_coordinate (n : GeneratedFeasibleContainingN)
    (x : GriessSpace) :
    (griessConwayEncode (rhoLocal n.val x)).2.1 generatedFeasibleMateLabel =
      (griessConwayEncode x).2.1 generatedFeasibleMateLabel := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup n.val
  change localFiberIntoH f = n.val at hf
  have hfirst : localFiberIntoH f ∈ localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    hf.symm ▸ n.property.1
  have hOmega : localFiberIntoH f ∈ localOmegaStabilizer := hf.symm ▸ n.property.2
  have hmon := generatedFeasible_localOmega_lift_monomial f hOmega
  have hp := (localAxisStabilizer_mk_iff f generatedFeasiblePhysicalRootPair).mp hfirst
  have hm := (generatedFeasible_monomial_pair_fix_iff f.val.2 hmon).mp hp.1
  change griessShortPermutation f.val.2 generatedFeasibleMateLabel =
    generatedFeasibleMateLabel at hm
  rw [← hf]
  change (griessConwayEncode (localGriessRepresentation f x)).2.1 _ = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  have hi := localShortOperator_image f (griessConwayEncode x).2.1 generatedFeasibleMateLabel
  rw [hm, generatedFeasibleMate_phase_zero f hfirst hOmega, qSign_zero, one_mul] at hi
  exact hi

/-- The original standard octad outer square at coordinates zero and one is exactly one. -/
theorem generatedFeasibleContaining_prototype_pair_product :
    2 * griessShortVector generatedFeasibleContainingOctadPrototypeLabel 0 *
      griessShortVector generatedFeasibleContainingOctadPrototypeLabel 1 = 1 := by
  simp only [griessShortVector, generatedFeasibleContainingOctadPrototype_integral]
  norm_num
  have hs : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hn : Real.sqrt 8 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp
  nlinarith

/-- The first coordinate prototype has original preferred mate coefficient minus one. -/
theorem generatedFeasibleContainingCoordinateFirst_mate :
    (griessConwayEncode generatedFeasibleContainingOctadDestination).2.1
      generatedFeasibleMateLabel = -1 := by
  rw [generatedFeasibleContainingOctadDestination, generatedFeasibleMateLabel]
  change (griessConwayEncode (sExtra (conwayShortAxis
    (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0))).2.1
      (Sum.inl (1, generatedFeasiblePhysicalRootPair)) = -1
  rw [generatedAxis_triality_octad_pair_coordinate,
    generatedFeasiblePhysicalRootPair_coordinates]
  change (-1 : ℝ) * (2 * griessShortVector generatedFeasibleContainingOctadPrototypeLabel 0 *
    griessShortVector generatedFeasibleContainingOctadPrototypeLabel 1) = -1
  rw [generatedFeasibleContaining_prototype_pair_product, mul_one]

/-- The second coordinate prototype has original preferred mate coefficient plus one. -/
theorem generatedFeasibleContainingCoordinateSecond_mate :
    (griessConwayEncode generatedFeasibleContainingTrialitySquare).2.1
      generatedFeasibleMateLabel = 1 := by
  rw [generatedFeasibleContainingTrialitySquare, generatedFeasibleContainingOctadDestination,
    generatedFeasibleMateLabel]
  change (griessConwayEncode (sExtra (sExtra (conwayShortAxis
    (Sum.inr (Sum.inl (generatedFeasibleContainingOctadPrototypeIndex, 0))) 0)))).2.1
      (Sum.inl (1, generatedFeasiblePhysicalRootPair)) = 1
  rw [generatedFeasibleContaining_triality_square_pair_coordinate,
    generatedFeasiblePhysicalRootPair_coordinates]
  exact generatedFeasibleContaining_prototype_pair_product

/-- The two original coordinate prototypes have disjoint actual simultaneous orbits. -/
theorem generatedFeasibleContainingCoordinateNOrbits_disjoint :
    Disjoint (generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingOctadDestination)
      (generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨n, hn⟩ ⟨m, hm⟩
  change rhoLocal n.val generatedFeasibleContainingOctadDestination = x at hn
  change rhoLocal m.val generatedFeasibleContainingTrialitySquare = x at hm
  have h1 := generatedFeasibleContaining_N_mate_coordinate n
    generatedFeasibleContainingOctadDestination
  have h2 := generatedFeasibleContaining_N_mate_coordinate m
    generatedFeasibleContainingTrialitySquare
  rw [hn, generatedFeasibleContainingCoordinateFirst_mate] at h1
  rw [hm, generatedFeasibleContainingCoordinateSecond_mate] at h2
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
