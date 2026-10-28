/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleFifthSlotCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthLocalOrbit

/-! Attainment for the orbit of the slot axis under the actual fifth-axis stabilizer.

Two original spatial generators of the actual fifth-axis projection, the sixth selected
monomial permutation and Seysen's ξ, have genuine whole-axis lifts in the actual stabilizer.
Their exact integer actions move the slot label through all sixteen catalogue labels. With
the coverage theorem this identifies the entire actual stabilizer orbit of the slot axis with
the sixteen-element catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option maxRecDepth 20000
attribute [local irreducible] generatedFifthAxis

/-- Explicit integer coordinates of a signed pair label on an ordered coordinate pair. -/
def generatedFeasibleFifthSlotPairIntegral (s : Fin 2) (a b : Fin 24) : Fin 24 → ℤ :=
  fun i => 4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)

/-- Every catalogue label has its explicit physical integer coordinates. -/
theorem generatedFeasibleFifthSlotCatalogue_integral (k : Fin 16) :
    griessShortIntegral (generatedFeasibleFifthSlotCatalogueLabel k) =
      generatedFeasibleFifthSlotPairIntegral (generatedFeasibleFifthSlotCatalogueData k).1
        (generatedFeasibleFifthSlotCatalogueData k).2.1.1
        (generatedFeasibleFifthSlotCatalogueData k).2.1.2 := by
  have hc : griessCoordinatePair (griessCoordinatePairEquiv.symm
      ⟨_, generatedFeasibleFifthSlotCatalogueData_mem k⟩) =
        (generatedFeasibleFifthSlotCatalogueData k).2.1 :=
    congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply _)
  funext i
  simp only [generatedFeasibleFifthSlotCatalogueLabel, griessShortIntegral, hc,
    generatedFeasibleFifthSlotPairIntegral]

/-- The sixth selected monomial permutation as an integer coordinate matrix. -/
def generatedFeasibleFifthSlotPermutationMatrix : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if generatedFifthMonomialSpatialForward 4 j = i then 1 else 0

/-- The actual permutation isometry acts by its literal integer coordinate matrix. -/
theorem generatedFeasibleFifthSlot_permutation_action (v : Fin 24 → ℝ) :
    (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation 4)).val v =
      generatedFeasibleFifthSlotPermutationMatrix.map (fun z => (z : ℝ) / ((1 : ℤ) : ℝ)) *ᵥ v := by
  funext i
  change v ((generatedFifthMonomialSpatialPermutation 4).val.symm i) = _
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
    generatedFeasibleFifthSlotPermutationMatrix]
  rw [Finset.sum_eq_single ((generatedFifthMonomialSpatialPermutation 4).val.symm i)]
  · rw [← generatedFifthMonomialSpatial_forward, Equiv.apply_symm_apply]
    simp
  · intro j _ hj
    rw [← generatedFifthMonomialSpatial_forward]
    have hne : (generatedFifthMonomialSpatialPermutation 4).val j ≠ i := by
      intro h
      apply hj
      rw [← h, Equiv.symm_apply_apply]
    simp [hne]
  · simp

/-- Seysen's ξ acts by its literal integer numerator divided by two. -/
theorem generatedFeasibleFifthSlot_xi_action (v : Fin 24 → ℝ) :
    co1XiIsometry.val v = co1XiNumerator.map (fun z => (z : ℝ) / ((2 : ℤ) : ℝ)) *ᵥ v := by
  change co1XiMatrix *ᵥ v = _
  congr 1
  ext i j
  simp [co1XiMatrix, co1XiMatrixQ]

/-- A certified integer equation determines the permutation image of a catalogue label. -/
theorem generatedFeasibleFifthSlot_permutation_label (k l : Fin 16) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1)
    (h : generatedFeasibleFifthSlotPermutationMatrix *ᵥ
        generatedFeasibleFifthSlotPairIntegral (generatedFeasibleFifthSlotCatalogueData k).1
          (generatedFeasibleFifthSlotCatalogueData k).2.1.1
          (generatedFeasibleFifthSlotCatalogueData k).2.1.2 =
      (1 * ε) • generatedFeasibleFifthSlotPairIntegral
        (generatedFeasibleFifthSlotCatalogueData l).1
        (generatedFeasibleFifthSlotCatalogueData l).2.1.1
        (generatedFeasibleFifthSlotCatalogueData l).2.1.2) :
    griessShortPermutation (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation 4))
      (generatedFeasibleFifthSlotCatalogueLabel k) = generatedFeasibleFifthSlotCatalogueLabel l :=
  generatedFeasibleFifthSlot_label_of_integral _ _ 1 (by norm_num)
    generatedFeasibleFifthSlot_permutation_action _ _ ε hε (by
      rw [generatedFeasibleFifthSlotCatalogue_integral,
        generatedFeasibleFifthSlotCatalogue_integral]
      exact h)

/-- A certified integer equation determines the ξ image of a catalogue label. -/
theorem generatedFeasibleFifthSlot_xi_label (k l : Fin 16) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : co1XiNumerator *ᵥ
        generatedFeasibleFifthSlotPairIntegral (generatedFeasibleFifthSlotCatalogueData k).1
          (generatedFeasibleFifthSlotCatalogueData k).2.1.1
          (generatedFeasibleFifthSlotCatalogueData k).2.1.2 =
      (2 * ε) • generatedFeasibleFifthSlotPairIntegral
        (generatedFeasibleFifthSlotCatalogueData l).1
        (generatedFeasibleFifthSlotCatalogueData l).2.1.1
        (generatedFeasibleFifthSlotCatalogueData l).2.1.2) :
    griessShortPermutation co1XiIsometry (generatedFeasibleFifthSlotCatalogueLabel k) =
      generatedFeasibleFifthSlotCatalogueLabel l :=
  generatedFeasibleFifthSlot_label_of_integral _ _ 2 (by norm_num)
    generatedFeasibleFifthSlot_xi_action _ _ ε hε (by
      rw [generatedFeasibleFifthSlotCatalogue_integral,
        generatedFeasibleFifthSlotCatalogue_integral]
      exact h)

/-- The selected permutation has a genuine whole-axis lift fixing the fifth axis. -/
theorem generatedFeasibleFifthSlot_permutation_lift : ∃ h : H,
    h ∈ generatedFifthLocalAxisStabilizer ∧ projH h = QuotientGroup.mk' signsSubgroup
      (golayPermutationIsometry (generatedFifthMonomialSpatialPermutation 4)) := by
  obtain ⟨h, hh⟩ := generatedFifthProjectedAxisStabilizer_permutation_mem 4
  exact ⟨h.val, h.property, hh⟩

/-- Seysen's ξ has a genuine whole-axis lift fixing the fifth axis. -/
theorem generatedFeasibleFifthSlot_xi_lift : ∃ h : H,
    h ∈ generatedFifthLocalAxisStabilizer ∧
      projH h = QuotientGroup.mk' signsSubgroup co1XiIsometry := by
  obtain ⟨h, hh⟩ := generatedFifthProjectedAxisStabilizer_xi_mem
  exact ⟨h.val, h.property, hh⟩

/-- The label of a local image of a signed-short axis is read from the Conway projection. -/
theorem generatedFeasibleFifthSlot_label_projection (h : H) (L : GriessShortIndex)
    (c : ZMod 2) : ∃ c' : ZMod 2,
      rhoLocal h (conwayShortAxis L c) = conwayShortAxis (co1ShortPermutation (projH h) L) c' := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  refine ⟨localShortPhase f L + c, ?_⟩
  rw [← hf, generatedFeasibleFifthSlot_local_image, localAxis_projection_short_mk]

/-- Catalogue labels reached from the slot axis by genuine fifth-axis fixers. -/
def generatedFeasibleFifthSlotReached (k : Fin 16) : Prop :=
  ∃ h : H, h ∈ generatedFifthLocalAxisStabilizer ∧ ∃ c : ZMod 2,
    rhoLocal h generatedFeasibleFifthSlotFirstAxis =
      conwayShortAxis (generatedFeasibleFifthSlotCatalogueLabel k) c

/-- The slot label itself is reached by the identity. -/
theorem generatedFeasibleFifthSlotReached_zero : generatedFeasibleFifthSlotReached 0 := by
  refine ⟨1, one_mem _, 0, ?_⟩
  rw [map_one]
  rfl

/-- A genuine lifted generator carries a reached label to its certified image. -/
theorem generatedFeasibleFifthSlotReached_step {k l : Fin 16} (g : leechIsomSubgroup)
    (hg : ∃ h : H, h ∈ generatedFifthLocalAxisStabilizer ∧
      projH h = QuotientGroup.mk' signsSubgroup g)
    (hlabel : griessShortPermutation g (generatedFeasibleFifthSlotCatalogueLabel k) =
      generatedFeasibleFifthSlotCatalogueLabel l)
    (hk : generatedFeasibleFifthSlotReached k) : generatedFeasibleFifthSlotReached l := by
  obtain ⟨h, hh, c, hc⟩ := hk
  obtain ⟨u, hu, hpu⟩ := hg
  obtain ⟨c', hc'⟩ := generatedFeasibleFifthSlot_label_projection u
    (generatedFeasibleFifthSlotCatalogueLabel k) c
  refine ⟨u * h, mul_mem hu hh, c', ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, hc, hc', hpu, QuotientGroup.mk'_apply,
    co1ShortPermutation_mk, hlabel]

set_option maxHeartbeats 4000000 in
-- Fifteen certified integer label transports along an explicit spanning tree.
/-- Every catalogue label is reached by a genuine fifth-axis fixer. -/
theorem generatedFeasibleFifthSlotReached_all (k : Fin 16) :
    generatedFeasibleFifthSlotReached k := by
  have p := generatedFeasibleFifthSlot_permutation_lift
  have x := generatedFeasibleFifthSlot_xi_lift
  have r0 := generatedFeasibleFifthSlotReached_zero
  have r10 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 0 10 (-1) (Or.inr rfl) (by decide)) r0
  have r1 := generatedFeasibleFifthSlotReached_step _ x
    (generatedFeasibleFifthSlot_xi_label 0 1 (-1) (Or.inr rfl) (by decide)) r0
  have r4 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 10 4 1 (Or.inl rfl) (by decide)) r10
  have r11 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 1 11 1 (Or.inl rfl) (by decide)) r1
  have r3 := generatedFeasibleFifthSlotReached_step _ x
    (generatedFeasibleFifthSlot_xi_label 1 3 (-1) (Or.inr rfl) (by decide)) r1
  have r6 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 4 6 1 (Or.inl rfl) (by decide)) r4
  have r5 := generatedFeasibleFifthSlotReached_step _ x
    (generatedFeasibleFifthSlot_xi_label 4 5 (-1) (Or.inr rfl) (by decide)) r4
  have r8 := generatedFeasibleFifthSlotReached_step _ x
    (generatedFeasibleFifthSlot_xi_label 11 8 1 (Or.inl rfl) (by decide)) r11
  have r12 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 6 12 1 (Or.inl rfl) (by decide)) r6
  have r7 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 5 7 1 (Or.inl rfl) (by decide)) r5
  have r14 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 8 14 (-1) (Or.inr rfl) (by decide)) r8
  have r9 := generatedFeasibleFifthSlotReached_step _ x
    (generatedFeasibleFifthSlot_xi_label 8 9 (-1) (Or.inr rfl) (by decide)) r8
  have r2 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 12 2 1 (Or.inl rfl) (by decide)) r12
  have r13 := generatedFeasibleFifthSlotReached_step _ x
    (generatedFeasibleFifthSlot_xi_label 12 13 (-1) (Or.inr rfl) (by decide)) r12
  have r15 := generatedFeasibleFifthSlotReached_step _ p
    (generatedFeasibleFifthSlot_permutation_label 9 15 1 (Or.inl rfl) (by decide)) r9
  fin_cases k <;> assumption

/-- Attainment: every catalogue axis lies in the actual fifth-axis stabilizer orbit of the slot
axis. Its phase is forced by the coverage theorem. -/
theorem generatedFeasibleFifthSlot_catalogue_attained (k : Fin 16) :
    generatedFeasibleFifthSlotCatalogueAxis k ∈
      MulAction.orbit generatedFifthLocalAxisStabilizer generatedFeasibleFifthSlotFirstAxis := by
  obtain ⟨h, hh, c, hc⟩ := generatedFeasibleFifthSlotReached_all k
  obtain ⟨k', hk'⟩ := generatedFeasibleFifthSlot_orbit_subset ⟨⟨h, hh⟩, rfl⟩
  change generatedFeasibleFifthSlotCatalogueAxis k' =
    rhoLocal h generatedFeasibleFifthSlotFirstAxis at hk'
  rw [hc] at hk'
  have hp := @generatedAxis_signed_injective
    (generatedFeasibleFifthSlotCatalogueLabel k', (generatedFeasibleFifthSlotCatalogueData k').2.2)
    (generatedFeasibleFifthSlotCatalogueLabel k, c) hk'
  have hkk : k' = k := generatedFeasibleFifthSlotCatalogueLabel_injective (congrArg Prod.fst hp)
  subst hkk
  exact ⟨⟨h, hh⟩, hc.trans hk'.symm⟩

/-- The entire actual fifth-axis stabilizer orbit of the slot axis is the catalogue. -/
theorem generatedFeasibleFifthSlot_orbit_eq :
    MulAction.orbit generatedFifthLocalAxisStabilizer generatedFeasibleFifthSlotFirstAxis =
      Set.range generatedFeasibleFifthSlotCatalogueAxis := by
  apply Set.Subset.antisymm generatedFeasibleFifthSlot_orbit_subset
  rintro _ ⟨k, rfl⟩
  exact generatedFeasibleFifthSlot_catalogue_attained k

/-- The actual fifth-axis stabilizer orbit of the slot axis has exactly sixteen vectors. -/
theorem generatedFeasibleFifthSlot_orbit_card :
    Nat.card (MulAction.orbit generatedFifthLocalAxisStabilizer
      generatedFeasibleFifthSlotFirstAxis) = 16 := by
  rw [generatedFeasibleFifthSlot_orbit_eq, generatedFeasibleFifthSlotCatalogue_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
