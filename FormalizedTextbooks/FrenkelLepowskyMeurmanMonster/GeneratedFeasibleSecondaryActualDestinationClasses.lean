/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryDestinationSeparation

/-! Exactly five genuine A destinations on the complete original secondary input orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Five actual A classes reached from the secondary orbit, using original source vectors. -/
def generatedFeasibleSecondaryActualDestinations : Fin 5 →
    generatedFeasibleLocalOrbitSpace generatedFeasiblePhysicalRootPair :=
  ![generatedFeasibleSecondaryAClass
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1),
    generatedFeasibleSecondaryAClass
      (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair),
    generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination,
    generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination,
    generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination]

/-- The five actual destination classes are pairwise distinct under the entire A action. -/
theorem generatedFeasibleSecondaryActualDestinations_injective :
    Function.Injective generatedFeasibleSecondaryActualDestinations := by
  have h01 := generatedFeasibleAnchorSecondaryDestination_separate
  have h02 := generatedFeasibleOctadSignedDestination_separate
    generatedFeasibleContainingOctadPrototypeIndex
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1
  have h03 := generatedFeasibleOctadSignedDestination_separate
    generatedFeasibleOutsideOctadPrototypeIndex
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1
  have h04 := generatedFeasibleOddSignedDestination_separate
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1
  have h12 := generatedFeasibleOctadSignedDestination_separate
    generatedFeasibleContainingOctadPrototypeIndex
    (Sum.inl (1, generatedFeasiblePhysicalRootPair)) 1
  have h13 := generatedFeasibleOctadSignedDestination_separate
    generatedFeasibleOutsideOctadPrototypeIndex
    (Sum.inl (1, generatedFeasiblePhysicalRootPair)) 1
  have h14 := generatedFeasibleOddSignedDestination_separate
    (Sum.inl (1, generatedFeasiblePhysicalRootPair)) 1
  rw [← generatedFeasibleSecondaryAxis_eq_short] at h12 h13 h14
  change generatedFeasibleSecondaryAClass
    (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) ≠
      generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination at h02
  change generatedFeasibleSecondaryAClass
    (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) ≠
      generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination at h03
  change generatedFeasibleSecondaryAClass
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) ≠
      generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination at h12
  change generatedFeasibleSecondaryAClass
    (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) ≠
      generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination at h13
  have h23 := generatedFeasibleContainingOutsideDestination_separate
  have h24 := generatedFeasibleOctadOddDestination_separate
    generatedFeasibleContainingOctadPrototypeIndex
  have h34 := generatedFeasibleOctadOddDestination_separate
    generatedFeasibleOutsideOctadPrototypeIndex
  change generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination ≠
    generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination at h24
  change generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination ≠
    generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination at h34
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [generatedFeasibleSecondaryActualDestinations]

/-- The proved six N sectors merge into five A destinations only in the two pair returns. -/
def generatedFeasibleSecondaryNActualDestinationIndex : Fin 6 → Fin 5 := ![0, 1, 1, 2, 3, 4]

/-- Every source prototype's actual triality image has its indicated genuine A class. -/
theorem generatedFeasibleSecondaryNPrototype_actual_destination (k : Fin 6) :
    generatedFeasibleSecondaryAClass (sExtra (generatedFeasibleSecondaryNPrototype k)) =
      generatedFeasibleSecondaryActualDestinations
        (generatedFeasibleSecondaryNActualDestinationIndex k) := by
  fin_cases k
  · change generatedFeasibleSecondaryAClass (generatedFeasibleMateDestination 0) = _
    rw [generatedFeasibleMateDestination_zero]
    rfl
  · change generatedFeasibleSecondaryAClass (generatedFeasibleMateDestination 1) =
      generatedFeasibleSecondaryAClass
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
    obtain ⟨h, hh⟩ := generatedFeasibleMateDestination_one_mem
    exact (generatedFeasibleSecondaryAClass_eq_iff _ _).mpr ⟨h⁻¹, by
      change rhoLocal h.val⁻¹ (generatedFeasibleMateDestination 1) = _
      rw [← hh, map_inv]
      exact (rhoLocal h.val).symm_apply_apply _⟩
  · change generatedFeasibleSecondaryAClass generatedFeasibleDisjointPairDestination =
      generatedFeasibleSecondaryAClass
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
    obtain ⟨h, hh⟩ := generatedFeasibleDisjointPairDestination_mem
    exact (generatedFeasibleSecondaryAClass_eq_iff _ _).mpr ⟨h⁻¹, by
      change rhoLocal h.val⁻¹ generatedFeasibleDisjointPairDestination = _
      rw [← hh, map_inv]
      exact (rhoLocal h.val).symm_apply_apply _⟩
  · rfl
  · rfl
  · rfl

/-- Actual N-equivalent secondary inputs have triality images in the same genuine A class. -/
theorem generatedFeasibleSecondaryNOrbit_actual_destination (k : Fin 6) (x : GriessSpace)
    (hx : x ∈ generatedFeasibleSecondaryNOrbit k) :
    generatedFeasibleSecondaryAClass (sExtra x) =
      generatedFeasibleSecondaryActualDestinations
        (generatedFeasibleSecondaryNActualDestinationIndex k) := by
  rw [generatedFeasibleSecondaryNOrbit_eq] at hx
  obtain ⟨n, hn⟩ := hx
  change rhoLocal n.val (generatedFeasibleSecondaryNPrototype k) = x at hn
  let n' : localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair :=
    ⟨⟨n.val, n.property.1⟩, n.property.2⟩
  obtain ⟨h, hh⟩ := localFeasibleTransition_triality_orbit _ n'
    (generatedFeasibleSecondaryNPrototype k)
  change rhoLocal h.val (sExtra (generatedFeasibleSecondaryNPrototype k)) =
    sExtra (rhoLocal n.val (generatedFeasibleSecondaryNPrototype k)) at hh
  rw [hn] at hh
  have he := (generatedFeasibleSecondaryAClass_eq_iff _ _).mpr ⟨h, hh⟩
  exact he.symm.trans (generatedFeasibleSecondaryNPrototype_actual_destination k)

/-- Every input in the entire actual secondary orbit reaches one of the five actual A classes. -/
theorem generatedFeasibleSecondaryActualDestinations_coverage (x : GriessSpace)
    (hx : x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair) :
    ∃ k : Fin 5, generatedFeasibleSecondaryAClass (sExtra x) =
      generatedFeasibleSecondaryActualDestinations k := by
  rw [generatedFeasibleSecondaryLocalOrbit_eq_physical] at hx
  obtain ⟨k, hk⟩ := (generatedFeasibleSecondaryNOrbit_coverage x).mp hx
  exact ⟨_, generatedFeasibleSecondaryNOrbit_actual_destination k x hk⟩

/-- Each of the five genuine A destination classes is reached by an original secondary input. -/
theorem generatedFeasibleSecondaryActualDestinations_reached (j : Fin 5) :
    ∃ x : GriessSpace,
      x ∈ generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair ∧
        generatedFeasibleSecondaryAClass (sExtra x) =
          generatedFeasibleSecondaryActualDestinations j := by
  let k : Fin 6 := ![0, 1, 3, 4, 5] j
  refine ⟨generatedFeasibleSecondaryNPrototype k,
    generatedFeasibleSecondaryNPrototype_mem k, ?_⟩
  rw [generatedFeasibleSecondaryNPrototype_actual_destination]
  have hk : generatedFeasibleSecondaryNActualDestinationIndex k = j := by
    fin_cases j <;> rfl
  rw [hk]

/-- The complete secondary transition image consists of exactly these five actual A classes. -/
theorem generatedFeasibleSecondaryActualDestinations_range :
    Set.range (fun x : generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair =>
      generatedFeasibleSecondaryAClass (sExtra x.val)) =
        Set.range generatedFeasibleSecondaryActualDestinations := by
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨j, hj⟩ := generatedFeasibleSecondaryActualDestinations_coverage x.val x.property
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨x, hx, he⟩ := generatedFeasibleSecondaryActualDestinations_reached j
    exact ⟨⟨x, hx⟩, he⟩

/-- There are exactly five genuine A classes among all secondary triality destinations. -/
theorem generatedFeasibleSecondaryActualDestinations_card :
    Nat.card (Set.range (fun x : generatedFeasibleSecondaryLocalOrbit
      generatedFeasiblePhysicalRootPair => generatedFeasibleSecondaryAClass (sExtra x.val))) =
        5 := by
  rw [generatedFeasibleSecondaryActualDestinations_range]
  rw [← Nat.card_congr (Equiv.ofInjective _
    generatedFeasibleSecondaryActualDestinations_injective)]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
