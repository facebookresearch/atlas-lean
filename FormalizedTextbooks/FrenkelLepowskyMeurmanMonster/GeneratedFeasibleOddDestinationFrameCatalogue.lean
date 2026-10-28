/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationSourceTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineMonomial

/-! Original preferred coordinate-pair lines orthogonal to the physical norm-eight frame. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The actual increasing coordinate pairs avoiding the physical frame coordinate zero. -/
def generatedFeasibleOddFramePairs : Finset (Fin 24 × Fin 24) :=
  Finset.univ.filter fun z => z.1 < z.2 ∧ z.1 ≠ 0 ∧ z.2 ≠ 0

/-- There are 253 increasing physical pairs outside the distinguished frame coordinate. -/
theorem generatedFeasibleOddFramePairs_card : generatedFeasibleOddFramePairs.card = 253 := by
  decide +kernel

/-- The actual preferred pair lines orthogonal to the distinguished physical frame. -/
def generatedFeasibleOddFrameShortLines : Set GriessShortIndex :=
  {r | ∃ s : Fin 2, ∃ p : Fin 276, r = Sum.inl (s, p) ∧
    griessCoordinatePair p ∈ generatedFeasibleOddFramePairs}

/-- Actual outside pair addresses are bound to the original canonical pair dictionary. -/
def generatedFeasibleOddFramePairIndex (z : generatedFeasibleOddFramePairs) : Fin 276 :=
  griessPairIndex z.val.1 z.val.2
    (ne_of_lt ((Finset.mem_filter.mp z.property).2.1))

/-- The dictionary index preserves precisely the increasing physical pair. -/
theorem generatedFeasibleOddFramePairIndex_coordinates (z : generatedFeasibleOddFramePairs) :
    griessCoordinatePair (generatedFeasibleOddFramePairIndex z) = z.val := by
  rw [generatedFeasibleOddFramePairIndex, griessPairIndex_coordinates]
  simp only [(Finset.mem_filter.mp z.property).2.1, ite_true]

/-- The physical addresses map into the original preferred-root catalogue. -/
def generatedFeasibleOddFrameCatalogueMap
    (z : Fin 2 × generatedFeasibleOddFramePairs) : generatedFeasibleOddFrameShortLines :=
  ⟨Sum.inl (z.1, generatedFeasibleOddFramePairIndex z.2),
    ⟨z.1, _, rfl, by rw [generatedFeasibleOddFramePairIndex_coordinates]; exact z.2.property⟩⟩

/-- Distinct physical addresses give distinct actual preferred roots. -/
theorem generatedFeasibleOddFrameCatalogueMap_bijective :
    Function.Bijective generatedFeasibleOddFrameCatalogueMap := by
  constructor
  · intro x y h
    have hh := Sum.inl_injective (congrArg Subtype.val h)
    apply Prod.ext
    · exact congrArg (fun z : Fin 2 × Fin 276 => z.1) hh
    · apply Subtype.ext
      have hp := congrArg (fun z : Fin 2 × Fin 276 => z.2) hh
      have hc := congrArg griessCoordinatePair hp
      rwa [generatedFeasibleOddFramePairIndex_coordinates,
        generatedFeasibleOddFramePairIndex_coordinates] at hc
  · intro r
    obtain ⟨s, p, hr, hp⟩ := r.property
    refine ⟨(s, ⟨griessCoordinatePair p, hp⟩), ?_⟩
    apply Subtype.ext
    change Sum.inl (s, generatedFeasibleOddFramePairIndex _) = r.val
    rw [hr]
    congr 2
    apply griessCoordinatePairEquiv.injective
    apply Subtype.ext
    exact generatedFeasibleOddFramePairIndex_coordinates _

/-- The two genuine sign families and 253 physical pairs parametrize the actual 506 lines. -/
def generatedFeasibleOddFrameCatalogueEquiv :
    Fin 2 × generatedFeasibleOddFramePairs ≃ generatedFeasibleOddFrameShortLines :=
  Equiv.ofBijective generatedFeasibleOddFrameCatalogueMap
    generatedFeasibleOddFrameCatalogueMap_bijective

/-- Exactly 506 original preferred root lines are orthogonal to the original frame. -/
theorem generatedFeasibleOddFrameShortLines_card :
    Nat.card generatedFeasibleOddFrameShortLines = 506 := by
  rw [← Nat.card_congr generatedFeasibleOddFrameCatalogueEquiv, Nat.card_prod,
    Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe, generatedFeasibleOddFramePairs_card]

/-- The genuine target first root belongs to this original frame-complement catalogue. -/
theorem generatedFeasibleOddFrame_target_mem :
    Sum.inl (0, generatedFeasibleOddDestinationPair) ∈ generatedFeasibleOddFrameShortLines := by
  refine ⟨0, _, rfl, ?_⟩
  rw [generatedFeasibleOddDestinationPair_coordinates]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
