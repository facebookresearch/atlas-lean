/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryPhysicalCoverage

/-! Three exact physical nonpair sectors of the actual secondary feasible orbit.
These source sectors are not assumed to be final feasible-axis classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original perpendicular octad addresses whose support lies in a specified actual catalogue. -/
def generatedFeasibleSecondaryOctadSubset (s : Finset (Fin 759)) :
    Finset (Fin 759 × Fin 64) :=
  Finset.univ.filter fun z => z.1 ∈ s ∧
    griessShortIntegral (Sum.inr (Sum.inl z)) 0 =
      griessShortIntegral (Sum.inr (Sum.inl z)) 1

private theorem octad_subset_card (s : Finset (Fin 759)) (n : ℕ)
    (h : ∀ o ∈ s, (Finset.univ.filter fun e : Fin 64 =>
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1).card = n) :
    (generatedFeasibleSecondaryOctadSubset s).card = s.card * n := by
  have hc : (generatedFeasibleSecondaryOctadSubset s).card =
      ∑ z : Fin 759 × Fin 64, if z.1 ∈ s ∧
        griessShortIntegral (Sum.inr (Sum.inl z)) 0 =
          griessShortIntegral (Sum.inr (Sum.inl z)) 1 then (1 : ℕ) else 0 := by
    simpa only [generatedFeasibleSecondaryOctadSubset, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun z : Fin 759 × Fin 64 => z.1 ∈ s ∧
        griessShortIntegral (Sum.inr (Sum.inl z)) 0 =
          griessShortIntegral (Sum.inr (Sum.inl z)) 1) Finset.univ).symm
  rw [hc, Fintype.sum_prod_type]
  have he (o : Fin 759) : (∑ e : Fin 64, if o ∈ s ∧
      griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
        griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1 then (1 : ℕ) else 0) =
      if o ∈ s then n else 0 := by
    by_cases ho : o ∈ s
    · simpa [ho, Finset.sum_boole] using h o ho
    · simp [ho]
  simp_rw [he]
  simp

/-- All three actual nonpair sectors, in their original preferred shortest-vector labels. -/
def generatedFeasibleSecondaryNonPairLabels : Fin 3 → Finset GriessShortIndex :=
  ![ (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadContainingLabels).map
      ⟨fun z => Sum.inr (Sum.inl z), by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)⟩,
     (generatedFeasibleSecondaryOctadSubset generatedFeasibleOctadOutsideLabels).map
      ⟨fun z => Sum.inr (Sum.inl z), by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)⟩,
     generatedFeasibleOrthogonalOddLabels.map
      ⟨fun z => Sum.inr (Sum.inr z), by intro a b h; exact Sum.inr_injective (Sum.inr_injective h)⟩]

/-- Both actual axis signs on each original nonpair physical line. -/
def generatedFeasibleSecondaryNonPairSignedLabels (k : Fin 3) :
    Finset (GriessShortIndex × ZMod 2) :=
  generatedFeasibleSecondaryNonPairLabels k ×ˢ Finset.univ

/-- Exact preferred-label cardinalities, derived from the genuine physical sign counts. -/
theorem generatedFeasibleSecondaryNonPairLabels_card (k : Fin 3) :
    (generatedFeasibleSecondaryNonPairLabels k).card = (![2464, 21120, 22528] : Fin 3 → ℕ) k := by
  fin_cases k
  · simp only [generatedFeasibleSecondaryNonPairLabels, Matrix.cons_val_zero', Finset.card_map]
    rw [
      octad_subset_card _ 32 generatedFeasibleOctadContaining_physical_count,
      generatedFeasibleOctadContainingLabels_card]
  · simp only [generatedFeasibleSecondaryNonPairLabels, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Finset.card_map]
    rw [
      octad_subset_card _ 64 generatedFeasibleOctadOutside_physical_count,
      generatedFeasibleOctadOutsideLabels_card]
  · simp only [generatedFeasibleSecondaryNonPairLabels, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Finset.card_map]
    rw [
      generatedFeasibleOrthogonalOddLabels_card]

/-- The genuine signed sectors have sizes 4928, 42240, 45056. -/
theorem generatedFeasibleSecondaryNonPairSignedLabels_card (k : Fin 3) :
    (generatedFeasibleSecondaryNonPairSignedLabels k).card =
      (![4928, 42240, 45056] : Fin 3 → ℕ) k := by
  rw [generatedFeasibleSecondaryNonPairSignedLabels, Finset.card_product,
    generatedFeasibleSecondaryNonPairLabels_card, Finset.card_univ]
  fin_cases k <;> norm_num [ZMod.card]

/-- Every nonpair preferred label belongs to the entire actual perpendicular catalogue. -/
theorem generatedFeasibleSecondaryNonPairLabels_subset (k : Fin 3) :
    generatedFeasibleSecondaryNonPairLabels k ⊆ generatedFeasibleOrthogonalShortLabels := by
  intro r hr
  fin_cases k <;> obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hr
  · rw [generatedFeasibleOrthogonalShortLabels_mem]
    exact (Finset.mem_filter.mp hz).2.2
  · rw [generatedFeasibleOrthogonalShortLabels_mem]
    exact (Finset.mem_filter.mp hz).2.2
  · change Sum.inr (Sum.inr z) ∈ generatedFeasibleOrthogonalShortLabels
    simpa only [generatedFeasibleOrthogonalShortLabels, Finset.inr_mem_disjSum] using hz

/-- Every actual perpendicular preferred label lies in the pair sector or one of the
three physical nonpair sectors. -/
theorem generatedFeasibleSecondary_catalogue_partition (r : GriessShortIndex) :
    r ∈ generatedFeasibleOrthogonalShortLabels ↔
      (∃ z ∈ generatedFeasibleOrthogonalPairLabels, Sum.inl z = r) ∨
        ∃ k : Fin 3, r ∈ generatedFeasibleSecondaryNonPairLabels k := by
  constructor
  · intro hr
    rcases r with z | z
    · exact Or.inl ⟨z, by simpa [generatedFeasibleOrthogonalShortLabels] using hr, rfl⟩
    · rcases z with ⟨o, e⟩ | z
      · have he : griessShortIntegral (Sum.inr (Sum.inl (o, e))) 0 =
            griessShortIntegral (Sum.inr (Sum.inl (o, e))) 1 :=
          (generatedFeasibleOrthogonalShortLabels_mem _).mp hr
        have hp : 0 < (Finset.univ.filter fun f : Fin 64 =>
            griessShortIntegral (Sum.inr (Sum.inl (o, f))) 0 =
              griessShortIntegral (Sum.inr (Sum.inl (o, f))) 1).card :=
          Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
        rw [generatedFeasibleOctad_physical_count] at hp
        by_cases hc : o ∈ generatedFeasibleOctadContainingLabels
        · refine Or.inr ⟨0, ?_⟩
          change _ ∈ (generatedFeasibleSecondaryOctadSubset _).map _
          exact Finset.mem_map.mpr ⟨(o, e),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc, he⟩, rfl⟩
        · have ho : o ∈ generatedFeasibleOctadOutsideLabels := by
            by_contra hn
            simp [hc, hn] at hp
          refine Or.inr ⟨1, ?_⟩
          change _ ∈ (generatedFeasibleSecondaryOctadSubset _).map _
          exact Finset.mem_map.mpr ⟨(o, e),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho, he⟩, rfl⟩
      · refine Or.inr ⟨2, ?_⟩
        change _ ∈ generatedFeasibleOrthogonalOddLabels.map _
        exact Finset.mem_map.mpr ⟨z,
          by simpa [generatedFeasibleOrthogonalShortLabels] using hr, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨k, hk⟩)
    · simpa [generatedFeasibleOrthogonalShortLabels] using hz
    · exact generatedFeasibleSecondaryNonPairLabels_subset k hk

/-- Every original signed nonpair input is in the genuine secondary feasible orbit. -/
theorem generatedFeasibleSecondaryNonPair_axis_mem (k : Fin 3)
    (r : GriessShortIndex) (hr : r ∈ generatedFeasibleSecondaryNonPairLabels k)
    (c : ZMod 2) :
    conwayShortAxis r c ∈
      generatedFeasibleSecondaryLocalOrbit generatedFeasiblePhysicalRootPair := by
  rw [generatedFeasibleSecondaryLocalOrbit_eq_physical]
  refine ⟨⟨(r, c), ?_⟩, rfl⟩
  exact Finset.mem_product.mpr
    ⟨generatedFeasibleSecondaryNonPairLabels_subset k hr, Finset.mem_univ _⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
