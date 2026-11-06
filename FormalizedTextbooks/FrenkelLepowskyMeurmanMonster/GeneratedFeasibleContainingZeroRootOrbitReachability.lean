/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroRootOrbitAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroSourceQPhaseFlip

/-! Complete genuine spatial and signed whole-axis transport of all selected-zero inputs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem source_mul (g h : leechIsomSubgroup)
    (hg : generatedAxisE8ImageSection g
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex))
    (hh : generatedAxisE8ImageSection h
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)) :
    generatedAxisE8ImageSection (g * h)
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
        generatedAxisE8CoordinateSection (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) := by
  apply generatedAxisE8_preserving_image
  intro u
  rw [map_mul, LinearEquiv.mul_apply]
  exact (generatedAxisE8_preserves_of_image_eq _ g hg _).trans
    (generatedAxisE8_preserves_of_image_eq _ h hh u)

private theorem node_transport (n : Fin 2160) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
          generatedAxisE8CoordinateSection (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
      leechIntegralAction g
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
      griessShortPermutation g generatedFeasibleContainingZeroShortLabel =
        generatedFeasibleContainingZeroCachedIndex (generatedFeasibleContainingZeroRootNode n) := by
  have all : ∀ m : ℕ, ∀ n : Fin 2160, n.val = m →
      ∃ g : leechIsomSubgroup,
        generatedAxisE8ImageSection g
          (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
            generatedAxisE8CoordinateSection (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
        leechIntegralAction g
          (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
            griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
        griessShortPermutation g generatedFeasibleContainingZeroShortLabel =
          generatedFeasibleContainingZeroCachedIndex (generatedFeasibleContainingZeroRootNode n) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro n hm
      by_cases hn : n = 0
      · subst n
        refine ⟨1, ?_, ?_, ?_⟩
        · apply generatedAxisE8_preserving_image
          intro u
          rw [map_one]
          rfl
        · rw [map_one]
          rfl
        · rw [map_one]
          rfl
      · obtain ⟨g, hgS, hgP, hgR⟩ := ih _ (by
          rw [← hm]
          exact generatedFeasibleContainingZeroRootParent_lt n hn)
          (generatedFeasibleContainingZeroRootParent n) rfl
        let k := generatedFeasibleContainingZeroRootGenerator (generatedFeasibleContainingZeroRootLetter n)
        refine ⟨k * g, source_mul k g
          (generatedFeasibleContainingZeroRootGenerator_section _) hgS, ?_, ?_⟩
        · rw [map_mul, LinearEquiv.mul_apply, hgP]
          exact generatedFeasibleContainingZeroRootGenerator_first _
        · rw [map_mul]
          change griessShortPermutation k
            (griessShortPermutation g generatedFeasibleContainingZeroShortLabel) = _
          rw [hgR]
          exact generatedFeasibleContainingZeroRoot_edge_actual n hn
  exact all n.val n rfl

private theorem nodes_cover {α : Type*} {n : ℕ}
    (s : Finset α) (f : Fin n → α) (hf : Function.Injective f)
    (hm : ∀ i, f i ∈ s) (hc : s.card = n) (x : α) (hx : x ∈ s) :
    ∃ i, f i = x := by
  classical
  let t := Finset.univ.map ⟨f, hf⟩
  have hsub : t ⊆ s := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
    exact hm i
  have he : t = s := Finset.eq_of_subset_of_card_le hsub (by simp [t, hc])
  have ht : x ∈ t := by rw [he]; exact hx
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ht
  exact ⟨i, hi⟩

/-- Every actual selected-zero root is present in the full genuine original-word transport tree. -/
theorem generatedFeasibleContainingZeroRootNode_cover (r : GriessShortIndex)
    (hr : generatedFeasibleContainingSelectedShortSquare r = 0) :
    ∃ n : Fin 2160,
      generatedFeasibleContainingZeroCachedIndex (generatedFeasibleContainingZeroRootNode n) = r := by
  apply nodes_cover (generatedFeasibleContainingSelectedShortLabels 0)
    (fun n => generatedFeasibleContainingZeroCachedIndex (generatedFeasibleContainingZeroRootNode n))
    (generatedFeasibleContainingZeroCachedIndex_injective.comp
      generatedFeasibleContainingZeroRootNode_injective)
    (fun n => generatedFeasibleContainingZeroCachedIndex_mem _)
    (by simpa using generatedFeasibleContainingSelectedShortLabels_card 0)
  refine Finset.mem_filter.mpr ⟨(generatedFeasibleOrthogonalShortLabels_mem r).mpr ?_, hr⟩
  exact (generatedFeasibleContaining_selected_zero_coordinates r hr 0 (by decide)).trans
    (generatedFeasibleContaining_selected_zero_coordinates r hr 1 (by decide)).symm

/-- All original selected-zero preferred roots reach the same anchor while fixing the entire
source section and the actual positive first root. -/
theorem generatedFeasibleContaining_selected_zero_spatial_transport
    (r : GriessShortIndex) (hr : generatedFeasibleContainingSelectedShortSquare r = 0) :
    ∃ g : leechIsomSubgroup,
      generatedAxisE8ImageSection g
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) =
          generatedAxisE8CoordinateSection (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) ∧
      leechIntegralAction g
        (griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) =
          griessShortLatticeVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)) ∧
      griessShortPermutation g r = generatedFeasibleContainingZeroShortLabel := by
  obtain ⟨n, hn⟩ := generatedFeasibleContainingZeroRootNode_cover r hr
  obtain ⟨g, hgS, hgP, hgR⟩ := node_transport n
  rw [hn] at hgR
  refine ⟨g⁻¹, ?_, ?_, ?_⟩
  · exact generatedAxisE8_preserving_image _ _
      (generatedAxisE8_preserves_inv _ _ (generatedAxisE8_preserves_of_image_eq _ _ hgS))
  · apply (leechIntegralAction g).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact hgP.symm
  · rw [map_inv]
    change (griessShortPermutation g).symm r = _
    rw [← hgR, Equiv.symm_apply_apply]

/-- Every genuine signed zero input reaches either specified anchor phase under an actual
whole-containing-axis fixer in the entire positive first-axis stabilizer. -/
theorem generatedFeasibleContaining_selected_zero_signed_transport
    (r : GriessShortIndex) (c d : ZMod 2)
    (hr : generatedFeasibleContainingSelectedShortSquare r = 0) :
    ∃ u : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      rhoLocal u.val generatedFeasibleContainingOctadDestination =
        generatedFeasibleContainingOctadDestination ∧
      rhoLocal u.val (conwayShortAxis r c) =
        conwayShortAxis generatedFeasibleContainingZeroShortLabel d := by
  obtain ⟨g, hgS, hgP, hgR⟩ := generatedFeasibleContaining_selected_zero_spatial_transport r hr
  have hgP' : griessShortPermutation g (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
      Sum.inl (0, generatedFeasiblePhysicalRootPair) :=
    (leechRootedA2_short_perm_eq_iff _ _ _).mpr (Or.inl hgP)
  obtain ⟨f, hf, hfirst, hsource⟩ :=
    generatedFeasibleContaining_source_flag_whole_lift g hgS hgP'
  let u : localAxisStabilizer generatedFeasiblePhysicalRootPair := ⟨localFiberIntoH f, hfirst⟩
  let b := localShortPhase f r + c
  have huR : rhoLocal u.val (conwayShortAxis r c) =
      conwayShortAxis generatedFeasibleContainingZeroShortLabel b := by
    change localGriessRepresentation f _ = _
    rw [generatedAxis_localFiber_image, hf, hgR]
  by_cases hb : b = d
  · exact ⟨u, hsource, hb ▸ huR⟩
  · have hphase : 1 + b = d := by
      have h : ∀ b d : ZMod 2, b ≠ d → 1 + b = d := by decide +kernel
      exact h b d hb
    refine ⟨generatedFeasibleContainingZeroPhaseWord * u, ?_, ?_⟩
    · change rhoLocal (generatedFeasibleContainingZeroPhaseWord.val * u.val) _ = _
      rw [map_mul, LinearEquiv.mul_apply, hsource,
        generatedFeasibleContainingZeroPhaseWord_source]
    · change rhoLocal (generatedFeasibleContainingZeroPhaseWord.val * u.val) _ = _
      rw [map_mul, LinearEquiv.mul_apply, huR,
        generatedFeasibleContainingZeroPhaseWord_anchor, hphase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
