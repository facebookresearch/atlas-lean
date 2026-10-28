/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroSupportTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenInputRecognition

/-! A complete physical cache of preferred short roots external to the containing source. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- All external pair phases and all disjoint octad signs, with actual support addresses. -/
abbrev GeneratedFeasibleContainingZeroCachedLabel :=
  (Fin 2 × Fin 120) ⊕ (Fin 30 × Fin 64)

/-- The actual octad at a certified original disjoint-support address. -/
def generatedFeasibleContainingZeroCachedOctad (j : Fin 30) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedFeasibleContainingZeroOctadNode j,
      (Finset.mem_filter.mp (generatedFeasibleContainingZeroOctadNode_mem j)).1⟩

/-- This actual octad retains its original encoder label exactly. -/
theorem generatedFeasibleContainingZeroCachedOctad_label (j : Fin 30) :
    golayOctadLabel (generatedFeasibleContainingZeroCachedOctad j) =
      generatedFeasibleContainingZeroOctadNode j :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply _)

/-- Actual increasing physical coordinates of all thirty disjoint octads. -/
def generatedFeasibleContainingZeroCachedOctadCoordinate : Fin 30 → Fin 8 → Fin 24 :=
  ![![8, 9, 10, 11, 12, 13, 14, 15],
  ![10, 11, 12, 13, 18, 19, 20, 21],
  ![12, 13, 14, 15, 20, 21, 22, 23],
  ![9, 10, 12, 15, 16, 19, 21, 22],
  ![8, 11, 13, 14, 17, 18, 20, 23],
  ![8, 11, 13, 14, 16, 19, 21, 22],
  ![12, 13, 14, 15, 16, 17, 18, 19],
  ![8, 9, 12, 13, 16, 17, 20, 21],
  ![9, 11, 13, 15, 16, 18, 20, 22],
  ![10, 11, 14, 15, 18, 19, 22, 23],
  ![8, 10, 12, 14, 17, 19, 21, 23],
  ![8, 9, 10, 11, 16, 17, 18, 19],
  ![9, 11, 12, 14, 16, 18, 21, 23],
  ![9, 11, 13, 15, 17, 19, 21, 23],
  ![16, 17, 18, 19, 20, 21, 22, 23],
  ![9, 10, 13, 14, 17, 18, 21, 22],
  ![8, 10, 13, 15, 17, 19, 20, 22],
  ![8, 9, 14, 15, 16, 17, 22, 23],
  ![8, 11, 12, 15, 16, 19, 20, 23],
  ![9, 10, 12, 15, 17, 18, 20, 23],
  ![8, 9, 10, 11, 20, 21, 22, 23],
  ![10, 11, 14, 15, 16, 17, 20, 21],
  ![8, 9, 12, 13, 18, 19, 22, 23],
  ![9, 10, 13, 14, 16, 19, 20, 23],
  ![8, 10, 12, 14, 16, 18, 20, 22],
  ![10, 11, 12, 13, 16, 17, 22, 23],
  ![8, 9, 14, 15, 18, 19, 20, 21],
  ![9, 11, 12, 14, 17, 19, 20, 22],
  ![8, 11, 12, 15, 17, 18, 21, 22],
  ![8, 10, 13, 15, 16, 18, 21, 23]]

/-- Bind every cached physical coordinate to the entire actual octad catalogue. -/
theorem generatedFeasibleContainingZeroCachedOctadCoordinate_actual :
    ∀ j : Fin 30, ∀ k : Fin 8,
      golayOctadCoordinate (generatedFeasibleContainingZeroCachedOctad j) k =
        generatedFeasibleContainingZeroCachedOctadCoordinate j k := by
  intro j k
  let t := golayMaskSupport
    (golayEncodedMask (golayOctadLabel (generatedFeasibleContainingZeroCachedOctad j)).val)
  let e := t.orderIsoOfFin (golayOctad_support_card (generatedFeasibleContainingZeroCachedOctad j))
  have hm : (golayEncodedMask (generatedFeasibleContainingZeroOctadNode j).val).testBit
      (generatedFeasibleContainingZeroCachedOctadCoordinate j k).val = true := by
    have hc : ∀ j' : Fin 30, ∀ k' : Fin 8,
        (golayEncodedMask (generatedFeasibleContainingZeroOctadNode j').val).testBit
          (generatedFeasibleContainingZeroCachedOctadCoordinate j' k').val = true := by decide +kernel
    exact hc j k
  let v : t := ⟨generatedFeasibleContainingZeroCachedOctadCoordinate j k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedFeasibleContainingZeroCachedOctad_label]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel (generatedFeasibleContainingZeroCachedOctad j)).val)).sort.idxOf
        (generatedFeasibleContainingZeroCachedOctadCoordinate j k) = k.val
    rw [generatedFeasibleContainingZeroCachedOctad_label]
    have hs : (golayMaskSupport (golayEncodedMask (generatedFeasibleContainingZeroOctadNode j).val)).sort =
        List.ofFn (generatedFeasibleContainingZeroCachedOctadCoordinate j) := by
      have hsorted : ∀ j' : Fin 30,
          List.SortedLT (List.ofFn (generatedFeasibleContainingZeroCachedOctadCoordinate j')) := by
        decide +kernel
      apply ((golayMaskSupport
        (golayEncodedMask (generatedFeasibleContainingZeroOctadNode j).val)).sortedLT_sort).eq_of_mem_iff
          (hsorted j)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j' : Fin 30, ∀ i' : Fin 24,
          i' ∈ golayMaskSupport (golayEncodedMask (generatedFeasibleContainingZeroOctadNode j').val) ↔
            i' ∈ List.ofFn (generatedFeasibleContainingZeroCachedOctadCoordinate j') := by decide +kernel
      exact hc j i
    rw [hs]
    have hc : ∀ j' : Fin 30, ∀ k' : Fin 8,
        (List.ofFn (generatedFeasibleContainingZeroCachedOctadCoordinate j')).idxOf
          (generatedFeasibleContainingZeroCachedOctadCoordinate j' k') = k'.val := by decide +kernel
    exact hc j k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The original even sign pattern is evaluated in its actual physical coordinates. -/
def generatedFeasibleContainingZeroCachedSignMask (j : Fin 30) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFeasibleContainingZeroCachedOctadCoordinate j k).val else 0) ||| m) 0

/-- The cached sign mask is exactly the original preferred octad sign mask. -/
theorem generatedFeasibleContainingZeroCachedSignMask_actual (j : Fin 30) (e : Fin 64) :
    generatedFeasibleContainingZeroCachedSignMask j e =
      griessOctadSignMask (generatedFeasibleContainingZeroCachedOctad j) e := by
  simp only [generatedFeasibleContainingZeroCachedSignMask, griessOctadSignMask,
    generatedFeasibleContainingZeroCachedOctadCoordinate_actual]

/-- Every cache label is bound to an actual original preferred short label. -/
def generatedFeasibleContainingZeroCachedIndex :
    GeneratedFeasibleContainingZeroCachedLabel → GriessShortIndex
  | Sum.inl (s, n) =>
    Sum.inl (s, griessPairIndex (generatedFeasibleContainingZeroPairNode n).1
      (generatedFeasibleContainingZeroPairNode n).2
      (ne_of_lt (Finset.mem_filter.mp (generatedFeasibleContainingZeroPairNode_mem n)).2.1))
  | Sum.inr (j, e) => Sum.inr (Sum.inl (generatedFeasibleContainingZeroCachedOctad j, e))

/-- Full actual integral coordinates of a cache label. -/
def generatedFeasibleContainingZeroCachedIntegral :
    GeneratedFeasibleContainingZeroCachedLabel → Fin 24 → ℤ
  | Sum.inl (s, n) => fun i =>
    4 * (if i = (generatedFeasibleContainingZeroPairNode n).1 then 1 else 0) +
      (if s = 0 then -4 else 4) *
        (if i = (generatedFeasibleContainingZeroPairNode n).2 then 1 else 0)
  | Sum.inr (j, e) => fun i =>
    if (golayEncodedMask (generatedFeasibleContainingZeroOctadNode j).val).testBit i.val then
      if (generatedFeasibleContainingZeroCachedSignMask j e).testBit i.val then -2 else 2
    else 0

/-- The cache gives the entire actual integral short vector, with no missing coordinates. -/
theorem generatedFeasibleContainingZeroCachedIntegral_actual
    (r : GeneratedFeasibleContainingZeroCachedLabel) :
    generatedFeasibleContainingZeroCachedIntegral r =
      griessShortIntegral (generatedFeasibleContainingZeroCachedIndex r) := by
  rcases r with ⟨s, n⟩ | ⟨j, e⟩
  · have hn : (generatedFeasibleContainingZeroPairNode n).1 <
        (generatedFeasibleContainingZeroPairNode n).2 :=
      (Finset.mem_filter.mp (generatedFeasibleContainingZeroPairNode_mem n)).2.1
    simp only [generatedFeasibleContainingZeroCachedIntegral,
      generatedFeasibleContainingZeroCachedIndex, griessShortIntegral, griessPairIndex_coordinates,
      hn, ite_true]
  · simp only [generatedFeasibleContainingZeroCachedIntegral,
      generatedFeasibleContainingZeroCachedIndex, griessShortIntegral,
      generatedFeasibleContainingZeroCachedOctad_label,
      generatedFeasibleContainingZeroCachedSignMask_actual]

/-- Distinct cache addresses are distinct actual preferred roots. -/
theorem generatedFeasibleContainingZeroCachedIndex_injective :
    Function.Injective generatedFeasibleContainingZeroCachedIndex := by
  intro r s h
  rcases r with ⟨a, n⟩ | ⟨j, e⟩ <;> rcases s with ⟨b, m⟩ | ⟨k, f⟩
  · simp only [generatedFeasibleContainingZeroCachedIndex, Sum.inl.injEq, Prod.mk.injEq] at h
    have hp := congrArg griessCoordinatePair h.2
    have hn : (generatedFeasibleContainingZeroPairNode n).1 <
        (generatedFeasibleContainingZeroPairNode n).2 :=
      (Finset.mem_filter.mp (generatedFeasibleContainingZeroPairNode_mem n)).2.1
    have hm : (generatedFeasibleContainingZeroPairNode m).1 <
        (generatedFeasibleContainingZeroPairNode m).2 :=
      (Finset.mem_filter.mp (generatedFeasibleContainingZeroPairNode_mem m)).2.1
    rw [griessPairIndex_coordinates, griessPairIndex_coordinates,
      ite_eq_left hn, ite_eq_left hm] at hp
    exact congrArg Sum.inl (Prod.ext h.1 (generatedFeasibleContainingZeroPairNode_injective hp))
  · simp [generatedFeasibleContainingZeroCachedIndex] at h
  · simp [generatedFeasibleContainingZeroCachedIndex] at h
  · simp only [generatedFeasibleContainingZeroCachedIndex, Sum.inr.injEq,
      Sum.inl.injEq, Prod.mk.injEq] at h
    have hc := congrArg golayOctadLabel h.1
    rw [generatedFeasibleContainingZeroCachedOctad_label,
      generatedFeasibleContainingZeroCachedOctad_label] at hc
    exact congrArg Sum.inr (Prod.ext (generatedFeasibleContainingZeroOctadNode_injective hc) h.2)

/-- Every cache vector vanishes on all eight actual source coordinates. -/
theorem generatedFeasibleContainingZeroCachedIntegral_source_zero :
    ∀ r : GeneratedFeasibleContainingZeroCachedLabel, ∀ i : Fin 8,
      generatedFeasibleContainingZeroCachedIntegral r (Fin.castAdd 16 i) = 0 := by
  decide +kernel

/-- Every cache address belongs to the genuine selected-zero short catalogue. -/
theorem generatedFeasibleContainingZeroCachedIndex_mem
    (r : GeneratedFeasibleContainingZeroCachedLabel) :
    generatedFeasibleContainingZeroCachedIndex r ∈ generatedFeasibleContainingSelectedShortLabels 0 := by
  refine Finset.mem_filter.mpr ⟨(generatedFeasibleOrthogonalShortLabels_mem _).mpr ?_, ?_⟩
  · have h0 := generatedFeasibleContainingZeroCachedIntegral_source_zero r 0
    have h1 := generatedFeasibleContainingZeroCachedIntegral_source_zero r 1
    rw [generatedFeasibleContainingZeroCachedIntegral_actual] at h0 h1
    simpa using h0.trans h1.symm
  · change generatedFeasibleContainingSelectedShortSquare
      (generatedFeasibleContainingZeroCachedIndex r) = 0
    unfold generatedFeasibleContainingSelectedShortSquare
      generatedFeasibleContainingSelectedSquare
    rw [generatedFeasibleContaining_selected_source_word]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val < 8
    · let j : Fin 8 := ⟨i.val, hi⟩
      have h := generatedFeasibleContainingZeroCachedIntegral_source_zero r j
      have hj : Fin.castAdd 16 j = i := Fin.ext rfl
      rw [hj, generatedFeasibleContainingZeroCachedIntegral_actual] at h
      simp [h]
    · simp [golayStandardOctad, hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
