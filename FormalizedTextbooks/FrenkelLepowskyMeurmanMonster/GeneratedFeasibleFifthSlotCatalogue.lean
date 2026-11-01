/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleFifthSlotFeasibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthShortCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! Coverage for the orbit of the slot axis under the actual fifth-axis stabilizer.

Every actual H element fixing the counted fifth axis carries the slot axis
`4(e₁₂-e₁₃)`, phase 0, into a sixteen-element catalogue of actual signed pair axes. The proof
uses only the actual matrix watermark of the fifth axis (its octad quadratic form), its actual
short coefficients and the genuine local coordinate action; no orbit size is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
attribute [local irreducible] generatedFifthAxis

/-- Sixteen entries: sign family, increasing physical coordinate pair and binary phase. -/
def generatedFeasibleFifthSlotCatalogueData : Fin 16 → Fin 2 × (Fin 24 × Fin 24) × ZMod 2 :=
  ![(0, (12, 13), 0), (1, (12, 13), 1), (0, (14, 15), 1), (1, (14, 15), 0),
    (0, (4, 6), 1), (1, (4, 6), 0), (0, (5, 7), 0), (1, (5, 7), 1),
    (0, (8, 11), 1), (1, (8, 11), 0), (0, (9, 10), 0), (1, (9, 10), 1),
    (0, (20, 22), 0), (1, (20, 22), 1), (0, (21, 23), 1), (1, (21, 23), 0)]

/-- Every catalogue pair is an increasing physical coordinate pair. -/
theorem generatedFeasibleFifthSlotCatalogueData_mem (k : Fin 16) :
    (generatedFeasibleFifthSlotCatalogueData k).2.1 ∈ griessCoordinatePairs := by
  revert k
  decide

/-- The actual short label of a catalogue entry. -/
def generatedFeasibleFifthSlotCatalogueLabel (k : Fin 16) : GriessShortIndex :=
  Sum.inl ((generatedFeasibleFifthSlotCatalogueData k).1,
    griessCoordinatePairEquiv.symm ⟨_, generatedFeasibleFifthSlotCatalogueData_mem k⟩)

/-- The actual signed-short axis of a catalogue entry. -/
def generatedFeasibleFifthSlotCatalogueAxis (k : Fin 16) : GriessSpace :=
  conwayShortAxis (generatedFeasibleFifthSlotCatalogueLabel k)
    (generatedFeasibleFifthSlotCatalogueData k).2.2

/-- Distinct catalogue entries have distinct actual short labels. -/
theorem generatedFeasibleFifthSlotCatalogueLabel_injective :
    Function.Injective generatedFeasibleFifthSlotCatalogueLabel := by
  intro k l h
  simp only [generatedFeasibleFifthSlotCatalogueLabel, Sum.inl.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h3 := congrArg Subtype.val (griessCoordinatePairEquiv.symm.injective h2)
  have hall : ∀ k l : Fin 16, (generatedFeasibleFifthSlotCatalogueData k).1 =
      (generatedFeasibleFifthSlotCatalogueData l).1 →
      (generatedFeasibleFifthSlotCatalogueData k).2.1 =
        (generatedFeasibleFifthSlotCatalogueData l).2.1 → k = l := by
    decide
  exact hall k l h1 h3

/-- Distinct catalogue entries give distinct actual Griess vectors. -/
theorem generatedFeasibleFifthSlotCatalogueAxis_injective :
    Function.Injective generatedFeasibleFifthSlotCatalogueAxis := by
  intro k l h
  have hp := @generatedAxis_signed_injective
    (generatedFeasibleFifthSlotCatalogueLabel k, (generatedFeasibleFifthSlotCatalogueData k).2.2)
    (generatedFeasibleFifthSlotCatalogueLabel l, (generatedFeasibleFifthSlotCatalogueData l).2.2) h
  exact generatedFeasibleFifthSlotCatalogueLabel_injective (congrArg Prod.fst hp)

/-- The catalogue consists of exactly sixteen actual Griess vectors. -/
theorem generatedFeasibleFifthSlotCatalogue_card :
    Nat.card (Set.range generatedFeasibleFifthSlotCatalogueAxis) = 16 := by
  rw [← Nat.card_congr (Equiv.ofInjective _ generatedFeasibleFifthSlotCatalogueAxis_injective),
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The first catalogue entry is the slot axis itself. -/
theorem generatedFeasibleFifthSlotCatalogueAxis_zero :
    generatedFeasibleFifthSlotCatalogueAxis 0 = generatedFeasibleFifthSlotFirstAxis :=
  rfl

/-- The actual short coefficient of the fifth axis at the slot label is one quarter. -/
theorem generatedFeasibleFifthSlot_first_coefficient :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (0, generatedFeasibleFifthSlotPair)) =
      1 / 4 := by
  rw [generatedFifth_final_pair_numerator, generatedFeasibleFifthSlotPair_coordinates]
  have h : generatedFifthFinalPairNumerator 0 12 13 = 4 := by decide
  rw [h]
  norm_num

/-- A fiber fixing the fifth axis relates its short coefficients along its label permutation. -/
theorem generatedFeasibleFifthSlot_fixer_short (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedFifthAxis = generatedFifthAxis)
    (r : GriessShortIndex) :
    (griessConwayEncode generatedFifthAxis).2.1 (griessShortPermutation f.val.2 r) =
      qSign (localShortPhase f r) * (griessConwayEncode generatedFifthAxis).2.1 r := by
  have he : (griessConwayEncode (rhoLocal (localFiberIntoH f) generatedFifthAxis)).2.1
      (griessShortPermutation f.val.2 r) =
      (griessConwayEncode generatedFifthAxis).2.1 (griessShortPermutation f.val.2 r) :=
    congrArg (fun x : GriessSpace =>
      (griessConwayEncode x).2.1 (griessShortPermutation f.val.2 r)) hf
  rw [generatedFourth_local_short, localShortOperator_image] at he
  exact he.symm

/-- The integral octad-weighted quadratic invariant of the fifth matrix watermark. -/
def generatedFeasibleFifthSlotQuadratic (r : GriessShortIndex) : ℤ :=
  ∑ i, (if Nat.testBit 0x0f000f i.val then 2 else 1) * griessShortIntegral r i ^ 2

/-- The actual fifth matrix evaluates the octad-weighted quadratic invariant. -/
theorem generatedFeasibleFifthSlot_matrix_quadratic (r : GriessShortIndex) :
    Matrix.toBilin' (griessConwayEncode generatedFifthAxis).1 (griessShortVector r)
      (griessShortVector r) = (generatedFeasibleFifthSlotQuadratic r : ℝ) / 32 := by
  rw [generatedFifth_matrix, Matrix.toBilin'_apply]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [generatedFeasibleFifthSlotQuadratic, Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [griessShortVector]
  split_ifs <;> push_cast <;> field_simp <;> rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)] <;>
    ring

/-- A fiber fixing the fifth axis preserves the octad-weighted quadratic invariant. -/
theorem generatedFeasibleFifthSlot_fixer_quadratic (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedFifthAxis = generatedFifthAxis)
    (r : GriessShortIndex) :
    generatedFeasibleFifthSlotQuadratic (griessShortPermutation f.val.2 r) =
      generatedFeasibleFifthSlotQuadratic r := by
  have hm : conwayMatrixAction f.val.2 (griessConwayEncode generatedFifthAxis).1 =
      (griessConwayEncode generatedFifthAxis).1 := by
    have he : (griessConwayEncode (rhoLocal (localFiberIntoH f) generatedFifthAxis)).1 =
        (griessConwayEncode generatedFifthAxis).1 :=
      congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
    rwa [generatedFourth_local_matrix] at he
  have hv : f.val.2.val.symm (griessShortVector (griessShortPermutation f.val.2 r)) =
      griessShortVector r ∨
      f.val.2.val.symm (griessShortVector (griessShortPermutation f.val.2 r)) =
        -griessShortVector r := by
    rcases griessShortPermutation_vector f.val.2 r with h | h
    · left
      rw [← h, LinearEquiv.symm_apply_apply]
    · right
      rw [show griessShortVector (griessShortPermutation f.val.2 r) =
          -f.val.2.val (griessShortVector r) by rw [h, neg_neg], map_neg,
        LinearEquiv.symm_apply_apply]
  have hq := conwayMatrixAction_pairing f.val.2 (griessConwayEncode generatedFifthAxis).1
    (griessShortVector (griessShortPermutation f.val.2 r))
    (griessShortVector (griessShortPermutation f.val.2 r))
  rw [hm] at hq
  have hq' : Matrix.toBilin' (griessConwayEncode generatedFifthAxis).1
      (griessShortVector (griessShortPermutation f.val.2 r))
      (griessShortVector (griessShortPermutation f.val.2 r)) =
      Matrix.toBilin' (griessConwayEncode generatedFifthAxis).1
        (griessShortVector r) (griessShortVector r) := by
    rw [hq]
    rcases hv with h | h <;> rw [h]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [generatedFeasibleFifthSlot_matrix_quadratic, generatedFeasibleFifthSlot_matrix_quadratic]
    at hq'
  have hq'' : (generatedFeasibleFifthSlotQuadratic (griessShortPermutation f.val.2 r) : ℝ) =
      generatedFeasibleFifthSlotQuadratic r := by
    linarith
  exact_mod_cast hq''

/-- The slot label has octad-weighted quadratic invariant thirty-two. -/
theorem generatedFeasibleFifthSlot_first_quadratic :
    generatedFeasibleFifthSlotQuadratic (Sum.inl (0, generatedFeasibleFifthSlotPair)) = 32 := by
  have hl : griessShortIntegral (Sum.inl (0, generatedFeasibleFifthSlotPair)) =
      fun i => 4 * (if i = 12 then 1 else 0) + (-4) * (if i = 13 then 1 else 0) := by
    funext i
    simp only [griessShortIntegral, generatedFeasibleFifthSlotPair_coordinates, ite_true]
  rw [generatedFeasibleFifthSlotQuadratic, hl]
  decide +kernel

/-- An actual short label with quadratic invariant thirty-two vanishes on the octad. -/
theorem generatedFeasibleFifthSlot_quadratic_octad_zero (r : GriessShortIndex)
    (hr : generatedFeasibleFifthSlotQuadratic r = 32) (i : Fin 24)
    (hi : Nat.testBit 0x0f000f i.val = true) : griessShortIntegral r i = 0 := by
  have hn := griessShortIntegral_squareSum r
  have hsplit : generatedFeasibleFifthSlotQuadratic r = leechSquareSum (griessShortIntegral r) +
      ∑ j, (if Nat.testBit 0x0f000f j.val then griessShortIntegral r j ^ 2 else 0) := by
    rw [generatedFeasibleFifthSlotQuadratic, leechSquareSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hsplit, hn] at hr
  have hz : ∑ j, (if Nat.testBit 0x0f000f j.val then griessShortIntegral r j ^ 2 else 0) = 0 := by
    linarith
  have hnonneg : ∀ j ∈ Finset.univ, 0 ≤
      (if Nat.testBit 0x0f000f j.val then griessShortIntegral r j ^ 2 else 0) := by
    intro j _
    split_ifs
    · exact sq_nonneg _
    · exact le_refl 0
  have hj := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ _)
  simp only [hi, ite_true] at hj
  exact pow_eq_zero_iff (by norm_num) |>.mp hj

/-- Every actual octad coefficient of the fifth axis is zero or has absolute value one eighth. -/
theorem generatedFeasibleFifthSlot_octad_coefficient (d : Fin 759) (e : Fin 64) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inr (Sum.inl (d, e))) = 0 ∨
      (griessConwayEncode generatedFifthAxis).2.1 (Sum.inr (Sum.inl (d, e))) = 1 / 8 ∨
      (griessConwayEncode generatedFifthAxis).2.1 (Sum.inr (Sum.inl (d, e))) = -1 / 8 := by
  by_cases hd : ∃ j, generatedFifthEvenRootOctad j = d
  · obtain ⟨j, rfl⟩ := hd
    right
    rw [generatedFifth_final_octad_coordinate]
    simp only [trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Int.coe_castRingHom]
    have hT : trialityIntegerMatrix e (generatedFifthEvenRootSign j) = 1 ∨
        trialityIntegerMatrix e (generatedFifthEvenRootSign j) = -1 := by
      unfold trialityIntegerMatrix trialityIntegerDiagonal trialityHadamard
      split_ifs <;> simp
    unfold qSign
    rcases hT with h | h <;> rw [h] <;> split_ifs <;> norm_num
  · left
    rw [generatedFifthAxis_local_expression, generatedFourthQShortBasis_triality_octad]
    apply Finset.sum_eq_zero
    intro f _
    rw [generatedFourth_local_short]
    have hz : localShortOperator generatedFifthLocalFiber
        (griessConwayEncode (sExtra (conwayShortAxis
          (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 (Sum.inr (Sum.inl (d, f))) =
          0 := by
      by_contra hn
      rcases (generatedFifth_middle_nonzero_iff _).mp hn with ⟨k, hk⟩ | ⟨k, hk⟩
      · simp only [generatedFifthOddRootOutputLabel, Sum.inr.injEq, reduceCtorEq] at hk
      · simp only [generatedFifthEvenRootOutputLabel, Sum.inr.injEq, Sum.inl.injEq,
          Prod.mk.injEq] at hk
        exact hd ⟨k, hk.1⟩
    rw [hz, mul_zero]

/-- Finite classification: an increasing pair outside the octad whose fifth pair numerator is
`±4` belongs to the catalogue, with the matching phase. -/
theorem generatedFeasibleFifthSlot_pair_classification : ∀ s : Fin 2, ∀ a b : Fin 24,
    ∀ c : ZMod 2, a < b → Nat.testBit 0x0f000f a.val = false →
      Nat.testBit 0x0f000f b.val = false →
      generatedFifthFinalPairNumerator s a b = (if c = 0 then 4 else -4) →
      ∃ k : Fin 16, generatedFeasibleFifthSlotCatalogueData k = (s, (a, b), c) := by
  decide +kernel

/-- Every actual fiber fixing the fifth axis sends the slot label and phase into the catalogue. -/
theorem generatedFeasibleFifthSlot_fixer_catalogue (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedFifthAxis = generatedFifthAxis) :
    ∃ k : Fin 16, griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleFifthSlotPair)) =
        generatedFeasibleFifthSlotCatalogueLabel k ∧
      localShortPhase f (Sum.inl (0, generatedFeasibleFifthSlotPair)) =
        (generatedFeasibleFifthSlotCatalogueData k).2.2 := by
  have hshort := generatedFeasibleFifthSlot_fixer_short f hf
    (Sum.inl (0, generatedFeasibleFifthSlotPair))
  rw [generatedFeasibleFifthSlot_first_coefficient] at hshort
  have hquad := generatedFeasibleFifthSlot_fixer_quadratic f hf
    (Sum.inl (0, generatedFeasibleFifthSlotPair))
  rw [generatedFeasibleFifthSlot_first_quadratic] at hquad
  have hzero := generatedFeasibleFifthSlot_quadratic_octad_zero _ hquad
  generalize localShortPhase f (Sum.inl (0, generatedFeasibleFifthSlotPair)) = c at hshort ⊢
  generalize griessShortPermutation f.val.2 (Sum.inl (0, generatedFeasibleFifthSlotPair)) = r
    at hshort hzero ⊢
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · have hmem := (griessCoordinatePairEquiv p).property
    have hab : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
      (Finset.mem_filter.mp hmem).2
    have hne : (griessCoordinatePair p).1 ≠ (griessCoordinatePair p).2 := ne_of_lt hab
    have ha : Nat.testBit 0x0f000f (griessCoordinatePair p).1.val = false := by
      by_contra h
      have h0 := hzero (griessCoordinatePair p).1 (by simpa using h)
      simp only [griessShortIntegral, ite_true, hne, ite_false] at h0
      norm_num at h0
    have hb : Nat.testBit 0x0f000f (griessCoordinatePair p).2.val = false := by
      by_contra h
      have h0 := hzero (griessCoordinatePair p).2 (by simpa using h)
      simp only [griessShortIntegral, hne.symm, ite_false, ite_true] at h0
      split_ifs at h0 <;> norm_num at h0
    have hnum : generatedFifthFinalPairNumerator s (griessCoordinatePair p).1
        (griessCoordinatePair p).2 = (if c = 0 then 4 else -4) := by
      rw [generatedFifth_final_pair_numerator] at hshort
      have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc c with rfl | rfl
      · simp only [qSign, ite_true] at hshort
        simp only [ite_true]
        have h4 : (generatedFifthFinalPairNumerator s (griessCoordinatePair p).1
            (griessCoordinatePair p).2 : ℝ) = 4 := by linarith
        exact_mod_cast h4
      · simp only [qSign, show (1 : ZMod 2) ≠ 0 by decide, ite_false] at hshort
        simp only [show (1 : ZMod 2) ≠ 0 by decide, ite_false]
        have h4 : (generatedFifthFinalPairNumerator s (griessCoordinatePair p).1
            (griessCoordinatePair p).2 : ℝ) = -4 := by linarith
        exact_mod_cast h4
    obtain ⟨k, hk⟩ := generatedFeasibleFifthSlot_pair_classification s _ _ c hab ha hb hnum
    refine ⟨k, ?_, ?_⟩
    · have hdata : generatedFeasibleFifthSlotCatalogueData k =
          (s, griessCoordinatePair p, c) := hk
      simp only [generatedFeasibleFifthSlotCatalogueLabel, Sum.inl.injEq, Prod.mk.injEq]
      refine ⟨by rw [hdata], ?_⟩
      apply griessCoordinatePairEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      change griessCoordinatePair p = (generatedFeasibleFifthSlotCatalogueData k).2.1
      rw [hdata]
    · rw [hk]
  · exfalso
    rcases generatedFeasibleFifthSlot_octad_coefficient d e with h | h | h <;>
      rw [h] at hshort <;> unfold qSign at hshort <;> split_ifs at hshort <;>
      norm_num at hshort
  · exfalso
    have h0 := hzero 0 (by decide)
    simp only [griessShortIntegral] at h0
    split_ifs at h0 <;> norm_num at h0

set_option backward.isDefEq.respectTransparency true in
-- Respect transparency so the subgroup action instance does not unfold the fifth axis.
/-- Coverage: the entire orbit of the slot axis under the actual fifth-axis stabilizer lies in
the sixteen-element catalogue. -/
theorem generatedFeasibleFifthSlot_orbit_subset :
    MulAction.orbit generatedFifthLocalAxisStabilizer generatedFeasibleFifthSlotFirstAxis ⊆
      Set.range generatedFeasibleFifthSlotCatalogueAxis := by
  rintro y ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedFifthAxis = generatedFifthAxis := by
    rw [hf]
    exact h.property
  obtain ⟨k, hk1, hk2⟩ := generatedFeasibleFifthSlot_fixer_catalogue f hfix
  refine ⟨k, ?_⟩
  change generatedFeasibleFifthSlotCatalogueAxis k =
    rhoLocal h.val generatedFeasibleFifthSlotFirstAxis
  rw [← hf, generatedFeasibleFifthSlotFirstAxis, generatedFeasibleFifthSlot_local_image, hk1, hk2,
    add_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
