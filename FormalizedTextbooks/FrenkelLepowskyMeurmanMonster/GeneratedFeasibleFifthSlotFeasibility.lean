/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotFeasibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPairTransition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthDiagonal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortVectorQTransport

/-! Genuine feasibility of the counted fifth axis relative to an actual signed pair axis.

The first signed pair axis is the actual axis of the coordinate pair `(12, 13)`. Its membership
in the actual first-stabilizer orbit of the opposite axis uses only literal triality, the
literal local fifth word, the actual perpendicular secondary catalogue and genuine local
transports. No orbit size or source class label is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The local fiber image of any actual signed-short axis, transported to H. -/
theorem generatedFeasibleFifthSlot_local_image (f : localFiberSubgroup) (t : GriessShortIndex)
    (e : ZMod 2) :
    rhoLocal (localFiberIntoH f) (conwayShortAxis t e) =
      conwayShortAxis (griessShortPermutation f.val.2 t) (localShortPhase f t + e) :=
  generatedAxis_localFiber_image f t e

set_option maxRecDepth 10000 in
-- Elaborate membership in the complete 93,150-address finite perpendicular catalogue.
/-- Two actual signed-short axes with perpendicular labels form a genuine feasible pair:
the second lies in the actual first-stabilizer orbit of the opposite of the first. -/
theorem generatedFeasibleFifthSlot_perpendicular_feasible (r s : GriessShortIndex)
    (c d : ZMod 2) (hrs : stdPairingFun (griessShortVector r) (griessShortVector s) = 0) :
    conwayShortAxis s d ∈ generatedFeasibleVectorOrbit (conwayShortAxis r c)
      (conwayShortAxis r (c + 1)) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) c 0
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  have himage (t : GriessShortIndex) (e : ZMod 2) : rhoLocal h (conwayShortAxis t e) =
      conwayShortAxis (griessShortPermutation f.val.2 t) (localShortPhase f t + e) := by
    rw [← hf]
    exact generatedFeasibleFifthSlot_local_image f t e
  rw [himage] at hh
  have hpair := @generatedAxis_signed_injective
    (griessShortPermutation f.val.2 r, localShortPhase f r + c)
    (Sum.inl (0, generatedFeasiblePhysicalRootPair), 0) hh
  have hr : griessShortPermutation f.val.2 r = Sum.inl (0, generatedFeasiblePhysicalRootPair) :=
    congrArg Prod.fst hpair
  have hc : localShortPhase f r + c = 0 := congrArg Prod.snd hpair
  have hperp : griessShortIntegral (griessShortPermutation f.val.2 s) 0 =
      griessShortIntegral (griessShortPermutation f.val.2 s) 1 := by
    rw [← generatedFeasiblePhysicalRoot_orthogonal_iff, ← hr]
    exact generatedFeasibleSixthSlot_image_orthogonal f.val.2 r s hrs
  have hmem : rhoLocal h (conwayShortAxis s d) ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) := by
    apply generatedFeasibleSecondaryLocalOrbit_subset
    rw [generatedFeasibleSecondaryLocalOrbit_eq_physical, himage]
    refine ⟨⟨(griessShortPermutation f.val.2 s, localShortPhase f s + d), ?_⟩, rfl⟩
    exact Finset.mem_product.mpr
      ⟨(generatedFeasibleOrthogonalShortLabels_mem _).mpr hperp, Finset.mem_univ _⟩
  have ht := generatedFeasibleSixthSlot_orbit_map (localIntoGenerated h⁻¹) hmem
  have hinv (y : GriessSpace) : (localIntoGenerated h⁻¹).val (rhoLocal h y) = y := by
    change rhoLocal h⁻¹ (rhoLocal h y) = y
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have h0 : conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 =
      rhoLocal h (conwayShortAxis r c) := by
    rw [himage, hr, hc]
  have h1 : conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1 =
      rhoLocal h (conwayShortAxis r (c + 1)) := by
    rw [himage, hr, ← add_assoc, hc, zero_add]
  rw [h0, h1, hinv, hinv, hinv] at ht
  exact ht

/-- The actual coordinate pair `(12, 13)`. -/
def generatedFeasibleFifthSlotPair : Fin 276 :=
  griessCoordinatePairEquiv.symm ⟨(12, 13), by decide⟩

/-- The chosen address is bound to its two physical coordinates. -/
theorem generatedFeasibleFifthSlotPair_coordinates :
    griessCoordinatePair generatedFeasibleFifthSlotPair = (12, 13) :=
  congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply ⟨(12, 13), by decide⟩)

/-- The actual coordinate pair `(1, 2)` reached by the inverse middle spatial word. -/
def generatedFeasibleFifthSlotMiddlePair : Fin 276 :=
  griessCoordinatePairEquiv.symm ⟨(1, 2), by decide⟩

/-- The middle address is bound to its two physical coordinates. -/
theorem generatedFeasibleFifthSlotMiddlePair_coordinates :
    griessCoordinatePair generatedFeasibleFifthSlotMiddlePair = (1, 2) :=
  congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply ⟨(1, 2), by decide⟩)

/-- The actual first signed axis used for the fifth slot: the minus pair `4(e₁₂-e₁₃)`, phase 0. -/
def generatedFeasibleFifthSlotFirstAxis : GriessSpace :=
  conwayShortAxis (Sum.inl (0, generatedFeasibleFifthSlotPair)) 0

/-- An integer matrix with a real scalar denominator transports actual short labels. -/
theorem generatedFeasibleFifthSlot_label_of_integral (e : leechIsomSubgroup)
    (M : Matrix (Fin 24) (Fin 24) ℤ) (d : ℤ) (hd : (d : ℝ) ≠ 0)
    (he : ∀ v, e.val v = M.map (fun z => (z : ℝ) / d) *ᵥ v) (r s : GriessShortIndex)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : M *ᵥ griessShortIntegral r = (d * ε) • griessShortIntegral s) :
    griessShortPermutation e r = s := by
  apply monsterNortonShortPermutation_of_vector
  have hv : e.val (griessShortVector r) = (ε : ℝ) • griessShortVector s := by
    rw [he]
    funext i
    have hi := congrFun h i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, griessShortVector, Pi.smul_apply,
      smul_eq_mul]
    have hc : (∑ j, (M i j : ℝ) * (griessShortIntegral r j : ℝ)) =
        (d : ℝ) * ε * griessShortIntegral s i := by
      exact_mod_cast hi
    calc (∑ j, (M i j : ℝ) / d * ((griessShortIntegral r j : ℝ) / Real.sqrt 8))
        = (∑ j, (M i j : ℝ) * (griessShortIntegral r j : ℝ)) / d / Real.sqrt 8 := by
          rw [Finset.sum_div, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = (ε : ℝ) * ((griessShortIntegral s i : ℝ) / Real.sqrt 8) := by
          rw [hc]
          field_simp
  rcases hε with rfl | rfl
  · left
    rw [hv]
    simp
  · right
    rw [hv]
    simp

/-- The inverse middle spatial word carries the slot pair to the plus pair `(1, 2)`. -/
theorem generatedFeasibleFifthSlot_inverse_middle_label :
    griessShortPermutation (generatedFifthLocalFiber⁻¹).val.2
      (Sum.inl (0, generatedFeasibleFifthSlotPair)) =
        Sum.inl (1, generatedFeasibleFifthSlotMiddlePair) := by
  apply generatedFeasibleFifthSlot_label_of_integral _ generatedFifthInverseNumerator 4
    (by norm_num) _ _ _ 1 (Or.inl rfl)
  · have hl : griessShortIntegral (Sum.inl (0, generatedFeasibleFifthSlotPair)) =
        fun i => 4 * (if i = 12 then 1 else 0) + (-4) * (if i = 13 then 1 else 0) := by
      funext i
      simp only [griessShortIntegral, generatedFeasibleFifthSlotPair_coordinates, ite_true]
    have hr : griessShortIntegral (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) =
        fun i => 4 * (if i = 1 then 1 else 0) + 4 * (if i = 2 then 1 else 0) := by
      funext i
      simp only [griessShortIntegral, generatedFeasibleFifthSlotMiddlePair_coordinates]
      norm_num
    rw [hl, hr]
    decide +kernel
  · intro v
    rw [generatedFifth_inverse_spatial_action]
    congr 1
    ext i j
    rw [generatedFifth_inverse_matrix_entry]
    simp

/-- The literal middle spatial word carries the plus pair `(1, 2)` to the slot pair. -/
theorem generatedFeasibleFifthSlot_middle_label :
    griessShortPermutation generatedFifthLocalFiber.val.2
      (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) =
        Sum.inl (0, generatedFeasibleFifthSlotPair) := by
  rw [← generatedFeasibleFifthSlot_inverse_middle_label, ← Equiv.Perm.mul_apply, ← map_mul]
  change griessShortPermutation (generatedFifthLocalFiber * generatedFifthLocalFiber⁻¹).val.2 _ = _
  rw [mul_inv_cancel]
  change griessShortPermutation (1 : leechIsomSubgroup) _ = _
  rw [map_one]
  rfl

/-- Both signed pair labels over `(1, 2)` have explicit physical integer coordinates. -/
theorem generatedFeasibleFifthSlot_middle_integral (s : Fin 2) :
    griessShortIntegral (Sum.inl (s, generatedFeasibleFifthSlotMiddlePair)) =
      fun i => 4 * (if i = 1 then 1 else 0) +
        (if s = 0 then -4 else 4) * (if i = 2 then 1 else 0) := by
  funext i
  simp only [griessShortIntegral, generatedFeasibleFifthSlotMiddlePair_coordinates]

/-- The pairing of a vector supported on `(1, 2)` reads only those two coordinates. -/
theorem generatedFeasibleFifthSlot_middle_pairing (x : ℤ) (v : Fin 24 → ℤ) :
    leechIntegralPairing (fun i => 4 * (if i = 1 then 1 else 0) + x * (if i = 2 then 1 else 0)) v =
      4 * v 1 + x * v 2 := by
  simp only [leechIntegralPairing, add_mul, mul_assoc, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero]

/-- Distinct actual signed axes over the pair `(1, 2)` are mutually feasible. -/
theorem generatedFeasibleFifthSlot_middle_pair_feasible (s t : Fin 2) (c d : ZMod 2)
    (hne : (s, c) ≠ (t, d)) :
    conwayShortAxis (Sum.inl (t, generatedFeasibleFifthSlotMiddlePair)) d ∈
      generatedFeasibleVectorOrbit
        (conwayShortAxis (Sum.inl (s, generatedFeasibleFifthSlotMiddlePair)) c)
        (conwayShortAxis (Sum.inl (s, generatedFeasibleFifthSlotMiddlePair)) (c + 1)) := by
  by_cases hst : s = t
  · subst t
    have hcd : c ≠ d := fun h => hne (by rw [h])
    have hall : ∀ c d : ZMod 2, c ≠ d → d = c + 1 := by decide
    rw [hall c d hcd]
    exact MulAction.mem_orbit_self _
  · apply generatedFeasibleFifthSlot_perpendicular_feasible
    rw [griessShortVector_pairing, generatedFeasibleFifthSlot_middle_integral,
      generatedFeasibleFifthSlot_middle_integral, generatedFeasibleFifthSlot_middle_pairing]
    have h : (4 * (4 * (if (1 : Fin 24) = 1 then 1 else 0) +
        (if t = 0 then -4 else 4) * (if (1 : Fin 24) = 2 then 1 else 0)) +
      (if s = 0 then -4 else 4) * (4 * (if (2 : Fin 24) = 1 then 1 else 0) +
        (if t = 0 then -4 else 4) * (if (2 : Fin 24) = 2 then 1 else 0)) : ℤ) = 0 := by
      have hall : ∀ s t : Fin 2, s ≠ t → (4 * (4 * (if (1 : Fin 24) = 1 then 1 else 0) +
          (if t = 0 then -4 else 4) * (if (1 : Fin 24) = 2 then 1 else 0)) +
        (if s = 0 then -4 else 4) * (4 * (if (2 : Fin 24) = 1 then 1 else 0) +
          (if t = 0 then -4 else 4) * (if (2 : Fin 24) = 2 then 1 else 0)) : ℤ) = 0 := by
        decide
      exact hall s t hst
    rw [h]
    norm_num

/-- The actual source octad axis is perpendicular to both signed pair labels over `(1, 2)`. -/
theorem generatedFeasibleFifthSlot_octad_perpendicular (s : Fin 2) :
    stdPairingFun (griessShortVector (Sum.inl (s, generatedFeasibleFifthSlotMiddlePair)))
      (griessShortVector (Sum.inr (Sum.inl (generatedFourthOctad, 0)))) = 0 := by
  rw [griessShortVector_pairing, generatedFeasibleFifthSlot_middle_integral,
    generatedFeasibleFifthSlot_middle_pairing]
  have hz (i : Fin 24) (hi : Nat.testBit 0xcccc00 i.val = false) :
      griessShortIntegral (Sum.inr (Sum.inl (generatedFourthOctad, 0))) i = 0 := by
    simp only [griessShortIntegral, generatedFourthOctad_mask, hi]
    rfl
  rw [hz 1 (by decide), hz 2 (by decide)]
  norm_num

/-- The source octad axis lies in the actual feasible orbit of every signed pair axis over
`(1, 2)` relative to its opposite. -/
theorem generatedFeasibleFifthSlot_octad_feasible (s : Fin 2) (c : ZMod 2) :
    conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0 ∈
      generatedFeasibleVectorOrbit
        (conwayShortAxis (Sum.inl (s, generatedFeasibleFifthSlotMiddlePair)) c)
        (conwayShortAxis (Sum.inl (s, generatedFeasibleFifthSlotMiddlePair)) (c + 1)) :=
  generatedFeasibleFifthSlot_perpendicular_feasible _ _ c 0
    (generatedFeasibleFifthSlot_octad_perpendicular s)

/-- Rebasing in the other direction: any orbit vector generates the same feasible orbit. -/
theorem generatedFeasibleFifthSlot_rebase_symm {a b x y : GriessSpace}
    (hx : x ∈ generatedFeasibleVectorOrbit a b) (hy : y ∈ generatedFeasibleVectorOrbit a b) :
    y ∈ generatedFeasibleVectorOrbit a x := by
  unfold generatedFeasibleVectorOrbit at hx hy ⊢
  rwa [MulAction.orbit_eq_iff.mpr hx]

/-- The actual triality image of the source octad axis is feasible relative to every signed
plus-pair axis over `(1, 2)`. Literal triality cycles the three non-distinguished pair axes. -/
theorem generatedFeasibleFifthSlot_triality_octad_feasible (c : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0) ∈
      generatedFeasibleVectorOrbit
        (conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) c)
        (conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) (c + 1)) := by
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · have ho := generatedFeasibleFifthSlot_octad_feasible 1 1
    have hb := generatedFeasibleFifthSlot_middle_pair_feasible 1 0 1 1 (by decide)
    have ht := generatedFeasibleSixthSlot_orbit_map extraIntoGenerated
      (generatedFeasibleFifthSlot_rebase_symm hb ho)
    change sExtra _ ∈ generatedFeasibleVectorOrbit (sExtra _) (sExtra _) at ht
    have e1 : sExtra (conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) 1) =
        conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) 0 := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    have e2 : sExtra (conwayShortAxis (Sum.inl (0, generatedFeasibleFifthSlotMiddlePair)) 1) =
        conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) (0 + 1) := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    rw [e1, e2] at ht
    exact ht
  · have ho := generatedFeasibleFifthSlot_octad_feasible 0 1
    have hb := generatedFeasibleFifthSlot_middle_pair_feasible 0 1 1 1 (by decide)
    have ht := generatedFeasibleSixthSlot_orbit_map extraIntoGenerated
      (generatedFeasibleFifthSlot_rebase_symm hb ho)
    change sExtra _ ∈ generatedFeasibleVectorOrbit (sExtra _) (sExtra _) at ht
    have e1 : sExtra (conwayShortAxis (Sum.inl (0, generatedFeasibleFifthSlotMiddlePair)) 1) =
        conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) 1 := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    have e2 : sExtra (conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) 1) =
        conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) (1 + 1) := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    rw [e1, e2] at ht
    exact ht

/-- The counted fifth axis lies in the actual first-stabilizer orbit of the opposite slot axis.
The explicit word is triality, the literal fifth local fiber and triality again. -/
theorem generatedFeasibleFifthSlot_fifth_feasible :
    generatedFifthAxis ∈ generatedFeasibleVectorOrbit generatedFeasibleFifthSlotFirstAxis
      (conwayShortAxis (Sum.inl (0, generatedFeasibleFifthSlotPair)) 1) := by
  have hA : rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair))
        (localShortPhase generatedFifthLocalFiber
          (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)))) =
      generatedFeasibleFifthSlotFirstAxis := by
    rw [generatedFeasibleFifthSlot_local_image, generatedFeasibleFifthSlot_middle_label,
      CharTwo.add_self_eq_zero]
    rfl
  have hB : rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (conwayShortAxis (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair))
        (localShortPhase generatedFifthLocalFiber
          (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)) + 1)) =
      conwayShortAxis (Sum.inl (0, generatedFeasibleFifthSlotPair)) 1 := by
    rw [generatedFeasibleFifthSlot_local_image, generatedFeasibleFifthSlot_middle_label,
      ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have h1 := generatedFeasibleFifthSlot_triality_octad_feasible
    (localShortPhase generatedFifthLocalFiber (Sum.inl (1, generatedFeasibleFifthSlotMiddlePair)))
  have h2 := generatedFeasibleSixthSlot_orbit_map
    (localIntoGenerated (localFiberIntoH generatedFifthLocalFiber)) h1
  change rhoLocal (localFiberIntoH generatedFifthLocalFiber) _ ∈ generatedFeasibleVectorOrbit
    (rhoLocal (localFiberIntoH generatedFifthLocalFiber) _)
    (rhoLocal (localFiberIntoH generatedFifthLocalFiber) _) at h2
  rw [hA, hB] at h2
  rw [generatedFifthAxis_local_expression]
  exact generatedFeasibleSixthSlot_orbit_triality generatedFeasibleFifthSlotPair h2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
