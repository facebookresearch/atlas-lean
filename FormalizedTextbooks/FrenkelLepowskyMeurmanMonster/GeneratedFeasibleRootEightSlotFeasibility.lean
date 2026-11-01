/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleFifthSlotFeasibility
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot08Short
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortFiber
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! The counted root-eight prototype is a genuine feasible axis for an actual signed pair axis.

This is the feasibility half of source slot 9 (label 10A1) of Höhn–Seysen,
arXiv:2508.01037, §4 and Table 3. Here "root eight" is the global local family of source
Table 1 at zero-based index 9, whose prototype is the literal triality, root-8 local word and
triality image of the counted fifth prototype; it is unrelated to the one-eighth coefficient.

The first signed axis is the plus pair `4(e₁₆+e₁₇)` with phase 0. Feasibility follows the
literal word of the prototype: the source octad axis is perpendicular to the pair `(0, 3)`,
the literal fifth local word carries that plus pair to the plus pair `(14, 15)`, the literal
root-8 word carries the minus pair `(14, 15)` to the plus pair `(16, 17)` with central phase
zero, and each triality step is transported by rebasing onto another axis over the same pair.
No orbit size or source class label is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The literal pair address `2` is the coordinate pair `(0, 3)`. -/
theorem generatedFeasibleRootEightSlot_source_coordinates :
    griessCoordinatePair 2 = (0, 3) := by
  rw [← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

/-- The literal pair address `231` is the coordinate pair `(14, 15)`. -/
theorem generatedFeasibleRootEightSlot_middle_coordinates :
    griessCoordinatePair 231 = (14, 15) := by
  rw [← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

/-- The literal pair address `248` is the coordinate pair `(16, 17)`. -/
theorem generatedFeasibleRootEightSlot_root_coordinates :
    griessCoordinatePair 248 = (16, 17) := by
  rw [← generatedAxisGlobalPairCoordinates_actual]
  decide +kernel

/-- The two coordinates of every actual pair address are distinct. -/
theorem generatedFeasibleRootEightSlot_pair_ne (p : Fin 276) :
    (griessCoordinatePair p).1 ≠ (griessCoordinatePair p).2 := by
  have h := (griessCoordinatePairEquiv p).property
  simp only [griessCoordinatePairs, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact ne_of_lt h

/-- The minus and plus pair labels over the same actual pair are perpendicular. -/
theorem generatedFeasibleRootEightSlot_pair_perpendicular (p : Fin 276) (s t : Fin 2)
    (hst : s ≠ t) :
    stdPairingFun (griessShortVector (Sum.inl (s, p))) (griessShortVector (Sum.inl (t, p))) =
      0 := by
  rw [griessShortVector_pairing]
  have hne := generatedFeasibleRootEightSlot_pair_ne p
  have hz : leechIntegralPairing (griessShortIntegral (Sum.inl (s, p)))
      (griessShortIntegral (Sum.inl (t, p))) = 0 := by
    simp only [leechIntegralPairing, griessShortIntegral, add_mul, mul_add, ite_mul, mul_ite,
      mul_one, zero_mul, mul_zero, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hne, hne.symm, ite_false]
    fin_cases s <;> fin_cases t
    all_goals first | exact absurd rfl hst | norm_num
  rw [hz]
  norm_num

/-- Distinct actual signed axes over the same pair are mutually feasible. -/
theorem generatedFeasibleRootEightSlot_pair_feasible (p : Fin 276) (s t : Fin 2) (c d : ZMod 2)
    (hne : (s, c) ≠ (t, d)) :
    conwayShortAxis (Sum.inl (t, p)) d ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (s, p)) c) (conwayShortAxis (Sum.inl (s, p)) (c + 1)) := by
  by_cases hst : s = t
  · subst t
    have hcd : c ≠ d := fun h => hne (by rw [h])
    have hall : ∀ c d : ZMod 2, c ≠ d → d = c + 1 := by decide
    rw [hall c d hcd]
    exact MulAction.mem_orbit_self _
  · exact generatedFeasibleFifthSlot_perpendicular_feasible _ _ c d
      (generatedFeasibleRootEightSlot_pair_perpendicular p s t hst)

/-- Both signed pair labels over `(0, 3)` have explicit physical integer coordinates. -/
theorem generatedFeasibleRootEightSlot_source_integral (s : Fin 2) :
    griessShortIntegral (Sum.inl (s, 2)) =
      fun i => 4 * (if i = 0 then 1 else 0) +
        (if s = 0 then -4 else 4) * (if i = 3 then 1 else 0) := by
  funext i
  simp only [griessShortIntegral, generatedFeasibleRootEightSlot_source_coordinates]

/-- The pairing of a vector supported on `(0, 3)` reads only those two coordinates. -/
theorem generatedFeasibleRootEightSlot_source_pairing (x : ℤ) (v : Fin 24 → ℤ) :
    leechIntegralPairing (fun i => 4 * (if i = 0 then 1 else 0) + x * (if i = 3 then 1 else 0)) v =
      4 * v 0 + x * v 3 := by
  simp only [leechIntegralPairing, add_mul, mul_assoc, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero]

/-- The actual source octad axis is perpendicular to both signed pair labels over `(0, 3)`. -/
theorem generatedFeasibleRootEightSlot_octad_perpendicular (s : Fin 2) :
    stdPairingFun (griessShortVector (Sum.inl (s, 2)))
      (griessShortVector (Sum.inr (Sum.inl (generatedFourthOctad, 0)))) = 0 := by
  rw [griessShortVector_pairing, generatedFeasibleRootEightSlot_source_integral,
    generatedFeasibleRootEightSlot_source_pairing]
  have hz (i : Fin 24) (hi : Nat.testBit 0xcccc00 i.val = false) :
      griessShortIntegral (Sum.inr (Sum.inl (generatedFourthOctad, 0))) i = 0 := by
    simp only [griessShortIntegral, generatedFourthOctad_mask, hi]
    rfl
  rw [hz 0 (by decide), hz 3 (by decide)]
  norm_num

/-- The actual triality image of the source octad axis is feasible relative to every signed
plus-pair axis over `(0, 3)`. Literal triality cycles the three non-distinguished pair axes. -/
theorem generatedFeasibleRootEightSlot_triality_octad_feasible (c : ZMod 2) :
    sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0) ∈
      generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (1, 2)) c)
        (conwayShortAxis (Sum.inl (1, 2)) (c + 1)) := by
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · have ho := generatedFeasibleFifthSlot_perpendicular_feasible _ _ 1 0
      (generatedFeasibleRootEightSlot_octad_perpendicular 1)
    have hb := generatedFeasibleRootEightSlot_pair_feasible 2 1 0 1 1 (by decide)
    have ht := generatedFeasibleSixthSlot_orbit_map extraIntoGenerated
      (generatedFeasibleFifthSlot_rebase_symm hb ho)
    change sExtra _ ∈ generatedFeasibleVectorOrbit (sExtra _) (sExtra _) at ht
    have e1 : sExtra (conwayShortAxis (Sum.inl (1, 2)) 1) = conwayShortAxis (Sum.inl (1, 2)) 0 := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    have e2 : sExtra (conwayShortAxis (Sum.inl (0, 2)) 1) =
        conwayShortAxis (Sum.inl (1, 2)) (0 + 1) := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    rw [e1, e2] at ht
    exact ht
  · have ho := generatedFeasibleFifthSlot_perpendicular_feasible _ _ 1 0
      (generatedFeasibleRootEightSlot_octad_perpendicular 0)
    have hb := generatedFeasibleRootEightSlot_pair_feasible 2 0 1 1 1 (by decide)
    have ht := generatedFeasibleSixthSlot_orbit_map extraIntoGenerated
      (generatedFeasibleFifthSlot_rebase_symm hb ho)
    change sExtra _ ∈ generatedFeasibleVectorOrbit (sExtra _) (sExtra _) at ht
    have e1 : sExtra (conwayShortAxis (Sum.inl (0, 2)) 1) = conwayShortAxis (Sum.inl (1, 2)) 1 := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    have e2 : sExtra (conwayShortAxis (Sum.inl (1, 2)) 1) =
        conwayShortAxis (Sum.inl (1, 2)) (1 + 1) := by
      rw [generatedAxis_triality_pair_exact]
      rfl
    rw [e1, e2] at ht
    exact ht

/-- The inverse literal fifth spatial word carries the plus pair `(14, 15)` to the plus pair
`(0, 3)`; this is read off from the exact integer inverse matrix. -/
theorem generatedFeasibleRootEightSlot_inverse_fifth_label :
    griessShortPermutation (generatedFifthLocalFiber⁻¹).val.2 (Sum.inl (1, 231)) =
      Sum.inl (1, 2) := by
  apply generatedFeasibleFifthSlot_label_of_integral _ generatedFifthInverseNumerator 4
    (by norm_num) _ _ _ 1 (Or.inl rfl)
  · have hl : griessShortIntegral (Sum.inl (1, 231)) =
        fun i => 4 * (if i = 14 then 1 else 0) + 4 * (if i = 15 then 1 else 0) := by
      funext i
      simp only [griessShortIntegral, generatedFeasibleRootEightSlot_middle_coordinates]
      norm_num
    have hr : griessShortIntegral (Sum.inl (1, 2)) =
        fun i => 4 * (if i = 0 then 1 else 0) + 4 * (if i = 3 then 1 else 0) := by
      funext i
      simp only [griessShortIntegral, generatedFeasibleRootEightSlot_source_coordinates]
      norm_num
    rw [hl, hr]
    decide +kernel
  · intro v
    rw [generatedFifth_inverse_spatial_action]
    congr 1
    ext i j
    rw [generatedFifth_inverse_matrix_entry]
    simp

/-- The literal fifth spatial word carries the plus pair `(0, 3)` to the plus pair `(14, 15)`. -/
theorem generatedFeasibleRootEightSlot_fifth_label :
    griessShortPermutation generatedFifthLocalFiber.val.2 (Sum.inl (1, 2)) = Sum.inl (1, 231) := by
  rw [← generatedFeasibleRootEightSlot_inverse_fifth_label, ← Equiv.Perm.mul_apply, ← map_mul]
  change griessShortPermutation (generatedFifthLocalFiber * generatedFifthLocalFiber⁻¹).val.2 _ = _
  rw [mul_inv_cancel]
  change griessShortPermutation (1 : leechIsomSubgroup) _ = _
  rw [map_one]
  rfl

/-- The counted fifth axis is feasible for the opposite minus pair axis over `(14, 15)`.
The explicit word is triality, the literal fifth local fiber and triality again. -/
theorem generatedFeasibleRootEightSlot_fifth_feasible :
    generatedFifthAxis ∈ generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (0, 231)) 1)
      (conwayShortAxis (Sum.inl (0, 231)) 0) := by
  have hA : rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (conwayShortAxis (Sum.inl (1, 2)) (localShortPhase generatedFifthLocalFiber
        (Sum.inl (1, 2)))) = conwayShortAxis (Sum.inl (1, 231)) 0 := by
    rw [generatedFeasibleFifthSlot_local_image, generatedFeasibleRootEightSlot_fifth_label,
      CharTwo.add_self_eq_zero]
  have hB : rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (conwayShortAxis (Sum.inl (1, 2)) (localShortPhase generatedFifthLocalFiber
        (Sum.inl (1, 2)) + 1)) = conwayShortAxis (Sum.inl (1, 231)) 1 := by
    rw [generatedFeasibleFifthSlot_local_image, generatedFeasibleRootEightSlot_fifth_label,
      ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have h1 := generatedFeasibleRootEightSlot_triality_octad_feasible
    (localShortPhase generatedFifthLocalFiber (Sum.inl (1, 2)))
  have h2 := generatedFeasibleSixthSlot_orbit_local (localFiberIntoH generatedFifthLocalFiber) h1
  rw [hA, hB] at h2
  have hb := generatedFeasibleRootEightSlot_pair_feasible 231 1 0 0 0 (by decide)
  have h3 := generatedFeasibleSixthSlot_orbit_map extraIntoGenerated
    (generatedFeasibleFifthSlot_rebase_symm hb h2)
  change sExtra _ ∈ generatedFeasibleVectorOrbit (sExtra _) (sExtra _) at h3
  have e1 : sExtra (conwayShortAxis (Sum.inl (1, 231)) 0) =
      conwayShortAxis (Sum.inl (0, 231)) 1 := by
    rw [generatedAxis_triality_pair_exact]
    rfl
  have e2 : sExtra (conwayShortAxis (Sum.inl (0, 231)) 0) =
      conwayShortAxis (Sum.inl (0, 231)) 0 := by
    rw [generatedAxis_triality_pair_exact]
    rfl
  rw [e1, e2] at h3
  rw [generatedFifthAxis_local_expression]
  exact h3

/-- The literal root-8 word sends the preferred minus pair lift over `(14, 15)` to the
preferred plus pair lift over `(16, 17)` with central phase zero. -/
theorem generatedFeasibleRootEightSlot_word_Q_image :
    spinConjugation (generatedAxisGlobalFifthShortWordFiber 8).val.1
        (griessShortQ (Sum.inl (0, 231))) = griessShortQ (Sum.inl (1, 248)) := by
  have h := generatedAxisGlobalFifthRoot08Short_QImage (Sum.inl (0, 231))
  rw [generatedAxisGlobalFifthPacketQFinite_actual,
    ← generatedAxisGlobalFifthQFast_actual 8 generatedAxisGlobalFifthQCache08_actual,
    ← generatedAxisGlobalFifthShortWord_QImage] at h
  have hl : generatedAxisGlobalFifthRoot08ShortLabel (Sum.inl (0, 231)) = Sum.inl (1, 248) := by
    decide +kernel
  have hp : generatedAxisGlobalFifthRoot08ShortPhase (Sum.inl (0, 231)) = 0 := by
    decide +kernel
  rw [hl, hp, show qCentral 0 = 1 from rfl, one_mul] at h
  exact h

/-- The literal root-8 word has central phase zero on the minus pair label over `(14, 15)`. -/
theorem generatedFeasibleRootEightSlot_word_phase :
    localShortPhase (generatedAxisGlobalFifthShortWordFiber 8) (Sum.inl (0, 231)) = 0 := by
  unfold localShortPhase
  rw [generatedFeasibleRootEightSlot_word_Q_image, griessShortQ_coeff]

/-- The literal root-8 word carries the minus pair label over `(14, 15)` to the plus pair
label over `(16, 17)`. -/
theorem generatedFeasibleRootEightSlot_word_label :
    griessShortPermutation (generatedAxisGlobalFifthShortWordFiber 8).val.2 (Sum.inl (0, 231)) =
      Sum.inl (1, 248) := by
  have hb := griessShortQ_image_base (generatedAxisGlobalFifthShortWordFiber 8) (Sum.inl (0, 231))
  rw [generatedFeasibleRootEightSlot_word_Q_image] at hb
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact (congrArg Multiplicative.toAdd hb).symm

/-- The literal root-8 local word sends both signs of the minus pair axis over `(14, 15)` to the
corresponding signs of the plus pair axis over `(16, 17)`. -/
theorem generatedFeasibleRootEightSlot_word_axis (c : ZMod 2) :
    rhoLocal generatedFifthRootEightLocal (conwayShortAxis (Sum.inl (0, 231)) c) =
      conwayShortAxis (Sum.inl (1, 248)) c := by
  rw [generatedFifthRootEightLocal, ← generatedAxisGlobalFifthShortWordFiber_local,
    generatedFeasibleFifthSlot_local_image, generatedFeasibleRootEightSlot_word_label,
    generatedFeasibleRootEightSlot_word_phase, zero_add]

/-- The counted root-eight prototype lies in the actual first-stabilizer orbit of the opposite
plus pair axis over `(16, 17)`. The explicit word is the literal word of the prototype. -/
theorem generatedFeasibleRootEightSlot_prototype_feasible :
    generatedFifthRootEightAxis ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (1, 248)) 0) (conwayShortAxis (Sum.inl (1, 248)) 1) := by
  have h1 := generatedFeasibleSixthSlot_orbit_local generatedFifthRootEightLocal
    generatedFeasibleRootEightSlot_fifth_feasible
  rw [generatedFeasibleRootEightSlot_word_axis, generatedFeasibleRootEightSlot_word_axis] at h1
  have hb := generatedFeasibleRootEightSlot_pair_feasible 248 1 0 1 1 (by decide)
  have h1' : rhoLocal generatedFifthRootEightLocal generatedFifthAxis ∈
      generatedFeasibleVectorOrbit (conwayShortAxis (Sum.inl (1, 248)) 1)
        (conwayShortAxis (Sum.inl (1, 248)) (1 + 1)) := h1
  have h2 := generatedFeasibleSixthSlot_orbit_map extraIntoGenerated
    (generatedFeasibleFifthSlot_rebase_symm hb h1')
  change sExtra _ ∈ generatedFeasibleVectorOrbit (sExtra _) (sExtra _) at h2
  have e1 : sExtra (conwayShortAxis (Sum.inl (1, 248)) 1) =
      conwayShortAxis (Sum.inl (1, 248)) 0 := by
    rw [generatedAxis_triality_pair_exact]
    rfl
  have e2 : sExtra (conwayShortAxis (Sum.inl (0, 248)) 1) =
      conwayShortAxis (Sum.inl (1, 248)) 1 := by
    rw [generatedAxis_triality_pair_exact]
    rfl
  rw [e1, e2] at h2
  rw [generatedFifthRootEightAxis_local_expression]
  exact h2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
