/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientDoubleCount
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryPhysicalGeometry

/-! The actual signed-short axes orthogonal to the first axis.

For the first axis over the physical root `4(e₀ - e₁)`, an actual signed-short axis is
orthogonal to it exactly when its short vector is perpendicular to the root, or when it
is the opposite signed axis. Hence 93151 of the 196560 actual signed-short axes are
orthogonal to every actual signed-short axis, and the first local orbit contains exactly
93151 orthogonal partners of the first axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem contraction_outer (v w : Fin 24 → ℝ) :
    axisMatrixContraction w ((2 : ℝ) • Matrix.vecMulVec v v) = 2 * (stdPairingFun v w) ^ 2 := by
  have hP : (stdPairingFun v w) ^ 2 = ∑ i, ∑ j, (v i * w i) * (v j * w j) := by
    rw [sq, stdPairingFun, Finset.sum_mul_sum]
  rw [hP, Finset.mul_sum]
  unfold axisMatrixContraction
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

/-- The pairing of every actual signed-short axis with the first physical axis. -/
theorem generatedFeasibleAmbient_first_form (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
      4 * (stdPairingFun (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
          (griessShortVector r)) ^ 2 +
        64 * qSign c * (if r = Sum.inl (0, generatedFeasiblePhysicalRootPair) then 1 else 0) := by
  rw [generatedFeasibleAmbient_axis_form, conwayShortAxis_encode]
  have hs : (conwayShortAxisRaw (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0).2.1 r =
      -8 * (if r = Sum.inl (0, generatedFeasiblePhysicalRootPair) then 1 else 0) := by
    simp only [conwayShortAxisRaw, Pi.smul_apply, Pi.single_apply, smul_eq_mul, qSign_zero]
    split_ifs <;> ring
  rw [hs]
  simp only [conwayShortAxisRaw]
  rw [contraction_outer]
  ring

private theorem root_not_mem :
    Sum.inl (0, generatedFeasiblePhysicalRootPair) ∉ generatedFeasibleOrthogonalShortLabels := by
  rw [generatedFeasibleOrthogonalShortLabels_mem]
  simp [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates]

/-- Orthogonality to the first axis: a perpendicular short vector, or the opposite axis. -/
theorem generatedFeasibleAmbient_first_form_eq_zero_iff (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c)
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) = 0 ↔
      r ∈ generatedFeasibleOrthogonalShortLabels ∨
        (r = Sum.inl (0, generatedFeasiblePhysicalRootPair) ∧ c = 1) := by
  rw [generatedFeasibleAmbient_first_form]
  by_cases hr : r = Sum.inl (0, generatedFeasiblePhysicalRootPair)
  · subst hr
    have hn : stdPairingFun (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
        (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair))) = 4 := by
      unfold stdPairingFun
      exact griessShortVector_norm_sq _
    simp only [hn, ↓reduceIte, root_not_mem, false_or, true_and, mul_one]
    rcases (show c = 0 ∨ c = 1 by fin_cases c <;> simp) with rfl | rfl
    · simp only [qSign_zero]
      constructor
      · intro h
        norm_num at h
      · intro h
        exact absurd h zero_ne_one
    · simp only [qSign_one]
      norm_num
  · simp only [hr, ↓reduceIte, false_and, or_false, mul_zero, add_zero]
    rw [generatedFeasibleOrthogonalShortLabels_mem, ← generatedFeasiblePhysicalRoot_orthogonal_iff]
    constructor
    · intro h
      have hsq : (stdPairingFun (griessShortVector (Sum.inl (0, generatedFeasiblePhysicalRootPair)))
          (griessShortVector r)) ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    · intro h
      rw [h]
      ring

/-- Exactly 93151 actual signed-short axes are orthogonal to the first physical axis. -/
theorem generatedFeasibleAmbientAxisZeroCount_first :
    generatedFeasibleAmbientAxisZeroCount
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) = 93151 := by
  classical
  have hset : {p : GriessShortIndex × ZMod 2 | griessForm (conwayShortAxis p.1 p.2)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) = 0} =
      ((generatedFeasibleOrthogonalSignedShortLabels ∪
        {(Sum.inl (0, generatedFeasiblePhysicalRootPair), 1)} :
          Finset (GriessShortIndex × ZMod 2)) : Set (GriessShortIndex × ZMod 2)) := by
    ext ⟨r, c⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_union, Finset.coe_singleton, Set.mem_union,
      Set.mem_singleton_iff, Finset.mem_coe, generatedFeasibleOrthogonalSignedShortLabels,
      Finset.mem_product, Finset.mem_univ, and_true, Prod.mk.injEq]
    exact generatedFeasibleAmbient_first_form_eq_zero_iff r c
  have hdisj : Disjoint generatedFeasibleOrthogonalSignedShortLabels
      {(Sum.inl (0, generatedFeasiblePhysicalRootPair), (1 : ZMod 2))} := by
    rw [Finset.disjoint_singleton_right]
    simp [generatedFeasibleOrthogonalSignedShortLabels, root_not_mem]
  change Nat.card ↥{p : GriessShortIndex × ZMod 2 | griessForm (conwayShortAxis p.1 p.2)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) = 0} = 93151
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj,
    generatedFeasibleOrthogonalSignedShortLabels_card, Finset.card_singleton]

/-- Every actual signed-short axis has exactly 93151 orthogonal signed-short axes. -/
theorem generatedFeasibleAmbientAxisZeroCount_signedShort (r : GriessShortIndex) (c : ZMod 2) :
    generatedFeasibleAmbientAxisZeroCount (conwayShortAxis r c) = 93151 := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive
    (Sum.inl (0, generatedFeasiblePhysicalRootPair)) r 0 c
  rw [← hh]
  exact (generatedFeasibleAmbientAxisZeroCount_smul h _).trans
    generatedFeasibleAmbientAxisZeroCount_first

/-- The first actual local orbit contains exactly 93151 orthogonal partners of any
actual signed-short axis. -/
theorem generatedFeasibleAmbient_first_orbit_orthogonal_card (r : GriessShortIndex)
    (c : ZMod 2) (s : GriessShortIndex) (d : ZMod 2) :
    Nat.card {x | x ∈ MulAction.orbit H (conwayShortAxis s d) ∧
      griessForm (conwayShortAxis r c) x = 0} = 93151 := by
  have h := generatedFeasibleAmbient_local_double_count r c (conwayShortAxis s d)
  have hc : Nat.card (MulAction.orbit H (conwayShortAxis s d)) = 196560 := by
    rw [generatedFeasibleAmbient_axis_local_orbit, generatedSignedShortAxes_card]
  rw [hc, generatedFeasibleAmbientAxisZeroCount_signedShort] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
