/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOddDestinationFrameCatalogue

/-! Genuine frame-preserving Mathieu and Golay transport of all 506 preferred root lines. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Actual fixation of either integral frame orientation fixes the original frame line. -/
theorem generatedFeasibleOddFrame_signed_mem (g : leechIsomSubgroup)
    (hg : leechIntegralAction g (leechCoordinateFrameLattice 0) =
        leechCoordinateFrameLattice 0 ∨
      leechIntegralAction g (leechCoordinateFrameLattice 0) = -leechCoordinateFrameLattice 0) :
    g ∈ generatedNormEightLineStabilizer := by
  rw [generatedNormEightLineStabilizer_mem, ← generatedNormEightLineMatrix_action]
  symm
  apply (generatedNormEightLineMatrix_eq_iff _ _).mpr
  rcases hg with hp | hn
  · left
    exact Subtype.ext hp
  · right
    exact Subtype.ext hn

set_option maxHeartbeats 8000000 in
-- Bind the original three-point word and all pair coordinates before preferred-class transport.
/-- Every actual frame-orthogonal preferred pair has an original monomial transport to the prototype
preserving the original norm-eight frame line. -/
theorem generatedFeasibleOddFrame_monomial (s : Fin 2) (p : Fin 276)
    (hp : griessCoordinatePair p ∈ generatedFeasibleOddFramePairs) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      e ∈ generatedNormEightLineStabilizer ∧
      griessShortPermutation e (Sum.inl (s, p)) =
        Sum.inl (0, generatedFeasibleOddDestinationPair) := by
  let a := (griessCoordinatePair p).1
  let b := (griessCoordinatePair p).2
  have hab : a ≠ b := griessCoordinatePair_ne p
  have houtside := (Finset.mem_filter.mp hp).2
  have ht : Function.Injective (![0, a, b] : Fin 3 → Fin 24) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [a, b]
  obtain ⟨q, hq⟩ := leechRootedA2_three_transitive ![0, a, b] ![0, 1, 2]
    ht (by intro i j he; fin_cases i <;> fin_cases j <;> simp_all)
  have hq0 : q.val 0 = 0 := hq 0
  have hqa : q.val a = 1 := hq 1
  have hqb : q.val b = 2 := hq 2
  let u := griessShortLatticeVector (Sum.inl (s, p))
  let v := leechIntegralAction (golayPermutationIsometry q) u
  have hv (i : Fin 24) : v.val i =
      4 * (if i = 1 then 1 else 0) + (if s = 0 then -4 else 4) * (if i = 2 then 1 else 0) := by
    change (leechIntegralAction (golayPermutationIsometry q) u).val i = _
    rw [leechIntegralAction_golayPermutation]
    have ha : q.val.symm i = a ↔ i = 1 := by rw [Equiv.symm_apply_eq, hqa]
    have hb : q.val.symm i = b ↔ i = 2 := by rw [Equiv.symm_apply_eq, hqb]
    simp only [golayIntegerPermute, u, griessShortLatticeVector, griessShortIntegral,
      a, b, ha, hb]
  let bits : Fin 4 → ZMod 2 := ![0, 0, if s = 0 then 0 else 1, 0]
  obtain ⟨d, hd⟩ := golayCode_four_coordinate_surjective
    (fun j : Fin 4 => Fin.castAdd 20 j)
    (by intro i j he; exact Fin.ext (congrArg (fun k : Fin 24 => k.val) he)) bits
  have hd1 : d.val 1 = 0 := congrFun hd 1
  have hd2 : d.val 2 = if s = 0 then 0 else 1 := congrFun hd 2
  have hpos : (leechIntegralAction (golaySignIsometry d) v).val =
      griessShortIntegral (Sum.inl (0, generatedFeasibleOddDestinationPair)) := by
    rw [leechIntegralAction_golaySign]
    funext i
    change (if d.val i = 0 then v.val i else -v.val i) = _
    rw [hv]
    simp only [griessShortIntegral, generatedFeasibleOddDestinationPair_coordinates, ite_true]
    by_cases h1 : i = 1
    · subst i
      simp [hd1]
    · by_cases h2 : i = 2
      · subst i
        rw [hd2]
        fin_cases s <;> norm_num
      · simp [h1, h2]
  let e := golaySignIsometry d * golayPermutationIsometry q
  have he : e ∈ golayMonomialSubgroup := ⟨d, q, rfl⟩
  have hframe : leechIntegralAction e (leechCoordinateFrameLattice 0) =
      leechCoordinateFrameLattice 0 ∨
      leechIntegralAction e (leechCoordinateFrameLattice 0) = -leechCoordinateFrameLattice 0 := by
    have hpframe : leechIntegralAction (golayPermutationIsometry q)
        (leechCoordinateFrameLattice 0) = leechCoordinateFrameLattice 0 := by
      apply Subtype.ext
      rw [leechIntegralAction_golayPermutation]
      funext i
      have hi : q.val.symm i = 0 ↔ i = 0 := by rw [Equiv.symm_apply_eq, hq0]
      simp only [golayIntegerPermute, leechCoordinateFrameLattice,
        leechCoordinateFrameVector, Pi.single_apply, hi]
    change leechIntegralAction (golaySignIsometry d * golayPermutationIsometry q) _ = _ ∨ _
    rw [map_mul, LinearEquiv.mul_apply, hpframe]
    by_cases hd0 : d.val 0 = 0
    · left
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      by_cases hi : i = 0 <;> simp [golayIntegerSign, leechCoordinateFrameLattice,
        leechCoordinateFrameVector, hi, hd0]
    · right
      apply Subtype.ext
      rw [leechIntegralAction_golaySign]
      funext i
      by_cases hi : i = 0 <;> simp [golayIntegerSign, leechCoordinateFrameLattice,
        leechCoordinateFrameVector, hi, hd0]
  refine ⟨e, he, generatedFeasibleOddFrame_signed_mem e hframe, ?_⟩
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  left
  apply Subtype.ext
  rw [map_mul, LinearEquiv.mul_apply]
  exact hpos


private theorem frame_pair_zero (s : Fin 2) (a b : Fin 24) (hab : a < b) :
    (4 * (if (0 : Fin 24) = a then (1 : ℤ) else 0) +
      (if s = 0 then -4 else 4) * (if (0 : Fin 24) = b then 1 else 0) = 0) ↔
      a ≠ 0 ∧ b ≠ 0 := by
  revert s a b
  decide +kernel

private theorem frame_image_zero (g : leechIsomSubgroup)
    (hg : g ∈ generatedNormEightLineStabilizer) (u : leechIntegral) (hu : u.val 0 = 0) :
    (leechIntegralAction g u).val 0 = 0 := by
  have hm := (generatedNormEightLineStabilizer_mem g).mp hg
  rw [← generatedNormEightLineMatrix_action] at hm
  have hp := leechRootedA2_integral_pairing_action g u (leechCoordinateFrameLattice 0)
  have hz : leechIntegralPairing u.val (leechCoordinateFrameLattice 0).val = 0 := by
    change u.val ⬝ᵥ Pi.single 0 8 = 0
    rw [dotProduct_single, hu, zero_mul]
  rw [hz] at hp
  rcases (generatedNormEightLineMatrix_eq_iff _ _).mp hm.symm with he | he
  · have hf : leechIntegralAction g (leechCoordinateFrameLattice 0) =
        leechCoordinateFrameLattice 0 := congrArg Subtype.val he
    rw [hf] at hp
    change (leechIntegralAction g u).val ⬝ᵥ Pi.single 0 8 = 0 at hp
    rw [dotProduct_single] at hp
    omega
  · have hf : leechIntegralAction g (leechCoordinateFrameLattice 0) =
        -leechCoordinateFrameLattice 0 := congrArg Subtype.val he
    rw [hf] at hp
    change (leechIntegralAction g u).val ⬝ᵥ -Pi.single 0 8 = 0 at hp
    rw [dotProduct_neg, dotProduct_single] at hp
    omega

/-- Every actual frame-line fixer preserves the genuine preferred outside-pair catalogue. -/
theorem generatedFeasibleOddFrame_image (g : leechIsomSubgroup)
    (hg : g ∈ generatedNormEightLineStabilizer) (r : GriessShortIndex)
    (hr : r ∈ generatedFeasibleOddFrameShortLines) :
    griessShortPermutation g r ∈ generatedFeasibleOddFrameShortLines := by
  obtain ⟨s, p, rfl, hp⟩ := hr
  obtain ⟨t, q, hq⟩ := generatedAxis_monomial_preserves_pair g
    (generatedNormEightLineStabilizer_le_monomial hg) s p
  refine ⟨t, q, hq, ?_⟩
  have hout := (Finset.mem_filter.mp hp).2
  have hz : (griessShortLatticeVector (Sum.inl (s, p))).val 0 = 0 := by
    simp [griessShortLatticeVector, griessShortIntegral, hout.2.1.symm, hout.2.2.symm]
  have hzero := frame_image_zero g hg _ hz
  have hsign := generatedE8Short_integral_sign g (Sum.inl (s, p))
  rw [hq] at hsign
  have hqzero : griessShortIntegral (Sum.inl (t, q)) 0 = 0 := by
    rcases hsign with he | he
    · rw [he] at hzero
      exact hzero
    · rw [he] at hzero
      change -griessShortIntegral (Sum.inl (t, q)) 0 = 0 at hzero
      omega
  have hlt := (Finset.mem_filter.mp (griessCoordinatePairEquiv q).property).2
  have houtq := (frame_pair_zero t _ _ hlt).mp hqzero
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, houtq⟩

/-- The original frame-line group's orbit of the genuine target root has exactly 506 lines. -/
theorem generatedFeasibleOddFrame_target_orbit :
    MulAction.orbit generatedNormEightLineStabilizer
      (Sum.inl (0, generatedFeasibleOddDestinationPair) : GriessShortIndex) =
      generatedFeasibleOddFrameShortLines := by
  ext r
  constructor
  · rintro ⟨g, rfl⟩
    exact generatedFeasibleOddFrame_image g.val g.property _ generatedFeasibleOddFrame_target_mem
  · rintro ⟨s, p, rfl, hp⟩
    obtain ⟨g, _, hg, hgr⟩ := generatedFeasibleOddFrame_monomial s p hp
    refine ⟨⟨g⁻¹, generatedNormEightLineStabilizer.inv_mem hg⟩, ?_⟩
    change griessShortPermutation g⁻¹ _ = _
    rw [← hgr, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
