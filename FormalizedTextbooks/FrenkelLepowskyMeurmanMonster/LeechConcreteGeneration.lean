/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Constructive generation of the actual Leech lattice isometry group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechCoordinateFrameClass
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechFrameMonomial

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The coordinate-frame vectors as elements of the actual integral lattice. -/
def leechCoordinateFrameLattice (i : Fin 24) : leechIntegral :=
  ⟨leechCoordinateFrameVector i, leechCoordinateFrameVector_mem i⟩

private def frameDifference (i : Fin 24) : Fin 24 → ℤ :=
  fun j => 4 * ((Pi.single i 1 : Fin 24 → ℤ) j - (Pi.single 0 1 : Fin 24 → ℤ) j)

private theorem frameDifference_mem (i : Fin 24) : frameDifference i ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro j
    simp only [frameDifference, Int.cast_mul, Int.cast_sub, Int.cast_ofNat, Pi.zero_apply,
      ZMod.val_zero, Nat.cast_zero, mul_zero, Int.cast_zero, add_zero,
      show (4 : ZMod 4) = 0 by decide, zero_mul]
  · have hs : ∑ j, frameDifference i j = 0 := by
      simp only [frameDifference, ← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [Pi.single_apply]
    rw [hs]
    norm_num

private theorem frameDifference_double (i : Fin 24) :
    leechCoordinateFrameLattice i = (2 : ℕ) • (⟨frameDifference i,
      frameDifference_mem i⟩ : leechIntegral) + leechCoordinateFrameLattice 0 := by
  apply Subtype.ext
  ext j
  simp only [two_nsmul, Submodule.coe_add, Pi.add_apply, leechCoordinateFrameLattice,
    leechCoordinateFrameVector, frameDifference, Pi.single_apply]
  split_ifs <;> norm_num

private theorem frameEmbedding (i : Fin 24) :
    leechCoordinateEmbedding (leechCoordinateFrameVector i) =
      (8 / Real.sqrt 8 : ℝ) • (Pi.single i 1 : Fin 24 → ℝ) := by
  ext j
  by_cases h : j = i <;>
    simp [leechCoordinateEmbedding, leechCoordinateFrameVector, h]

/-- Fixing the distinguished frame vector forces preservation of the whole signed frame. -/
theorem leech_fix_frame_mem_monomial (e : leechIsomSubgroup)
    (hfix : leechIntegralAction e (leechCoordinateFrameLattice 0) =
      leechCoordinateFrameLattice 0) : e ∈ golayMonomialSubgroup := by
  apply leechFrame_mem_monomial e
  intro i
  let w : leechIntegral := ⟨frameDifference i, frameDifference_mem i⟩
  have he := congrArg (leechIntegralAction e) (frameDifference_double i)
  rw [map_add, map_nsmul, hfix] at he
  have hu : (leechIntegralAction e (leechCoordinateFrameLattice i)).val =
      fun j => 2 * (leechIntegralAction e w).val j + leechCoordinateFrameVector 0 j := by
    funext j
    have hh := congrArg (fun v : leechIntegral => v.val j) he
    simpa only [two_nsmul, Submodule.coe_add, Pi.add_apply, leechCoordinateFrameLattice,
      two_mul] using hh
  obtain ⟨j, hj⟩ := leechNormEight_coordinate_frame_class
    (leechIntegralAction e (leechCoordinateFrameLattice i)) (leechIntegralAction e w)
    (by rw [leechIntegralAction_squareSum]; exact leechCoordinateFrameVector_square i) hu
  have hc : (8 / Real.sqrt 8 : ℝ) ≠ 0 :=
    div_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hgeom := leechIntegralAction_embedding e (leechCoordinateFrameLattice i)
  change leechCoordinateEmbedding (leechIntegralAction e (leechCoordinateFrameLattice i)).val =
    e.val (leechCoordinateEmbedding (leechCoordinateFrameVector i)) at hgeom
  refine ⟨j, ?_⟩
  rcases hj with hj | hj
  · refine ⟨0, ?_⟩
    rw [hj, frameEmbedding, frameEmbedding, map_smul] at hgeom
    rw [qSign_zero, one_smul]
    ext k
    have hh := congrFun hgeom k
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    exact (mul_left_cancel₀ hc hh).symm
  · refine ⟨1, ?_⟩
    rw [hj, map_neg, frameEmbedding, frameEmbedding, map_smul] at hgeom
    rw [qSign_one, neg_one_smul]
    ext k
    have hh := congrFun hgeom k
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at hh
    apply mul_left_cancel₀ hc
    simpa only [Pi.neg_apply, mul_neg] using hh.symm

/-- Every genuine signed Golay permutation belongs to the concrete generator group. -/
theorem golayMonomial_le_concrete : golayMonomialSubgroup ≤ leechConcreteGeneratorSubgroup := by
  rintro e ⟨d, p, rfl⟩
  exact leechConcreteGeneratorSubgroup.mul_mem (golaySignIsometry_mem_concrete d)
    (golayPermutationIsometry_mem_concrete p)

/-- Actual Golay signs, Golay permutations, and the three-bases isometry generate all Co₀.
The proof reduces an arbitrary norm-eight image, then recognizes its coordinate-frame stabilizer. -/
theorem leechConcreteGeneratorSubgroup_eq_top : leechConcreteGeneratorSubgroup = ⊤ := by
  apply top_unique
  intro e _
  obtain ⟨k, hk, haxis⟩ := leechNormEight_concrete_transitive
    (leechIntegralAction e (leechCoordinateFrameLattice 0))
    (by rw [leechIntegralAction_squareSum]; exact leechCoordinateFrameVector_square 0)
  have hfix : leechIntegralAction (k * e) (leechCoordinateFrameLattice 0) =
      leechCoordinateFrameLattice 0 := by
    apply Subtype.ext
    simpa only [map_mul, LinearEquiv.mul_apply, leechCoordinateFrameLattice,
      leechCoordinateFrameVector] using haxis
  have hke := golayMonomial_le_concrete (leech_fix_frame_mem_monomial (k * e) hfix)
  have hh := leechConcreteGeneratorSubgroup.mul_mem
    (leechConcreteGeneratorSubgroup.inv_mem hk) hke
  simpa only [inv_mul_cancel_left] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
