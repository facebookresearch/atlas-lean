/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co2OrderShortStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalLocal

/-! The actual local stabilizer of Conway's pair axis, in fiber coordinates.
The subgroup is defined by its genuine descended Griess action on H. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The matrix coordinate of the axis is twice the outer square of its short vector. -/
theorem localAxis_matrix_outer (p : Fin 276) : conwayAxisMatrix p =
    (2 : ℝ) • Matrix.vecMulVec (griessShortVector (Sum.inl (0, p)))
      (griessShortVector (Sum.inl (0, p))) := by
  funext i j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [conwayAxisMatrix_rank_one, conwayAxis_short_outer]
  ring

/-- Fixing the nonzero short coordinate is equivalent to fixing its label and sign. -/
theorem localAxis_short_fixed_iff (f : localFiberSubgroup) (r : GriessShortIndex) :
    localShortRepresentation f ((-8 : ℝ) • Pi.single r 1) =
      (-8 : ℝ) • Pi.single r 1 ↔
      griessShortPermutation f.val.2 r = r ∧ localShortPhase f r = 0 := by
  classical
  constructor
  · intro h
    have he := congrFun h (griessShortPermutation f.val.2 r)
    change localShortOperator f ((-8 : ℝ) • Pi.single r 1)
      (griessShortPermutation f.val.2 r) = _ at he
    rw [localShortOperator_image] at he
    have hp : griessShortPermutation f.val.2 r = r := by
      by_contra hp
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, ite_true, hp,
        ite_false, mul_zero, mul_one] at he
      have hs := qSign_sq (localShortPhase f r)
      nlinarith
    refine ⟨hp, (qSign_eq_one_iff _).mp ?_⟩
    simp only [hp, Pi.smul_apply, smul_eq_mul, Pi.single_apply, ite_true, mul_one] at he
    linarith
  · rintro ⟨hp, hphase⟩
    funext t
    obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective t
    change localShortOperator f ((-8 : ℝ) • Pi.single r 1)
      (griessShortPermutation f.val.2 s) = _
    rw [localShortOperator_image]
    by_cases hs : s = r
    · subst s
      simp [hp, hphase]
    · have ht : griessShortPermutation f.val.2 s ≠ r := by
        intro h
        exact hs ((griessShortPermutation f.val.2).injective (h.trans hp.symm))
      simp [hs, ht]

/-- The fiber action fixes Conway's axis exactly when its short label and phase are fixed. -/
theorem localAxis_fiber_fixed_iff (f : localFiberSubgroup) (p : Fin 276) :
    localGriessRepresentation f (conwayAxis p) = conwayAxis p ↔
      griessShortPermutation f.val.2 (Sum.inl (0, p)) = Sum.inl (0, p) ∧
        localShortPhase f (Sum.inl (0, p)) = 0 := by
  constructor
  · intro h
    have he := congrArg griessConwayEncode h
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
      conwayAxis_encode] at he
    exact (localAxis_short_fixed_iff f _).mp (congrArg (fun x : ConwayRawSpace => x.2.1) he)
  · intro h
    have hs := (localAxis_short_fixed_iff f _).mpr h
    have hm : conwayMatrixAction f.val.2 (conwayAxisMatrix p) = conwayAxisMatrix p := by
      rw [localAxis_matrix_outer, map_smul, conwayMatrixAction_short_outer, h.1]
    have he : griessConwayEncode (localGriessRepresentation f (conwayAxis p)) =
        griessConwayEncode (conwayAxis p) := by
      rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply,
        conwayAxis_encode, hm, hs, map_zero]
    have hd := congrArg griessConwayDecode he
    simpa only [griessConwayDecode_encode] using hd

/-- The actual local group elements fixing the specified pair axis. -/
noncomputable def localAxisStabilizer (p : Fin 276) : Subgroup H where
  carrier := {h | rhoLocal h (conwayAxis p) = conwayAxis p}
  one_mem' := by change rhoLocal 1 (conwayAxis p) = conwayAxis p; rw [map_one]; rfl
  mul_mem' := by
    intro h k hh hk
    change rhoLocal h (conwayAxis p) = conwayAxis p at hh
    change rhoLocal k (conwayAxis p) = conwayAxis p at hk
    change rhoLocal (h * k) (conwayAxis p) = conwayAxis p
    rw [map_mul, LinearEquiv.mul_apply, hk, hh]
  inv_mem' := by
    intro h hh
    change rhoLocal h (conwayAxis p) = conwayAxis p at hh
    change rhoLocal h⁻¹ (conwayAxis p) = conwayAxis p
    apply (rhoLocal h).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact hh.symm

/-- This criterion is stated for actual quotient membership, using any fiber representative. -/
theorem localAxisStabilizer_mk_iff (f : localFiberSubgroup) (p : Fin 276) :
    localFiberIntoH f ∈ localAxisStabilizer p ↔
      griessShortPermutation f.val.2 (Sum.inl (0, p)) = Sum.inl (0, p) ∧
        localShortPhase f (Sum.inl (0, p)) = 0 :=
  localAxis_fiber_fixed_iff f p

/-- The short-label action of the descended local projection is the fiber Leech action. -/
theorem localAxis_projection_short_mk (f : localFiberSubgroup) (r : GriessShortIndex) :
    co1ShortPermutation (projH (localFiberIntoH f)) r =
      griessShortPermutation f.val.2 r := by
  change co1ShortPermutation (QuotientGroup.mk f.val.2) r = _
  rw [co1ShortPermutation_mk]

/-- The genuine local axis stabilizer projects into the genuine short-class stabilizer. -/
theorem localAxisStabilizer_projection_mem (p : Fin 276) (h : localAxisStabilizer p) :
    projH h.val ∈ co2ShortStabilizer (Sum.inl (0, p)) := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hmem : localFiberIntoH f ∈ localAxisStabilizer p := by rw [hf]; exact h.property
  change co1ShortPermutation (projH h.val) (Sum.inl (0, p)) = Sum.inl (0, p)
  rw [← hf, localAxis_projection_short_mk]
  exact ((localAxisStabilizer_mk_iff f p).mp hmem).1

/-- Restriction of the actual exact-sequence projection to the actual axis stabilizer. -/
noncomputable def localAxisStabilizerProjection (p : Fin 276) :
    localAxisStabilizer p →* co2ShortStabilizer (Sum.inl (0, p)) :=
  (projH.comp (localAxisStabilizer p).subtype).codRestrict _
    (localAxisStabilizer_projection_mem p)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
