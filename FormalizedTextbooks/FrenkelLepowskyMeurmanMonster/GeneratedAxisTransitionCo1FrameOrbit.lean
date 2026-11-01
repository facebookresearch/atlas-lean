/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaClass
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! The genuine Co₁ orbit and stabilizer of the source Ω class. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

/-- The actual Conway quotient action in the proved binary lattice coordinates. -/
noncomputable instance co1FrameClassAction : MulAction Co1 (Fin 24 → ZMod 2) :=
  MulAction.compHom (Fin 24 → ZMod 2) co1BinaryAction

/-- The two quotient coordinate descriptions give the same actual orbit. -/
noncomputable def co1OmegaFrameOrbitEquiv :
    MulAction.orbit leechIsomSubgroup (leechReduction (leechCoordinateFrameLattice 0)) ≃
      MulAction.orbit Co1 (toAdd (qQuotHom sourceOmegaQ)) where
  toFun u := ⟨leechHyperbolicCoordinates u.val, by
    obtain ⟨e, he⟩ := u.property
    refine ⟨QuotientGroup.mk e, ?_⟩
    change leechBinaryAction e (toAdd (qQuotHom sourceOmegaQ)) = _
    rw [sourceOmegaQ_eq_frame_class, leechBinaryAction_coordinates]
    exact congrArg leechHyperbolicCoordinates he⟩
  invFun v := ⟨leechHyperbolicCoordinates.symm v.val, by
    obtain ⟨c, hc⟩ := v.property
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective signsSubgroup c
    refine ⟨e, ?_⟩
    apply leechHyperbolicCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    change leechBinaryAction e (toAdd (qQuotHom sourceOmegaQ)) = v.val at hc
    exact (leechBinaryAction_coordinates e
      (leechReduction (leechCoordinateFrameLattice 0))).symm.trans
      ((congrArg (leechBinaryAction e) sourceOmegaQ_eq_frame_class).symm.trans hc)⟩
  left_inv u := by
    apply Subtype.ext
    exact leechHyperbolicCoordinates.symm_apply_apply u.val
  right_inv v := by
    apply Subtype.ext
    exact leechHyperbolicCoordinates.apply_symm_apply v.val

/-- The actual binary Ω orbit has exactly 8,292,375 elements. -/
theorem co1OmegaFrame_orbit_card :
    Nat.card (MulAction.orbit Co1 (toAdd (qQuotHom sourceOmegaQ))) = 8292375 := by
  rw [← Nat.card_congr co1OmegaFrameOrbitEquiv]
  exact leechFrameClass_orbit_card

/-- The actual Conway subgroup fixing Ω in the binary quotient. -/
noncomputable def co1OmegaFrameStabilizer : Subgroup Co1 :=
  MulAction.stabilizer Co1 (toAdd (qQuotHom sourceOmegaQ))

/-- The genuine binary Ω stabilizer has its proved frame-orbit index. -/
theorem co1OmegaFrameStabilizer_index : co1OmegaFrameStabilizer.index = 8292375 := by
  rw [co1OmegaFrameStabilizer, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  exact co1OmegaFrame_orbit_card

/-- The actual binary Ω stabilizer has order 2¹¹ times the Golay permutation group order. -/
theorem co1OmegaFrameStabilizer_card :
    Nat.card co1OmegaFrameStabilizer = 501397585920 := by
  have h := co1OmegaFrameStabilizer.card_mul_index
  rw [co1OmegaFrameStabilizer_index, co1_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 8292375) h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
