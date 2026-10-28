/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryAnchoredMatrixInvariant

/-! Genuine first-axis stabilizer separation of the secondary triality destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual orbit class under the original first-axis stabilizer. -/
def generatedFeasibleSecondaryAClass (x : GriessSpace) :
    generatedFeasibleLocalOrbitSpace generatedFeasiblePhysicalRootPair :=
  Quotient.mk (MulAction.orbitRel
    (localAxisStabilizer generatedFeasiblePhysicalRootPair) GriessSpace) x

/-- Equality of these classes is transport by the entire genuine first-axis stabilizer. -/
theorem generatedFeasibleSecondaryAClass_eq_iff (x y : GriessSpace) :
    generatedFeasibleSecondaryAClass x = generatedFeasibleSecondaryAClass y ↔
      ∃ h : localAxisStabilizer generatedFeasiblePhysicalRootPair,
        rhoLocal h.val x = y := by
  constructor
  · intro he
    have hh := MulAction.orbitRel_apply.mp (Quotient.exact' he)
    exact MulAction.mem_orbit_symm.mp hh
  · intro hh
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_symm.mp hh

/-- Actual containing-pair and outside-pair destinations have different A classes. -/
theorem generatedFeasibleContainingOutsideDestination_separate :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingOctadDestination ≠
      generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination := by
  intro he
  obtain ⟨h, hh⟩ := (generatedFeasibleSecondaryAClass_eq_iff _ _).mp he
  have hi := generatedFeasibleAnchoredMatrixPairing_invariant
    generatedFeasiblePhysicalRootPair h generatedFeasibleContainingOctadDestination
  rw [hh, generatedFeasibleContainingOctadDestination_anchored_pairing,
    generatedFeasibleOutsideOctadDestination_anchored_pairing] at hi
  norm_num at hi

/-- Both actual octad destinations have zero tensor coordinate. -/
theorem generatedFeasibleOctadDestination_tensor_zero (o : Fin 759) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) 0))).2.2 =
      0 := generatedAxis_triality_octad_tensor_zero o 0

/-- The original odd destination has a nonzero tensor coordinate. -/
theorem generatedFeasibleOddDestination_tensor_ne_zero :
    (griessConwayEncode generatedFeasibleSecondaryOddDestination).2.2 ≠ 0 := by
  exact generatedAxis_triality_odd_tensor_ne_zero 0 2 0

/-- Every actual octad triality class differs from the actual secondary odd class. -/
theorem generatedFeasibleOctadOddDestination_separate (o : Fin 759) :
    generatedFeasibleSecondaryAClass
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) 0)) ≠
      generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination := by
  intro he
  obtain ⟨h, hh⟩ := (generatedFeasibleSecondaryAClass_eq_iff _ _).mp he
  have hz := generatedAxis_local_preserves_tensor_zero h.val _
    (generatedFeasibleOctadDestination_tensor_zero o)
  rw [hh] at hz
  exact generatedFeasibleOddDestination_tensor_ne_zero hz

/-- The actual A action preserves the original signed-short catalogue. -/
theorem generatedFeasibleSecondaryA_preserves_signed
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair) (x : GriessSpace)
    (hx : x ∈ generatedSignedShortAxes) : rhoLocal h.val x ∈ generatedSignedShortAxes := by
  rw [← generatedAxisLocalOrbit_eq_signed (Sum.inl (0, 0)) 0] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  refine ⟨h.val * k, ?_⟩
  rw [rhoLocal.map_mul, LinearEquiv.mul_apply, hk]

/-- An actual octad triality destination cannot share an A class with a signed-short axis. -/
theorem generatedFeasibleOctadSignedDestination_separate (o : Fin 759)
    (r : GriessShortIndex) (c : ZMod 2) :
    generatedFeasibleSecondaryAClass (conwayShortAxis r c) ≠
      generatedFeasibleSecondaryAClass
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, 0))) 0)) := by
  intro he
  obtain ⟨h, hh⟩ := (generatedFeasibleSecondaryAClass_eq_iff _ _).mp he
  have hs := generatedFeasibleSecondaryA_preserves_signed h _ ⟨(r, c), rfl⟩
  rw [hh] at hs
  exact generatedAxis_triality_octad_not_signed o 0 hs

/-- The actual odd triality destination cannot share an A class with a signed-short axis. -/
theorem generatedFeasibleOddSignedDestination_separate (r : GriessShortIndex) (c : ZMod 2) :
    generatedFeasibleSecondaryAClass (conwayShortAxis r c) ≠
      generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination := by
  intro he
  obtain ⟨h, hh⟩ := (generatedFeasibleSecondaryAClass_eq_iff _ _).mp he
  have hs := generatedFeasibleSecondaryA_preserves_signed h _ ⟨(r, c), rfl⟩
  rw [hh] at hs
  exact generatedAxis_triality_odd_not_signed 0 2 0 hs

/-- The existing singleton opposite-axis and secondary signed-short A classes are distinct. -/
theorem generatedFeasibleAnchorSecondaryDestination_separate :
    generatedFeasibleSecondaryAClass
        (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 1) ≠
      generatedFeasibleSecondaryAClass
        (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) := by
  intro he
  obtain ⟨h, hh⟩ := (generatedFeasibleSecondaryAClass_eq_iff _ _).mp he
  rw [localAxisStabilizer_signedAxis_fixed h.val _ h.property 1,
    generatedFeasibleSecondaryAxis_eq_short] at hh
  have hi := @generatedAxis_signed_injective
    (Sum.inl (0, generatedFeasiblePhysicalRootPair), 1)
    (Sum.inl (1, generatedFeasiblePhysicalRootPair), 1) hh
  have hs := congrArg (fun z : GriessShortIndex × ZMod 2 => z.1) hi
  have hp := congrArg (fun z : Fin 2 × Fin 276 => z.1) (Sum.inl.inj hs)
  norm_num at hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
