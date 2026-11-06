/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPairCentralizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerExact

/-! Identification of the actual global opposite-axis stabilizer
with its actual local stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The distinguished source pair axis is the positive signed-short axis in the same coordinates. -/
theorem conwayShortAxis_pair_zero (p : Fin 276) :
    conwayShortAxis (Sum.inl (0, p)) 0 = conwayAxis p := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [conwayShortAxis_encode, conwayAxis_encode, localAxis_matrix_outer]
  simp only [conwayShortAxisRaw, qSign_zero, mul_one]

private theorem localAxis_fixes_both (h : H) (p : Fin 276)
    (hh : h ∈ localAxisStabilizer p) (c : ZMod 2) :
    rhoLocal h (conwayShortAxis (Sum.inl (0, p)) c) =
      conwayShortAxis (Sum.inl (0, p)) c := by
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  have hfix : localGriessRepresentation f (conwayAxis p) = conwayAxis p := hh
  have hp := (localAxis_fiber_fixed_iff f p).mp hfix
  have hm : conwayMatrixAction f.val.2
      (Matrix.vecMulVec (griessShortVector (Sum.inl (0, p)))
        (griessShortVector (Sum.inl (0, p)))) =
      Matrix.vecMulVec (griessShortVector (Sum.inl (0, p)))
        (griessShortVector (Sum.inl (0, p))) := by
    rw [conwayMatrixAction_short_outer, hp.1]
  have hs := (localAxis_short_fixed_iff f (Sum.inl (0, p))).mpr hp
  rw [map_smul] at hs
  have hu : localShortRepresentation f (Pi.single (Sum.inl (0, p)) 1) =
      Pi.single (Sum.inl (0, p)) 1 :=
    (smul_right_injective _ (by norm_num : (-8 : ℝ) ≠ 0)) hs
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation f _) = _
  rw [localGriessRepresentation_encode, conwayShortAxis_encode,
    localConwayRawRepresentation_apply]
  simp only [conwayShortAxisRaw, map_smul, hm, hu, map_zero]

/-- Every actual local axis stabilizer element fixes either sign of its short axis. -/
theorem localAxisStabilizer_signedAxis_fixed (h : H) (p : Fin 276)
    (hh : h ∈ localAxisStabilizer p) (c : ZMod 2) :
    rhoLocal h (conwayShortAxis (Sum.inl (0, p)) c) =
      conwayShortAxis (Sum.inl (0, p)) c :=
  localAxis_fixes_both h p hh c

/-- The actual global subgroup fixing both opposite signed axes. -/
noncomputable def generatedShortAxisPairStabilizer (p : Fin 276) : Subgroup G :=
  MulAction.stabilizer G (conwayShortAxis (Sum.inl (0, p)) 0) ⊓
    MulAction.stabilizer G (conwayShortAxis (Sum.inl (0, p)) 1)

/-- Exact global pair-stabilizer identification, using full actual centralizer
recognition and the actual local signed-short coordinate action. -/
theorem generatedShortAxisPairStabilizer_eq_local (p : Fin 276) :
    generatedShortAxisPairStabilizer p = (localAxisStabilizer p).map localIntoGenerated := by
  apply le_antisymm
  · intro g hg
    obtain ⟨h, rfl⟩ := generated_fix_shortAxis_pair_local g (Sum.inl (0, p)) hg.1 hg.2
    refine ⟨h, ?_, rfl⟩
    change rhoLocal h (conwayAxis p) = conwayAxis p
    have hh := hg.1
    change rhoLocal h (conwayShortAxis (Sum.inl (0, p)) 0) =
      conwayShortAxis (Sum.inl (0, p)) 0 at hh
    simpa only [conwayShortAxis_pair_zero] using hh
  · rintro _ ⟨h, hh, rfl⟩
    exact ⟨localAxis_fixes_both h p hh 0, localAxis_fixes_both h p hh 1⟩

/-- The actual global pair stabilizer has the actual local stabilizer cardinality. -/
theorem generatedShortAxisPairStabilizer_card (p : Fin 276) :
    Nat.card (generatedShortAxisPairStabilizer p) = Nat.card (localAxisStabilizer p) := by
  rw [generatedShortAxisPairStabilizer_eq_local]
  exact Nat.card_congr ((localAxisStabilizer p).equivMapOfInjective
    localIntoGenerated localIntoGenerated_injective).symm.toEquiv

/-- The actual global pair stabilizer has its proved exact-sequence order,
with the genuine short stabilizer as the quotient. -/
theorem generatedShortAxisPairStabilizer_card_relation (p : Fin 276) :
    Nat.card (generatedShortAxisPairStabilizer p) =
      2 ^ 24 * Nat.card (co2ShortStabilizer (Sum.inl (0, p))) := by
  rw [generatedShortAxisPairStabilizer_card, localAxisStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
