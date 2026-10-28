/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhaseKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupport

/-! A genuine upper bound for the Q stabilizer of the actual octad axis.
Equality requires proving that every supported short class lies in the checked
eight-dimensional span; that assertion is not used here. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The selected octad's support is the original MOG coordinates eight to fifteen. -/
theorem generatedOctadBasisOctad_mask :
    golayEncodedMask (golayOctadLabel generatedOctadBasisOctad).val = 0xff00 := by
  have hlabel : golayOctadLabel generatedOctadBasisOctad = 3 :=
    congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨3, by decide +kernel⟩)
  rw [hlabel]
  decide +kernel

/-- All eight checked independent roots are genuine nonzero coordinates
of an actual transition on the selected octad. -/
theorem generatedOctadBasisLabel_supported (j : Fin 8) :
    generatedOctadShortSupport generatedOctadBasisOctad (generatedOctadBasisLabel j) := by
  fin_cases j <;>
    norm_num [generatedOctadBasisLabel, generatedOctadShortSupport, generatedOctadPairSupport,
      griessPairIndex_coordinates, generatedOctadBasisOctad_mask, Nat.testBit]

/-- The actual Q elements fixing this actual transitioned octad axis. -/
noncomputable def generatedOctadAxisQStabilizer (e : Fin 64) (c : ZMod 2) : Subgroup Q :=
  (MulAction.stabilizer H
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c))).comap inclQ

/-- An actual Q element fixing a vector has zero conjugation phase at each
nonzero short coordinate of that vector. -/
theorem generatedAxis_Q_fixed_short_phase (q : Q) (x : GriessSpace)
    (hfix : rhoLocal (inclQ q) x = x) (r : GriessShortIndex)
    (hr : (griessConwayEncode x).2.1 r ≠ 0) : localAxisQPhase r q = 1 := by
  have he := congrArg (fun y : GriessSpace => (griessConwayEncode y).2.1 r) hfix
  change (griessConwayEncode (localGriessRepresentation (localFiberIncl q) x)).2.1 r = _ at he
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at he
  have hd := localShortOperator_image (localFiberIncl q) (griessConwayEncode x).2.1 r
  change localShortOperator (localFiberIncl q) _ (griessShortPermutation 1 r) = _ at hd
  rw [map_one, Equiv.Perm.one_apply] at hd
  change localShortOperator (localFiberIncl q) (griessConwayEncode x).2.1 r = _ at he
  rw [hd] at he
  have hs : qSign (localShortPhase (localFiberIncl q) r) = 1 :=
    (mul_right_cancel₀ hr (he.trans (one_mul _).symm))
  have hp := (qSign_eq_one_iff _).mp hs
  rw [localAxisQPhase_eq_short_phase] at hp
  exact toAdd.injective hp

/-- Every actual Q stabilizer element satisfies all eight independent phase constraints. -/
theorem generatedOctadAxisQStabilizer_le_phase_kernel (e : Fin 64) (c : ZMod 2) :
    generatedOctadAxisQStabilizer e c ≤ generatedOctadBasisQPhases.ker := by
  intro q hq
  apply MonoidHom.mem_ker.mpr
  apply toAdd.injective
  funext j
  have hr := (generatedAxis_triality_octad_support_iff generatedOctadBasisOctad e c
    (generatedOctadBasisLabel j)).mpr (generatedOctadBasisLabel_supported j)
  have hp := generatedAxis_Q_fixed_short_phase q _ hq (generatedOctadBasisLabel j) hr
  change toAdd (localAxisQPhase (generatedOctadBasisLabel j) q) = 0
  rw [hp]
  rfl

/-- The actual Q stabilizer has at most 2^17 elements, without an assumed
orbit or an unverified spanning claim for its other 112 short coordinates. -/
theorem generatedOctadAxisQStabilizer_card_le (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedOctadAxisQStabilizer e c) ≤ 2 ^ 17 := by
  rw [← generatedOctadBasis_Q_phases_kernel_card]
  exact Subgroup.card_le_of_le (generatedOctadAxisQStabilizer_le_phase_kernel e c)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
