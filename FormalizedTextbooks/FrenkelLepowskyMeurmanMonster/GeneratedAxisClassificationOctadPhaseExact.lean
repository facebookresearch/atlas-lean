/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadIntegralSpan

/-! The actual octad-axis Q stabilizer is the eight-phase kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The binary conjugation functional of an actual extraspecial element. -/
def generatedOctadQCommuteLinear (q : Q) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := qBeta (toAdd q.base) v + qBeta v (toAdd q.base)
  map_add' u v := by rw [qBeta_add_right, qBeta_add_left]; abel
  map_smul' a v := by
    simp only [qBeta_smul_right, qBeta_smul_left, smul_add, RingHom.id_apply]

/-- Zero phase on the checked basis forces zero phase on every actual
supported short lift, by its proved integer and binary spanning expression. -/
theorem generatedOctad_phase_kernel_supported (q : Q)
    (hq : q ∈ generatedOctadBasisQPhases.ker) (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    localAxisQPhase r q = 1 := by
  have hb (j : Fin 8) : generatedOctadQCommuteLinear q
      (generatedOctadBasisBinaryMatrix.col j) = 0 := by
    have hz := congrArg (fun m : Multiplicative (Fin 8 → ZMod 2) => toAdd m j)
      (MonoidHom.mem_ker.mp hq)
    change toAdd (localAxisQPhase (generatedOctadBasisLabel j) q) = 0 at hz
    change qBeta (toAdd q.base) (toAdd (griessShortQ (generatedOctadBasisLabel j)).base) +
      qBeta (toAdd (griessShortQ (generatedOctadBasisLabel j)).base) (toAdd q.base) = 0 at hz
    rw [generatedOctadBasis_actual_base] at hz
    exact hz
  obtain ⟨a, ha⟩ := generatedOctadShortSupport_binary_span r hr
  have hm : generatedOctadBasisBinaryMatrix *ᵥ a =
      ∑ j, a j • generatedOctadBasisBinaryMatrix.col j := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.col_apply]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  apply toAdd.injective
  change generatedOctadQCommuteLinear q (toAdd (griessShortQ r).base) = 0
  rw [← ha]
  change generatedOctadQCommuteLinear q (generatedOctadBasisBinaryMatrix *ᵥ a) = 0
  rw [hm, map_sum]
  simp only [map_smul, hb, smul_zero, Finset.sum_const_zero]

/-- Every signed-octad transition has zero tensor coordinates, on the actual dictionary. -/
theorem generatedAxis_triality_octad_tensor_zero_all
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.2 = 0 := by
  funext t i
  simp [griessConwayEncode, sExtra, griessTriality, conwayShortAxis, griessConwayDecode,
    conwayShortAxisRaw, trialityBlockAction, trialityCycleAction, trialityCycle]

/-- All eight zero phases suffice to fix the actual octad transition,
including its matrix, short, and tensor coordinates. -/
theorem generatedOctad_phase_kernel_le_axis_stabilizer (e : Fin 64) (c : ZMod 2) :
    generatedOctadBasisQPhases.ker ≤ generatedOctadAxisQStabilizer e c := by
  intro q hq
  change rhoLocal (inclQ q)
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c)) = _
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation (localFiberIncl q) _) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  · apply Prod.ext
    · ext r
      have hd := localShortOperator_image (localFiberIncl q)
        (griessConwayEncode (sExtra
          (conwayShortAxis (Sum.inr (Sum.inl (generatedOctadBasisOctad, e))) c))).2.1 r
      change localShortOperator (localFiberIncl q) _ (griessShortPermutation 1 r) = _ at hd
      rw [map_one, Equiv.Perm.one_apply] at hd
      change localShortOperator (localFiberIncl q) _ r = _
      rw [hd]
      by_cases hr : generatedOctadShortSupport generatedOctadBasisOctad r
      · have hp := generatedOctad_phase_kernel_supported q hq r hr
        have hz : localShortPhase (localFiberIncl q) r = 0 := by
          rw [localAxisQPhase_eq_short_phase, hp]
          rfl
        rw [hz, qSign_zero, one_mul]
      · have hz := not_ne_iff.mp
          (mt (generatedAxis_triality_octad_support_iff generatedOctadBasisOctad e c r).mp hr)
        rw [hz, mul_zero]
    · rw [generatedAxis_triality_octad_tensor_zero_all, map_zero]

/-- The actual Q stabilizer equals the proved eight-phase kernel. -/
theorem generatedOctadAxisQStabilizer_eq_phase_kernel (e : Fin 64) (c : ZMod 2) :
    generatedOctadAxisQStabilizer e c = generatedOctadBasisQPhases.ker :=
  le_antisymm (generatedOctadAxisQStabilizer_le_phase_kernel e c)
    (generatedOctad_phase_kernel_le_axis_stabilizer e c)

/-- Exactly 2^17 actual extraspecial elements fix the transitioned octad axis. -/
theorem generatedOctadAxisQStabilizer_card (e : Fin 64) (c : ZMod 2) :
    Nat.card (generatedOctadAxisQStabilizer e c) = 2 ^ 17 := by
  rw [generatedOctadAxisQStabilizer_eq_phase_kernel, generatedOctadBasis_Q_phases_kernel_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
