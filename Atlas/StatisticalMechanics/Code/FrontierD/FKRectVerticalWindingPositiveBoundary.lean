/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingBoundarySum










open Equiv Finset

namespace StatMech.FrontierD

noncomputable section



theorem sum_fkRectBlackBoundaryWeight_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) :
    (∑ d : FKMedialBlackDart R.medialTorus,
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega) d) = 0 := by
  let f : FKMedialBlackDart R.medialTorus -> Int × Int := fun d =>
    fkRectBlackBoundaryWeight R
      (fkRectConfigurationToMedialPairing R omega) d
  let g : R.medialTorus.Vertex × Bool -> Int × Int := fun vb =>
    f ((fkMedialBlackDartEquivVertexBool R.medialTorus).symm vb)
  have hequiv : (∑ d : FKMedialBlackDart R.medialTorus, f d) =
      ∑ vb : R.medialTorus.Vertex × Bool, g vb := by
    apply Fintype.sum_equiv
      (fkMedialBlackDartEquivVertexBool R.medialTorus)
    intro d
    change f d = g ((fkMedialBlackDartEquivVertexBool R.medialTorus) d)
    unfold g
    rw [(fkMedialBlackDartEquivVertexBool
      R.medialTorus).symm_apply_apply]
  have hprod : (∑ vb : R.medialTorus.Vertex × Bool, g vb) =
      ∑ v : R.medialTorus.Vertex, ∑ b : Bool, g (v, b) :=
    Fintype.sum_prod_type g
  change (∑ d : FKMedialBlackDart R.medialTorus, f d) = 0
  rw [hequiv, hprod]
  apply Finset.sum_eq_zero
  intro v _
  rw [Fintype.sum_bool]
  simp only [g, f, fkMedialBlackDartEquivVertexBool]
  simpa only [add_comm] using
    fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero R omega v



theorem sum_fkRectBlackBoundaryCycleWinding_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) :
    (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      fkRectBlackBoundaryCycleWinding R omega C) = 0 := by
  unfold fkRectBlackBoundaryCycleWinding
  rw [sum_permCycleQuotientWeightSum]
  exact sum_fkRectBlackBoundaryWeight_eq_zero R omega


theorem sum_fkRectBlackBoundaryCycleWinding_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) :
    (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      (fkRectBlackBoundaryCycleWinding R omega C).2) = 0 := by
  have h := congrArg Prod.snd
    (sum_fkRectBlackBoundaryCycleWinding_eq_zero R omega)
  rw [Prod.snd_sum] at h
  simpa using h


def fkRectPositiveVerticalBoundaryWindingTotal
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    (fkRectBlackBoundaryCycleWinding R omega C).2.toNat

private theorem two_mul_sum_toNat_eq_sum_natAbs_of_sum_eq_zero
    {α : Type*} [Fintype α] (w : α -> Int)
    (hsum : ∑ a, w a = 0) :
    2 * (∑ a, (w a).toNat) = ∑ a, (w a).natAbs := by
  have hdiff :
      (∑ a, ((w a).toNat : Int)) -
          (∑ a, ((-w a).toNat : Int)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using hsum
  have hbalance : (∑ a, (w a).toNat) = ∑ a, (-w a).toNat := by
    exact_mod_cast sub_eq_zero.mp hdiff
  calc
    2 * (∑ a, (w a).toNat) =
        (∑ a, (w a).toNat) + ∑ a, (-w a).toNat := by omega
    _ = ∑ a, ((w a).toNat + (-w a).toNat) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ a, (w a).natAbs := by
      apply Finset.sum_congr rfl
      intro a _
      exact Int.toNat_add_toNat_neg_eq_natAbs (w a)



theorem fkRectUnorientedVerticalWindingTotal_eq_two_mul_positiveBoundary
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectUnorientedVerticalWindingTotal R omega =
      2 * fkRectPositiveVerticalBoundaryWindingTotal R omega := by
  rw [fkRectUnorientedVerticalWindingTotal,
    fkRectUnorientedVerticalWindingTotal_eq_sum_blackBoundaryCycle]
  symm
  exact two_mul_sum_toNat_eq_sum_natAbs_of_sum_eq_zero
    (fun C : FKRectConfigurationBlackBoundaryCycle R omega =>
      (fkRectBlackBoundaryCycleWinding R omega C).2)
    (sum_fkRectBlackBoundaryCycleWinding_snd_eq_zero R omega)


theorem fkRectUnorientedVerticalWindingNumber_eq_positiveBoundary
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectUnorientedVerticalWindingNumber R omega =
      fkRectPositiveVerticalBoundaryWindingTotal R omega := by
  unfold fkRectUnorientedVerticalWindingNumber
  rw [fkRectUnorientedVerticalWindingTotal_eq_two_mul_positiveBoundary]
  simp

end

end StatMech.FrontierD
