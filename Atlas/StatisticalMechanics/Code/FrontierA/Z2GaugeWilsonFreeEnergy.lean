/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















import Code.FrontierA.Z2GaugeCubicalDualEquiv
import Code.FrontierA.Z2GaugeWilsonSupport
import Code.Ising.PressureBCIndep

open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.FrontierA

noncomputable section

local instance wilsonFreeEnergyPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]



def multibondTwistCoupling (J : P → Real) (D : Finset P) : P → Real :=
  fun p => if p ∈ D then -J p else J p

@[simp] theorem multibondTwistCoupling_apply_mem
    (J : P → Real) (D : Finset P) {p : P} (hp : p ∈ D) :
    multibondTwistCoupling J D p = -J p := by
  simp [multibondTwistCoupling, hp]

@[simp] theorem multibondTwistCoupling_apply_not_mem
    (J : P → Real) (D : Finset P) {p : P} (hp : p ∉ D) :
    multibondTwistCoupling J D p = J p := by
  simp [multibondTwistCoupling, hp]



theorem multibond_twist_energy_eq_shiftedCut
    (ends : P → V × V) (J : P → Real) (D : Finset P) (s : V → Bool) :
    (∑ p : P, multibondTwistCoupling J D p) -
        2 * ∑ p ∈ multibondCut ends s, multibondTwistCoupling J D p =
      (∑ p : P, J p) - 2 * ∑ p ∈ multibondCut ends s ∆ D, J p := by
  classical
  have sum_indicator (S : Finset P) (f : P → Real) :
      (∑ p ∈ S, f p) = ∑ p : P, if p ∈ S then f p else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [sum_indicator (multibondCut ends s),
    sum_indicator (multibondCut ends s ∆ D),
    Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hcut : p ∈ multibondCut ends s <;>
    by_cases hD : p ∈ D <;>
    simp [multibondTwistCoupling, hcut, hD, mem_symmDiff] <;> ring


theorem multibondIsingWeight_twist_eq_shiftedActivity
    (ends : P → V × V) (J : P → Real) (D : Finset P) (s : V → Bool) :
    multibondIsingWeight ends (multibondTwistCoupling J D) s =
      Real.exp (∑ p : P, J p) *
        ∏ p ∈ multibondCut ends s ∆ D, Real.exp (-2 * J p) := by
  rw [multibondIsingWeight, multibond_energy_eq_sub_cut,
    multibond_twist_energy_eq_shiftedCut]
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  symm
  calc
    (∑ p ∈ multibondCut ends s ∆ D, -2 * J p) =
        ∑ p ∈ multibondCut ends s ∆ D, -(2 * J p) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = -(∑ p ∈ multibondCut ends s ∆ D, 2 * J p) := by
      rw [Finset.sum_neg_distrib]



theorem multibondIsingPartition_twist_eq_shiftedActivity
    (root : V) (ends : P → V × V) (J : P → Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) =
      (2 * Real.exp (∑ p : P, J p)) *
        ∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1 ∆ D, Real.exp (-2 * J p) := by
  rw [multibondIsingPartition]
  calc
    (∑ s : V → Bool,
        multibondIsingWeight ends (multibondTwistCoupling J D) s) =
        ∑ bs : Bool × AnchoredConfig V root,
          multibondIsingWeight ends (multibondTwistCoupling J D)
            (unanchorConfig bs.1 bs.2) := by
      apply Fintype.sum_equiv (configEquivBoolAnchored root)
      intro s
      rw [show unanchorConfig ((configEquivBoolAnchored root s).1)
          ((configEquivBoolAnchored root s).2) = s from
        (configEquivBoolAnchored root).left_inv s]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [multibondIsingWeight_twist_eq_shiftedActivity,
        multibondCut_unanchorConfig]
      rw [Fintype.sum_bool]
      rw [← Finset.mul_sum]
      ring


theorem multibondIsingPartition_pos
    (ends : P → V × V) (J : P → Real) :
    0 < multibondIsingPartition ends J := by
  unfold multibondIsingPartition multibondIsingWeight
  positivity


def multibondIsingAction (ends : P → V × V) (J : P → Real)
    (s : V → Bool) : Real :=
  ∑ p : P, J p * if s (ends p).1 = s (ends p).2 then 1 else -1



theorem multibondIsingPartition_eq_Z_neg_one
    (ends : P → V × V) (J : P → Real) :
    multibondIsingPartition ends J =
      StatMech.Ising.Z (-1) (multibondIsingAction ends J) := by
  simp [multibondIsingPartition, multibondIsingWeight,
    StatMech.Ising.Z, multibondIsingAction]



theorem multibondIsingAction_twist_sub_abs_le
    (ends : P → V × V) (J : P → Real) (D : Finset P) (s : V → Bool) :
    |multibondIsingAction ends J s -
        multibondIsingAction ends (multibondTwistCoupling J D) s| ≤
      2 * ∑ p ∈ D, |J p| := by
  classical
  unfold multibondIsingAction
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ p : P, (
        (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
          multibondTwistCoupling J D p *
            (if s (ends p).1 = s (ends p).2 then 1 else -1))|
        ≤ ∑ p : P, |(
            (J p * if s (ends p).1 = s (ends p).2 then 1 else -1) -
              multibondTwistCoupling J D p *
                (if s (ends p).1 = s (ends p).2 then 1 else -1))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : P, if p ∈ D then 2 * |J p| else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ D <;>
        by_cases hs : s (ends p).1 = s (ends p).2 <;>
        simp [multibondTwistCoupling, hp, hs] <;>
        ring_nf <;> simp [abs_mul]
    _ = 2 * ∑ p ∈ D, |J p| := by
      rw [← Finset.sum_filter]
      simp only [subset_univ, filter_mem_eq_of_subset]
      rw [← Finset.mul_sum]


def multibondDisorderFreeEnergy
    (ends : P → V × V) (J : P → Real) (D : Finset P) : Real :=
  Real.log (multibondIsingPartition ends J) -
    Real.log (multibondIsingPartition ends (multibondTwistCoupling J D))



theorem multibondDisorderFreeEnergy_abs_le
    (ends : P → V × V) (J : P → Real) (D : Finset P) :
    |multibondDisorderFreeEnergy ends J D| ≤
      2 * ∑ p ∈ D, |J p| := by
  unfold multibondDisorderFreeEnergy
  rw [multibondIsingPartition_eq_Z_neg_one,
    multibondIsingPartition_eq_Z_neg_one]
  simpa using StatMech.Ising.logZ_dist_le (-1)
    (multibondIsingAction ends J)
    (multibondIsingAction ends (multibondTwistCoupling J D))
    (2 * ∑ p ∈ D, |J p|)
    (multibondIsingAction_twist_sub_abs_le ends J D)



theorem multibondIsing_twist_partition_ratio_eq_disorderRatio
    (root : V) (ends : P → V × V) (J : P → Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) /
        multibondIsingPartition ends J =
      (∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1 ∆ D, Real.exp (-2 * J p)) /
        (∑ s : AnchoredConfig V root,
          ∏ p ∈ multibondCut ends s.1, Real.exp (-2 * J p)) := by
  rw [multibondIsingPartition_twist_eq_shiftedActivity]
  rw [multibondIsingPartition_eq_two_mul_anchored]
  rw [← Finset.mul_sum]
  have hbulk : 2 * Real.exp (∑ p : P, J p) ≠ 0 := by positivity
  field_simp




theorem cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      multibondIsingPartition cubicalDualEnds
          (multibondTwistCoupling (fun p => gaugeDualCoupling (K p))
            (cubicalXYSheet k)) /
        multibondIsingPartition cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) := by
  rw [cubicalXYWilsonExpectation_eq_typedDisorderRatio ha hb hc k K hK]
  symm
  exact multibondIsing_twist_partition_ratio_eq_disorderRatio
    none cubicalDualEnds (fun p => gaugeDualCoupling (K p))
      (cubicalXYSheet k)



theorem neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    -Real.log
        (gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k)) =
      multibondDisorderFreeEnergy cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k) := by
  rw [cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio ha hb hc k K hK]
  unfold multibondDisorderFreeEnergy
  rw [Real.log_div
    (multibondIsingPartition_pos _ _).ne'
    (multibondIsingPartition_pos _ _).ne']
  ring


@[simp] theorem card_cubicalXYSheet
    {a b c : Nat} (k : Fin (c + 1)) :
    (cubicalXYSheet (a := a) (b := b) k).card = a * b := by
  unfold cubicalXYSheet
  rw [Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    rcases x with ⟨i, j⟩
    rcases y with ⟨i', j'⟩
    simp only at hxy
    cases hxy
    rfl



theorem cubicalXYWilsonFreeEnergy_mem_Icc
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p) :
    -Real.log
        (gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k)) ∈
      Set.Icc 0
        (2 * ∑ p ∈ cubicalXYSheet k, |gaugeDualCoupling (K p)|) := by
  have hpos : 0 <
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) :=
    (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence K hK (cubicalXYLoop k)).mpr
      ⟨cubicalXYSheet k, cubicalXYSheet_hasWilsonBoundary k⟩
  have hle :
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) ≤ 1 :=
    (gaugeWilsonExpectation_mem_Icc
      cubicalPlaquetteIncidence K hK (cubicalXYLoop k)).2
  constructor
  · rw [neg_nonneg]
    exact Real.log_nonpos hpos.le hle
  · rw [neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
      ha hb hc k K hK]
    exact le_trans (le_abs_self _)
      (multibondDisorderFreeEnergy_abs_le cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k))



theorem cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (beta : Real) (hbeta : 0 < beta) :
    -Real.log
        (gaugeWilsonExpectation cubicalPlaquetteIncidence
          (fun _ : CubicalPlaquette a b c => beta) (cubicalXYLoop k)) ≤
      2 * (a * b : Nat) * gaugeDualCoupling beta := by
  have hbound := (cubicalXYWilsonFreeEnergy_mem_Icc ha hb hc k
    (fun _ : CubicalPlaquette a b c => beta) (fun _ => hbeta)).2
  have hdual := gaugeDualCoupling_pos hbeta
  simpa [abs_of_pos hdual, Finset.sum_const, nsmul_eq_mul, mul_assoc] using hbound

end

end StatMech.FrontierA
