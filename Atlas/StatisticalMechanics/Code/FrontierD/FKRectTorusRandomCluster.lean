/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusMedial

open scoped BigOperators

namespace StatMech.FrontierD

noncomputable section

noncomputable instance fkRectOpenGraphDecidableRel
    (R : FKRectTorus) (omega : R.Configuration) :
    DecidableRel (fkRectOpenGraph R omega).Adj := Classical.decRel _


def fkRectOpenEdgeCount (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  (Finset.univ.filter fun a : R.EdgeIndex => omega a = true).card


def fkRectNumClusters (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  Fintype.card (fkRectOpenGraph R omega).ConnectedComponent


def fkRectEdgeProduct (R : FKRectTorus) (p : Real)
    (omega : R.Configuration) : Real :=
  ∏ a : R.EdgeIndex, if omega a then p else 1 - p



def fkRectRandomClusterWeight (R : FKRectTorus) (p q : Real)
    (omega : R.Configuration) : Real :=
  fkRectEdgeProduct R p omega * q ^ fkRectNumClusters R omega


def fkRectRandomClusterZ (R : FKRectTorus) (p q : Real) : Real :=
  ∑ omega : R.Configuration, fkRectRandomClusterWeight R p q omega


def fkRectCriticalP (q : Real) : Real :=
  Real.sqrt q / (1 + Real.sqrt q)

theorem fkRectCriticalP_pos {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalP q := by
  unfold fkRectCriticalP
  exact div_pos (Real.sqrt_pos.2 hq) (by positivity)

theorem fkRectCriticalP_lt_one {q : Real} (hq : 0 < q) :
    fkRectCriticalP q < 1 := by
  unfold fkRectCriticalP
  rw [div_lt_one (by positivity : 0 < 1 + Real.sqrt q)]
  linarith

theorem one_sub_fkRectCriticalP {q : Real} (hq : 0 < q) :
    1 - fkRectCriticalP q = 1 / (1 + Real.sqrt q) := by
  unfold fkRectCriticalP
  field_simp [ne_of_gt (by positivity : 0 < 1 + Real.sqrt q)]
  ring

theorem fkRectCriticalP_eq_sqrt_mul_one_sub {q : Real} (hq : 0 < q) :
    fkRectCriticalP q = Real.sqrt q * (1 - fkRectCriticalP q) := by
  rw [one_sub_fkRectCriticalP hq]
  unfold fkRectCriticalP
  ring

theorem card_fkRectEdgeIndex (R : FKRectTorus) :
    Fintype.card R.EdgeIndex = 2 * R.width * R.height := by
  simp [FKRectTorus.EdgeIndex, FKRectTorus.Vertex, mul_assoc]



theorem fkRectEdgeProduct_critical_eq (R : FKRectTorus)
    {q : Real} (hq : 0 < q) (omega : R.Configuration) :
    fkRectEdgeProduct R (fkRectCriticalP q) omega =
      (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) *
        Real.sqrt q ^ fkRectOpenEdgeCount R omega := by
  classical
  let d : Real := 1 / (1 + Real.sqrt q)
  have hpOpen : fkRectCriticalP q = d * Real.sqrt q := by
    dsimp [d]
    unfold fkRectCriticalP
    ring
  have hpClosed : 1 - fkRectCriticalP q = d := by
    exact one_sub_fkRectCriticalP hq
  unfold fkRectEdgeProduct fkRectOpenEdgeCount
  rw [show (∏ a : R.EdgeIndex,
      if omega a then fkRectCriticalP q else 1 - fkRectCriticalP q) =
      ∏ a : R.EdgeIndex, d * (if omega a then Real.sqrt q else 1) by
    apply Finset.prod_congr rfl
    intro a ha
    cases hopen : omega a
    · simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using hpClosed
    · simp only [↓reduceIte]
      exact hpOpen]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, card_fkRectEdgeIndex]
  congr 1
  rw [Finset.prod_ite]
  simp


def fkRectCriticalReducedWeight (R : FKRectTorus) (q : Real)
    (omega : R.Configuration) : Real :=
  Real.sqrt q ^ fkRectOpenEdgeCount R omega *
    q ^ fkRectNumClusters R omega


theorem fkRectRandomClusterWeight_critical_eq (R : FKRectTorus)
    {q : Real} (hq : 0 < q) (omega : R.Configuration) :
    fkRectRandomClusterWeight R (fkRectCriticalP q) q omega =
      (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) *
        fkRectCriticalReducedWeight R q omega := by
  rw [fkRectRandomClusterWeight, fkRectEdgeProduct_critical_eq R hq]
  unfold fkRectCriticalReducedWeight
  ring


def fkRectCriticalReducedZ (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration, fkRectCriticalReducedWeight R q omega

theorem fkRectRandomClusterZ_critical_eq (R : FKRectTorus)
    {q : Real} (hq : 0 < q) :
    fkRectRandomClusterZ R (fkRectCriticalP q) q =
      (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) *
        fkRectCriticalReducedZ R q := by
  unfold fkRectRandomClusterZ fkRectCriticalReducedZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  exact fkRectRandomClusterWeight_critical_eq R hq omega

theorem fkRectCriticalReducedWeight_pos (R : FKRectTorus)
    {q : Real} (hq : 0 < q) (omega : R.Configuration) :
    0 < fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  exact mul_pos (pow_pos (Real.sqrt_pos.2 hq) _) (pow_pos hq _)

theorem fkRectCriticalReducedZ_pos (R : FKRectTorus)
    {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalReducedZ R q := by
  unfold fkRectCriticalReducedZ
  exact Finset.sum_pos
    (fun omega _ => fkRectCriticalReducedWeight_pos R hq omega)
    Finset.univ_nonempty



def fkRectCriticalRandomClusterProb (R : FKRectTorus) (q : Real)
    (omega : R.Configuration) : Real :=
  fkRectCriticalReducedWeight R q omega / fkRectCriticalReducedZ R q

theorem fkRectCriticalRandomClusterProb_eq_weight_div_Z
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q omega =
      fkRectRandomClusterWeight R (fkRectCriticalP q) q omega /
        fkRectRandomClusterZ R (fkRectCriticalP q) q := by
  rw [fkRectCriticalRandomClusterProb,
    fkRectRandomClusterWeight_critical_eq R hq,
    fkRectRandomClusterZ_critical_eq R hq]
  have hd : (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) ≠ 0 := by
    positivity
  field_simp

theorem fkRectCriticalRandomClusterProb_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    0 <= fkRectCriticalRandomClusterProb R q omega := by
  exact (div_pos (fkRectCriticalReducedWeight_pos R hq omega)
    (fkRectCriticalReducedZ_pos R hq)).le

theorem sum_fkRectCriticalRandomClusterProb
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    ∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega = 1 := by
  unfold fkRectCriticalRandomClusterProb
  rw [<- Finset.sum_div]
  exact div_self (fkRectCriticalReducedZ_pos R hq).ne'



def fkRectCriticalRandomClusterPMF (R : FKRectTorus)
    {q : Real} (hq : 0 < q) : PMF R.Configuration :=
  PMF.ofFintype
    (fun omega => ENNReal.ofReal (fkRectCriticalRandomClusterProb R q omega)) <| by
      rw [<- ENNReal.ofReal_sum_of_nonneg
        (fun omega _ => fkRectCriticalRandomClusterProb_nonneg R hq omega),
        sum_fkRectCriticalRandomClusterProb R hq]
      simp

@[simp] theorem fkRectCriticalRandomClusterPMF_apply
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterPMF R hq omega =
      ENNReal.ofReal (fkRectCriticalRandomClusterProb R q omega) :=
  PMF.ofFintype_apply _ _

end

end StatMech.FrontierD
