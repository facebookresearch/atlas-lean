/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLocalMarkedDisagreementSwitch
import Code.FrontierD.SixVertexSectorTransferBridge










open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section

local instance instDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem eval_sixVertexLocalMarkedPatternWeight
    (t : Real) (p : SixVertexLocalIncomingPattern) :
    eval t (sixVertexLocalMarkedPatternWeight p) =
      sixVertexLocalPatternWeight (2 + t) p := by
  unfold sixVertexLocalMarkedPatternWeight sixVertexLocalPatternWeight
  by_cases hp : p.Ice
  · rw [if_pos hp, if_pos hp]
    by_cases hc : p.IsCType <;> simp [hc]
  · simp [hp]


noncomputable def sixVertexTorusMarkedWeight
    {T : EvenTorus} (omega : SixVertexArrows T) : Real[X] :=
  ∏ v, sixVertexLocalMarkedPatternWeight
    (sixVertexLocalIncomingPattern omega v)


def sixVertexTorusCTypeCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  ∑ v, if omega.IsCType v then 1 else 0

theorem sixVertexTorusMarkedWeight_eq_pow
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) :
    sixVertexTorusMarkedWeight omega =
      (C 2 + X) ^ sixVertexTorusCTypeCount omega := by
  unfold sixVertexTorusMarkedWeight sixVertexTorusCTypeCount
  simp_rw [sixVertexLocalMarkedPatternWeight_eq_pow _
    (sixVertexLocalIncomingPattern_ice omega homega _)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp only [sixVertexLocalIncomingPattern_isCType_iff]

theorem sixVertexTorusMarkedWeight_eq_zero_of_not_ice
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : ¬ omega.IceRule) :
    sixVertexTorusMarkedWeight omega = 0 := by
  classical
  simp only [SixVertexArrows.IceRule, not_forall] at homega
  obtain ⟨v, hv⟩ := homega
  have hpattern : ¬ (sixVertexLocalIncomingPattern omega v).Ice := by
    rw [SixVertexLocalIncomingPattern.Ice,
      sixVertexLocalIncomingPattern_count]
    exact hv
  have hzero : sixVertexLocalMarkedPatternWeight
      (sixVertexLocalIncomingPattern omega v) = 0 := by
    simp [sixVertexLocalMarkedPatternWeight, hpattern]
  exact Finset.prod_eq_zero (Finset.mem_univ v) hzero

theorem coeff_sixVertexTorusMarkedWeight
    {T : EvenTorus} (omega : SixVertexArrows T) (k : Nat) :
    (sixVertexTorusMarkedWeight omega).coeff k =
      if omega.IceRule then
        (2 : Real) ^ (sixVertexTorusCTypeCount omega - k) *
          (sixVertexTorusCTypeCount omega).choose k
      else 0 := by
  classical
  by_cases homega : omega.IceRule
  · rw [if_pos homega, sixVertexTorusMarkedWeight_eq_pow omega homega,
      coeff_two_add_X_pow]
  · rw [if_neg homega]
    rw [sixVertexTorusMarkedWeight_eq_zero_of_not_ice omega homega]
    simp

theorem eval_sixVertexTorusMarkedWeight
    {T : EvenTorus} (t : Real) (omega : SixVertexArrows T) :
    eval t (sixVertexTorusMarkedWeight omega) =
      omega.weight (2 + t) := by
  change (evalRingHom t) (sixVertexTorusMarkedWeight omega) = _
  rw [sixVertexTorusMarkedWeight, map_prod, SixVertexArrows.weight]
  apply Finset.prod_congr rfl
  intro v hv
  change eval t
      (sixVertexLocalMarkedPatternWeight
        (sixVertexLocalIncomingPattern omega v)) = _
  rw [eval_sixVertexLocalMarkedPatternWeight,
    sixVertexLocalPatternWeight_eq_localWeight]


noncomputable def sixVertexTorusMarkedSectorPartitionPolynomial
    (T : EvenTorus) (n : Fin (T.width + 1)) : Real[X] :=
  ∑ omega : SixVertexArrows T,
    if sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
      sixVertexTorusMarkedWeight omega
    else 0

theorem eval_sixVertexTorusMarkedSectorPartitionPolynomial
    (T : EvenTorus) (n : Fin (T.width + 1)) (t : Real) :
    eval t (sixVertexTorusMarkedSectorPartitionPolynomial T n) =
      svTorusSectorArrowPartitionSum T n (2 + t) := by
  change (evalRingHom t)
      (sixVertexTorusMarkedSectorPartitionPolynomial T n) = _
  rw [sixVertexTorusMarkedSectorPartitionPolynomial,
    svTorusSectorArrowPartitionSum, map_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp [hsector, eval_sixVertexTorusMarkedWeight]
  · simp [hsector]


theorem sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace
    (T : EvenTorus) (n : Fin (T.width + 1)) :
    sixVertexTorusMarkedSectorPartitionPolynomial T n =
      sixVertexShiftedSectorTracePolynomial T.width T.height n.val := by
  apply Polynomial.funext
  intro t
  calc
    eval t (sixVertexTorusMarkedSectorPartitionPolynomial T n) =
        svTorusSectorArrowPartitionSum T n (2 + t) :=
      eval_sixVertexTorusMarkedSectorPartitionPolynomial T n t
    _ = Matrix.trace
        (sixVertexSectorTransfer T.width n.val (2 + t) ^ T.height) :=
      svTorusSectorArrowPartitionSum_eq_sectorTrace T n (2 + t)
    _ = eval t
        (sixVertexShiftedSectorTracePolynomial
          T.width T.height n.val) :=
      (eval_sixVertexShiftedSectorTracePolynomial
        T.width T.height n.val t).symm



theorem sixVertexMarkedSectorTraceCoefficient_eq_torus_sum
    (T : EvenTorus) (n : Fin (T.width + 1)) (k : Nat) :
    sixVertexMarkedSectorTraceCoefficient
        T.width T.height n.val k =
      ∑ omega : SixVertexArrows T,
        if sixVertexUpCount
            (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
          (sixVertexTorusMarkedWeight omega).coeff k
        else 0 := by
  unfold sixVertexMarkedSectorTraceCoefficient
  rw [← sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace T n]
  unfold sixVertexTorusMarkedSectorPartitionPolynomial
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp [hsector]
  · simp [hsector]



theorem sixVertexMarkedSectorTraceCoefficient_eq_colored_count
    (T : EvenTorus) (n : Fin (T.width + 1)) (k : Nat) :
    sixVertexMarkedSectorTraceCoefficient
        T.width T.height n.val k =
      ∑ omega : SixVertexArrows T,
        if sixVertexUpCount
            (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
          if omega.IceRule then
            (2 : Real) ^ (sixVertexTorusCTypeCount omega - k) *
              (sixVertexTorusCTypeCount omega).choose k
          else 0
        else 0 := by
  rw [sixVertexMarkedSectorTraceCoefficient_eq_torus_sum]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp [hsector, coeff_sixVertexTorusMarkedWeight]
  · simp [hsector]

end

end StatMech.FrontierD
