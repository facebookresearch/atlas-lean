/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusRandomCluster

open scoped BigOperators

namespace StatMech.FrontierD

noncomputable section



def fkRectMedialLoopCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  fkMedialLoopCount R.medialTorus
    (fkRectConfigurationToMedialPairing R omega)





def fkRectEulerHomologyDefect (R : FKRectTorus)
    (omega : R.Configuration) : Int :=
  2 * (fkRectNumClusters R omega : Int) +
      (fkRectOpenEdgeCount R omega : Int) -
    (fkRectMedialLoopCount R omega : Int) -
    (R.width * R.height : Nat)

theorem fkRectCriticalReducedWeight_eq_sqrt_pow
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega =
      Real.sqrt q ^
        (fkRectOpenEdgeCount R omega + 2 * fkRectNumClusters R omega) := by
  unfold fkRectCriticalReducedWeight
  calc
    Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        q ^ fkRectNumClusters R omega =
      Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        (Real.sqrt q ^ 2) ^ fkRectNumClusters R omega := by
          rw [Real.sq_sqrt hq.le]
    _ = Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        Real.sqrt q ^ (2 * fkRectNumClusters R omega) := by
          rw [pow_mul]
    _ = Real.sqrt q ^
        (fkRectOpenEdgeCount R omega + 2 * fkRectNumClusters R omega) := by
          rw [pow_add]



theorem fkRectCriticalReducedWeight_eq_loop_defect
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega =
      Real.sqrt q ^ (R.width * R.height : Nat) *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          Real.sqrt q ^ fkRectEulerHomologyDefect R omega := by
  have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  rw [fkRectCriticalReducedWeight_eq_sqrt_pow R hq]
  rw [<- zpow_natCast]
  rw [show ((fkRectOpenEdgeCount R omega +
      2 * fkRectNumClusters R omega : Nat) : Int) =
      (R.width * R.height : Nat) +
        (fkRectMedialLoopCount R omega : Int) +
          fkRectEulerHomologyDefect R omega by
    unfold fkRectEulerHomologyDefect
    push_cast
    ring]
  rw [zpow_add₀ hsqrt, zpow_add₀ hsqrt]
  simp only [zpow_natCast]


def fkRectCriticalLoopNormalization (R : FKRectTorus) (q : Real) : Real :=
  (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) *
    Real.sqrt q ^ (R.width * R.height)




theorem fkRectRandomClusterWeight_critical_eq_loop_defect
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectRandomClusterWeight R (fkRectCriticalP q) q omega =
      fkRectCriticalLoopNormalization R q *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          Real.sqrt q ^ fkRectEulerHomologyDefect R omega := by
  rw [fkRectRandomClusterWeight_critical_eq R hq,
    fkRectCriticalReducedWeight_eq_loop_defect R hq]
  unfold fkRectCriticalLoopNormalization
  ring



theorem fkRectRandomClusterWeight_critical_eq_loop_net
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) (s : Nat)
    (hnet : fkRectEulerHomologyDefect R omega = 2 * (s : Int)) :
    fkRectRandomClusterWeight R (fkRectCriticalP q) q omega =
      fkRectCriticalLoopNormalization R q *
        Real.sqrt q ^ fkRectMedialLoopCount R omega * q ^ s := by
  rw [fkRectRandomClusterWeight_critical_eq_loop_defect R hq, hnet]
  have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  rw [show (2 * (s : Int)) = (2 * s : Nat) by omega, zpow_natCast]
  rw [pow_mul, Real.sq_sqrt hq.le]

end

end StatMech.FrontierD
