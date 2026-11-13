/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SignedLoopThermodynamicLimit













open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.Ising StatMech.FrontierA

noncomputable section




def ons_rectDualPathCriticalCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N)
    (sigma : Equiv.Perm (ons_rectDualGraph M N).Dart) : Complex :=
  let matrix := 1 - kwGraphTransition (ons_rectDualGraph M N)
    (ons_rectDualPathDefectWeight path ons_signedLoopCriticalWeight)
    embedding.turnPhase
  (ons_signedLoopCriticalWeight : Complex) ^
      (2 * (ons_rectDualPathDefect path).card) *
    (((sigma.sign : Int) : Complex) *
      ∏ dart, matrix (sigma dart) dart)



theorem summable_ons_rectDualPathCriticalCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    Summable (ons_rectDualPathCriticalCycleCoverTerm embedding path) :=
  (hasSum_fintype
    (ons_rectDualPathCriticalCycleCoverTerm embedding path)).summable



theorem tsum_ons_rectDualPathCriticalCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    ∑' sigma, ons_rectDualPathCriticalCycleCoverTerm embedding path sigma =
      (ons_sourceX (ons_rectDualGraph M N) {path.source, path.target}
        ons_signedLoopCriticalWeight : Complex) ^ 2 := by
  rw [tsum_fintype]
  unfold ons_rectDualPathCriticalCycleCoverTerm
  rw [← Finset.mul_sum]
  rw [← Matrix.det_apply']
  exact (coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet embedding path
    ons_signedLoopCriticalWeight_pos.ne').symm



def ons_rectDualPathCriticalNormalizedCycleCoverTerm {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N)
    (sigma : Equiv.Perm (ons_rectDualGraph M N).Dart) : Complex :=
  ons_rectDualPathCriticalCycleCoverTerm embedding path sigma /
    ons_rectDualKWDet embedding ons_signedLoopCriticalWeight

theorem summable_ons_rectDualPathCriticalNormalizedCycleCoverTerm
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    Summable
      (ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path) :=
  (summable_ons_rectDualPathCriticalCycleCoverTerm embedding path).div_const _



theorem tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    ∑' sigma,
        ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path sigma =
      (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0
        (fun config => StatMech.Ising.spin config path.source *
          StatMech.Ising.spin config path.target) : Complex) ^ 2 := by
  unfold ons_rectDualPathCriticalNormalizedCycleCoverTerm
  rw [tsum_div_const,
    tsum_ons_rectDualPathCriticalCycleCoverTerm embedding path]
  rw [ons_finiteTwoPoint_critical_source_ratio
    (ons_rectDualGraph M N) path.source_ne_target]
  push_cast
  rw [div_pow, coe_ons_rectDual_X_sq_eq_kwDet embedding]

private theorem abs_isingExpectation_spin_mul_spin_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (u v : V) :
    |isingExpectation G beta 0 (fun config => spin config u * spin config v)| ≤ 1 := by
  unfold isingExpectation
  calc
    |∑ spin, isingProb G beta 0 spin *
        (StatMech.Ising.spin spin u * StatMech.Ising.spin spin v)| ≤
        ∑ spin, |isingProb G beta 0 spin *
          (StatMech.Ising.spin spin u * StatMech.Ising.spin spin v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ spin, isingProb G beta 0 spin := by
      apply Finset.sum_le_sum
      intro spin _
      rw [abs_mul, abs_of_nonneg (isingProb_nonneg G beta 0 spin), abs_mul]
      exact mul_le_of_le_one_right (isingProb_nonneg G beta 0 spin)
        (mul_le_one₀ (abs_spin_le_one spin u) (abs_nonneg _)
          (abs_spin_le_one spin v))
    _ = 1 := isingProb_sum_eq_one G beta 0




theorem norm_tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm_le_one
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (path : ons_RectDualPath M N) :
    ‖∑' sigma,
        ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path sigma‖ ≤ 1 := by
  rw [tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm embedding path,
    norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg _)
    (abs_isingExpectation_spin_mul_spin_le_one
      (ons_rectDualGraph M N) ons_betaC path.source path.target)




theorem ons_rectDualPathCriticalNormalizedCycleCover_tendsto_freeState
    (embedding : ∀ n, KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
    (a b : StatMech.Lattice.Site 2)
    (hsource : ∀ᶠ n in Filter.atTop,
      ((ons_box2EquivRect n).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in Filter.atTop,
      ((ons_box2EquivRect n).symm (path n).target).1 = b) :
    Filter.Tendsto
      (fun n => ∑' sigma,
        ons_rectDualPathCriticalNormalizedCycleCoverTerm
          (embedding n) (path n) sigma)
      Filter.atTop
      (nhds ((((∫ spin, StatMech.Ising.spinProd {a, b} spin
        ∂(StatMech.Ising.freeState 2 ons_betaC 0 :
          MeasureTheory.Measure
            (StatMech.ConfigSpace (StatMech.Lattice.Site 2)))) : Real) :
              Complex) ^ 2)) := by
  apply (ons_rectDualPathCriticalRatio_tendsto_freeState
    embedding path a b hsource htarget).congr'
  filter_upwards [] with n
  rw [tsum_ons_rectDualPathCriticalNormalizedCycleCoverTerm]
  exact (coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio
    (embedding n) (path n)).symm

end

end StatMech.Onsager
