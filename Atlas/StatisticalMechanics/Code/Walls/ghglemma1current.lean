/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Walls.ghggrahamclose
import Code.Sharpness.HcovAssembly

open Finset BigOperators SimpleGraph
open scoped Classical

namespace StatMech.Walls



theorem ghg_covariance_triangle_current_delta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (beta h : Real) (hbeta : 0 <= beta)
    (i j k : V) :
    Sharpness.HcovAssembly.hcaFieldDelta G beta h i j
        * Sharpness.HcovAssembly.hcaFieldDelta G beta h j k
      <= Sharpness.HcovAssembly.hcaFieldDelta G beta h j j
        * Sharpness.HcovAssembly.hcaFieldDelta G beta h i k := by
  let Z := Sharpness.currentSum (Sharpness.withGhost G) beta
    (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1)) ∅
  have hZpos : 0 < Z := by
    exact Ising.acr_currentSum_empty_pos (Sharpness.withGhost G) beta
      (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1))
  have hdelta (x y : V) :
      Z ^ 2 * Ising.cov2 G beta h x y
        = Sharpness.HcovAssembly.hcaFieldDelta G beta h x y := by
    simpa [Z, Ising.cov2, mul_comm] using
      (Sharpness.HcovAssembly.hca_field_covariance_eq_delta G beta h x y
        (ne_of_gt hZpos))
  have hlemma := ghg_lemma1_is_vbg G beta h hbeta i j k
  have hvar :
      VBG.vbg_var (Ising.isingProb G beta h) (fun s => Ising.spin s j)
        = Ising.cov2 G beta h j j := by
    rw [VBG.vbg_cov2_eq]
    rfl
  rw [hvar] at hlemma
  rw [<- hdelta i j, <- hdelta j k, <- hdelta j j, <- hdelta i k]
  calc
    (Z ^ 2 * Ising.cov2 G beta h i j) * (Z ^ 2 * Ising.cov2 G beta h j k)
        = (Z ^ 2) ^ 2
            * (Ising.cov2 G beta h i j * Ising.cov2 G beta h j k) := by ring
    _ <= (Z ^ 2) ^ 2
            * (Ising.cov2 G beta h j j * Ising.cov2 G beta h i k) :=
      mul_le_mul_of_nonneg_left hlemma (sq_nonneg (Z ^ 2))
    _ = (Z ^ 2 * Ising.cov2 G beta h j j)
          * (Z ^ 2 * Ising.cov2 G beta h i k) := by ring




theorem ghg_covariance_triangle_sourcePairDisconnSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (beta h : Real) (hbeta : 0 <= beta)
    (i j k : V) :
    Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta
          (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1))
          (Sharpness.HcovAssembly.hcaFieldSource i j) ∅ (some i) none
        * Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta
          (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1))
          (Sharpness.HcovAssembly.hcaFieldSource j k) ∅ (some j) none
      <= Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta
          (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1))
          (Sharpness.HcovAssembly.hcaFieldSource j j) ∅ (some j) none
        * Sharpness.FluxEdgeCopy.sourcePairDisconnSum (Sharpness.withGhost G) beta
          (Sharpness.FieldGhostDict.ghostCoupling h beta (fun _ => 1))
          (Sharpness.HcovAssembly.hcaFieldSource i k) ∅ (some i) none := by
  simpa [Sharpness.HcovAssembly.hcaFieldDelta] using
    ghg_covariance_triangle_current_delta G beta h hbeta i j k

end StatMech.Walls
