/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Ising.TwoReplica
import Code.Ising.TwoReplicaWeighted
import Code.Ising.AizenmanSignDominance
import Code.Ising.HdomNativeWeight
import Code.Ising.TwoCurrentProbBound
import Code.Ising.CrossClassHdom
import Code.Ising.AizenmanBarsky

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




















noncomputable def egh_ensembleUrsell (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (B : Finset V) (o x y : V) : ℝ :=
  ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m B o x y















theorem egh_ensemble_ursell_eq (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (B : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    egh_ensembleUrsell G β J M B o x y = -2 * tcp_allConnMass G β J M B o x y :=
  tcp_lebowitz_summed_gap G β J M B hox hoy hxy





















theorem egh_ensemble_domination (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    2 * tcp_allConnMass G β J M B o x y
      ≤ tcp_partitionFunction G β J M B + tcp_allConnMass G β J M B o x y :=
  cch_crossClass_full_dom G β J hβ hJ M B o x y






theorem egh_ensemble_prob_le_one (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) :
    tcp_allConnProb G β J M B o x y ≤ 1 :=
  cch_allConn_prob_le_one G β J hβ hJ M B o x y










theorem egh_ensemble_ursell_sign (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) :
    egh_ensembleUrsell G β J M B o x y ≤ 0 := by
  rw [egh_ensemble_ursell_eq G β J M B hox hoy hxy]
  have := tcp_allConnMass_nonneg G β J hβ hJ M B o x y
  linarith





















theorem egh_ghs_distinct_site_ensemble (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) {o x y : V} (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y) :
    ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B
      ≤ (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {x, y}))
        + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, y}))
        + (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m (B ∆ {o, x})) :=
  tcp_ghs_distinct_site G β J hβ hJ M B hox hoy hxy




















theorem egh_eq_gri2_ensemble (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {u v : V} (huv : u ≠ v)
    (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v
        ↔ connP (posEdges G.edgeFinset m) u v) :
    ∑ m ∈ M, hnw_mass G β J m (B ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m B :=
  tcp_family_prob_le_one G β J hβ hJ M hnd B hm huv hcoh



















theorem egh_u3_nonpos_bound (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) (μ : ℝ) (hμ : 0 ≤ μ) :
    -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y
      ∧ -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  tcp_prob_bound_closes_lebowitz G β J hβ hJ M B o x y μ hμ











theorem egh_u3_nonpos (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) (μ : ℝ) (hμ : 0 ≤ μ) :
    -2 * μ * tcp_allConnProb G β J M B o x y ≤ 0 :=
  (egh_u3_nonpos_bound G β J hβ hJ M B o x y μ hμ).2





theorem egh_lebowitz_quantitative (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (B : Finset V) (o x y : V) (μ : ℝ) (hμ : 0 ≤ μ) :
    -2 * μ ≤ -2 * μ * tcp_allConnProb G β J M B o x y :=
  (egh_u3_nonpos_bound G β J hβ hJ M B o x y μ hμ).1




















theorem egh_aizenman_barsky_sharpness (β h : ℝ) (o : V) (Jsum : ℝ)
    (hghs : GHSThreePointSym G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o Jsum hghs hfactor

end Ising

end StatMech
