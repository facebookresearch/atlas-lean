/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.StatisticalMechanics.RandomCluster.FKPressureDeriv
import PhyslibExt.StatisticalMechanics.RandomCluster.EdgePartitionFunction
import Mathlib.Data.Sym.Card

/-!
# Pressure regression and retained finite-graph coverage

A fixed finite carrier cannot be isomorphic to its double and have an edge. In contrast,
a constant sequence on one edge jointly satisfies the retained convex-limit hypotheses.
The existing edge-restricted box convergence theorem is instantiated in dimension one;
this is not convergence of the raw, uncentered partition function.
-/

open SimpleGraph Filter Topology
open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKPressureDeriv

example {V : Type*} [Fintype V] [DecidableEq V]
    (G : ℕ → SimpleGraph V) [∀ n, DecidableRel (G n).Adj]
    (hjux : ∀ m n, G (m + n) ≃g G m ⊕g G n) :
    ¬ 0 < (G 1).edgeFinset.card := by
  have h := Fintype.card_congr (hjux 1 1).toEquiv
  rw [Fintype.card_sum] at h
  let : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
  have hempty : (G 1).edgeFinset = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact isEmptyElim a
  simp [hempty]

private abbrev oneEdge : SimpleGraph (Fin 2) := ⊤
private lemma oneEdge_card : oneEdge.edgeFinset.card = 1 := by decide
private lemma oneEdge_pos : 0 < oneEdge.edgeFinset.card := by rw [oneEdge_card]; decide

example (t : ℝ) : HasDerivAt (ivp2_tiltFreeEnergy oneEdge 2)
    (fpd_avgDensity oneEdge t) t :=
  fpd_tiltFreeEnergy_deriv_eq_avgDensity oneEdge oneEdge_pos t

-- No juxtaposition or growing-edge premise is needed by this retained fixed-carrier API.
example : ConvexOn ℝ Set.univ (ivp2_tiltFreeEnergy oneEdge 2) := by
  have hc := ivp2_tiltFreeEnergy_convexOn oneEdge 2 (by norm_num) oneEdge_pos
  exact (fpd_ivPressure_convexDeriv_facts (fun _ : ℕ => oneEdge) (fun _ => hc)
    (ivp2_tiltFreeEnergy oneEdge 2) (fun _ => tendsto_const_nhds)).1

-- The two unused loop coordinates already multiply the raw one-edge partition function by4.
example (p q : ℝ) : fkZ oneEdge p q = 4 * ecz_fkZEdge oneEdge p q := by
  have hNE : ecz_NE oneEdge = 2 := by
    rw [ecz_NE_eq, Sym2.card, oneEdge_card]
    norm_num
  rw [ecz_factorization, hNE]
  norm_num

-- Genuine growing boxes, with all positive-index edge hypotheses discharged together.
example (t : ℝ) : ecz_PerEdgeDensityConverges 1 t :=
  ecz_perEdgeDensityConverges (by norm_num) t
    (fun n hn => ecz_box_edge_pos 1 (by norm_num) hn)

run_cmd do
  if (← Lean.getEnv).contains `StatMech.FK.fpd_exists_convex_ivPressure then
    throwError "Retired fixed-carrier existence wrapper is still present"

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKPressureDeriv
