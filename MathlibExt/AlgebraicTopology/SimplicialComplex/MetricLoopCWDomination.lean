/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricLoopLocalConvexity
public import MathlibExt.Topology.CWComplex.MetricDomination
public import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Based CW domination of raw metric loops

The original raw-loop local convexity data instantiates the neutral metric
interpolation CW construction, retaining its point and complete relative homotopy.
-/

noncomputable section
set_option autoImplicit false

open Set Function Filter Topology
open scoped unitInterval NNReal BigOperators

universe u

namespace MetricLoopCWDominationConstruction

open Topology.CWComplex.MetricDomination

/-- The full raw metric-loop application. Only the original complex and vertex are inputs. -/
private theorem metric_loop_based_CW_domination {V : Type u}
    (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let a : PreAbstractSimplicialComplex.MetricRealization P :=
      PreAbstractSimplicialComplex.Realization.toMetric P
        (PreAbstractSimplicialComplex.Realization.vertex P v hv)
    let M := Path a a
    let e : M := Path.refl a
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J) (W : J → Set M)
      (v0 : J) (hv0 : {v0} ∈ Q),
      (∀ s : Finset J, s ∈ Q ↔ s.Nonempty ∧ ∃ x : M, ∀ j ∈ s, x ∈ W j) ∧
      (∀ j : J, IsOpen (W j) ∧ (W j).Nonempty) ∧
      (⋃ j : J, W j = Set.univ) ∧ LocallyFinite W ∧
      (∀ j : J, e ∈ W j ↔ j = v0) ∧
      let N := Q.Realization
      let n0 := PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0
      let cw := PreAbstractSimplicialComplex.Realization.classicalCWComplex Q
      letI : Topology.CWComplex (Set.univ : Set N) := cw
      ∃ (p : C(M, N)) (q : C(N, M)),
        p e = n0 ∧ q n0 = e ∧
        ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id M) ({e} : Set M),
          (∀ t : unitInterval, H (t, e) = e) ∧
          ∃ j : Topology.CWComplex.cell (Set.univ : Set N) 0,
            ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = n0 := by
  let a : PreAbstractSimplicialComplex.MetricRealization P :=
    PreAbstractSimplicialComplex.Realization.toMetric P
      (PreAbstractSimplicialComplex.Realization.vertex P v hv)
  let M := Path a a
  let e : M := Path.refl a
  obtain ⟨d, htop, U, _, _, H, hstationary, hconvex, _⟩ :=
    PreAbstractSimplicialComplex.metricLoopLocalConvexity P v hv
  -- This keeps the ORIGINAL compact-open Path topology definitionally.
  let : MetricSpace M := d.replaceTopology htop.symm
  choose B hBopen hBmem hBsquare hBstable using hconvex
  let c : Interpolation M :=
    { domain := U
      homotopy := H
      stationary := hstationary
      neighborhood := B
      neighborhood_open := hBopen
      neighborhood_mem := hBmem
      neighborhood_square := fun x a ha b hb => hBsquare x a b ha hb
      neighborhood_stable := fun x a ha b hb hab t => hBstable x a b ha hb hab t }
  exact metric_based_CW_domination c e

end MetricLoopCWDominationConstruction

public section

namespace PreAbstractSimplicialComplex

/-- Construct a CW domination of the entire actual raw metric-loop space at its literal point. -/
theorem metricLoopCWDomination {V : Type u}
    (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let a : PreAbstractSimplicialComplex.MetricRealization P :=
      PreAbstractSimplicialComplex.Realization.toMetric P
        (PreAbstractSimplicialComplex.Realization.vertex P v hv)
    let M := Path a a
    let e : M := Path.refl a
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J) (W : J → Set M)
      (v0 : J) (hv0 : {v0} ∈ Q),
      (∀ s : Finset J, s ∈ Q ↔ s.Nonempty ∧ ∃ x : M, ∀ j ∈ s, x ∈ W j) ∧
      (∀ j : J, IsOpen (W j) ∧ (W j).Nonempty) ∧
      (⋃ j : J, W j = Set.univ) ∧ LocallyFinite W ∧
      (∀ j : J, e ∈ W j ↔ j = v0) ∧
      let N := Q.Realization
      let n0 := PreAbstractSimplicialComplex.Realization.vertex Q v0 hv0
      let cw := PreAbstractSimplicialComplex.Realization.classicalCWComplex Q
      letI : Topology.CWComplex (Set.univ : Set N) := cw
      ∃ (p : C(M, N)) (q : C(N, M)),
        p e = n0 ∧ q n0 = e ∧
        ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id M) ({e} : Set M),
          (∀ t : unitInterval, H (t, e) = e) ∧
          ∃ j : Topology.CWComplex.cell (Set.univ : Set N) 0,
            ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = n0 := by
  exact MetricLoopCWDominationConstruction.metric_loop_based_CW_domination P v hv

end PreAbstractSimplicialComplex
