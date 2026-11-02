/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC`

On the path `0 - 1 - 2` (`pathGraph 3`) at `p = 1/2`, `q = 2`:
* `numClustersBC` with the empty wiring `⊥` is the free cluster count (`numClustersBC_bot`), and
  with the boundary clique it is the wired count (`numClustersBC_boundaryClique`);
* `bcProb` is nonnegative and normalized for the wiring `C = ⊤` that joins all three vertices;
* `bcProb_positively_associated` (FKG): the indicators of "edge `s(0, 1)` open" and
  "edge `s(1, 2)` open" are positively correlated under the free measure;
* `bcProb_mono_bc` (comparison of boundary conditions): with wirings `⊥ ≤ ⊤`, the event
  "edge `s(0, 1)` open" has larger probability under the fully wired measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.MonoBC

open _root_.StatMech _root_.StatMech.FK

/-- The event "the coordinate `e` is open". -/
def edgeOpen {E : Type*} (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

/-- "The coordinate `e` is open" is an increasing event. -/
theorem isIncreasing_edgeOpen {E : Type*} (e : E) : IsIncreasing (edgeOpen e) := by
  intro x y hxy hx
  have h := hxy e
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- The indicator of an increasing event is monotone. -/
theorem monotone_indicator_edgeOpen {E : Type*} (e : E) :
    Monotone ((edgeOpen e).indicator (fun _ => (1 : ℝ))) :=
  (isIncreasing_edgeOpen e).indicator_monotone

-- With the empty wiring, `numClustersBC` is the free cluster count.
example (ω : ConfigSpace (Sym2 (Fin 3))) :
    numClustersBC (SimpleGraph.pathGraph 3) ⊥ ω = numClusters (SimpleGraph.pathGraph 3) ω :=
  numClustersBC_bot _ ω

-- With the boundary clique of `{0, 2}`, `numClustersBC` is the wired cluster count.
example (ω : ConfigSpace (Sym2 (Fin 3))) :
    numClustersBC (SimpleGraph.pathGraph 3)
        (Lattice.boundaryCliqueGraph (fun x : Fin 3 => x ≠ 1)) ω
      = Lattice.numClustersWired (SimpleGraph.pathGraph 3) (fun x : Fin 3 => x ≠ 1) ω :=
  numClustersBC_boundaryClique _ _ ω

-- `bcProb` with the full wiring `⊤` is nonnegative.
example (ω : ConfigSpace (Sym2 (Fin 3))) :
    0 ≤ bcProb (SimpleGraph.pathGraph 3) ⊤ (1 / 2) 2 ω :=
  bcProb_nonneg _ _ (by norm_num) (by norm_num) (by norm_num) ω

-- `bcProb` is normalized.
example : ∑ ω, bcProb (SimpleGraph.pathGraph 3) ⊤ (1 / 2) 2 ω = 1 :=
  bcProb_sum_eq_one _ _ (by norm_num) (by norm_num) (by norm_num)

-- FKG for the free measure on the path: the two edge indicators are positively correlated.
example :
    (∑ ω, bcProb (SimpleGraph.pathGraph 3) ⊥ (1 / 2) 2 ω
          * (edgeOpen (s(0, 1) : Sym2 (Fin 3))).indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, bcProb (SimpleGraph.pathGraph 3) ⊥ (1 / 2) 2 ω
          * (edgeOpen (s(1, 2) : Sym2 (Fin 3))).indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, bcProb (SimpleGraph.pathGraph 3) ⊥ (1 / 2) 2 ω
          * ((edgeOpen (s(0, 1) : Sym2 (Fin 3))).indicator (fun _ => (1 : ℝ)) ω
            * (edgeOpen (s(1, 2) : Sym2 (Fin 3))).indicator (fun _ => (1 : ℝ)) ω) :=
  bcProb_positively_associated _ _ (by norm_num) (by norm_num) (by norm_num)
    (monotone_indicator_edgeOpen _) (monotone_indicator_edgeOpen _)

-- Comparison of boundary conditions: wiring all vertices (`⊥ ≤ ⊤`) raises the probability that
-- the edge `s(0, 1)` is open.
example :
    (∑ ω, (edgeOpen (s(0, 1) : Sym2 (Fin 3))).indicator (fun _ => (1 : ℝ)) ω
        * bcProb (SimpleGraph.pathGraph 3) ⊥ (1 / 2) 2 ω)
      ≤ ∑ ω, (edgeOpen (s(0, 1) : Sym2 (Fin 3))).indicator (fun _ => (1 : ℝ)) ω
        * bcProb (SimpleGraph.pathGraph 3) ⊤ (1 / 2) 2 ω :=
  bcProb_mono_bc _ _ _ bot_le (by norm_num) (by norm_num) (by norm_num) (isIncreasing_edgeOpen _)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.MonoBC
