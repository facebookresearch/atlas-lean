/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FKG

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKG`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` and the triangle `⊤ : SimpleGraph (Fin 3)`:
* `card_connectedComponent_sup_edge_lt`: adding the edge `{0, 1}` to the empty graph on `Fin 2`
  merges two components;
* `numClusters_supermodular` and `fkWeight_logSupermodular` on the triangle;
* `fkProb_FKGLatticeCondition` at `p = 1/2`, `q = 2`;
* the headline `fkProb_positively_associated` (FKG inequality) at `p = 1/2`, `q = 2` on the
  triangle, for the increasing indicator functions of two different edges being open, and the
  event form `fkProb_positively_associated_events`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKG

open _root_.StatMech _root_.StatMech.FK

/-- The event "the edge `e` is open". -/
def edgeOpen {V : Type*} (e : Sym2 V) : Set (ConfigSpace (Sym2 V)) := {ω | ω e = true}

/-- "The edge `e` is open" is an increasing event. -/
theorem edgeOpen_isIncreasing {V : Type*} (e : Sym2 V) : IsIncreasing (edgeOpen e) := by
  intro x y hxy hx
  have h := hxy e
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- The indicator that the edge `e` is open is monotone. -/
theorem edgeOpen_indicator_monotone {V : Type*} (e : Sym2 V) :
    Monotone ((edgeOpen e).indicator fun _ => (1 : ℝ)) :=
  isIncreasing_iff_indicator_monotone.mp (edgeOpen_isIncreasing e)

-- On the empty graph, `0` and `1` are not reachable, so adding the edge drops the count.
example : Nat.card ((⊥ : SimpleGraph (Fin 2)) ⊔ SimpleGraph.edge 0 1).ConnectedComponent
    < Nat.card (⊥ : SimpleGraph (Fin 2)).ConnectedComponent :=
  card_connectedComponent_sup_edge_lt fun h => by
    simpa using SimpleGraph.reachable_bot.mp h

-- Supermodularity of the cluster count on the triangle.
example (a b : ConfigSpace (Sym2 (Fin 3))) :
    numClusters (⊤ : SimpleGraph (Fin 3)) a + numClusters ⊤ b
      ≤ numClusters ⊤ (a ⊔ b) + numClusters ⊤ (a ⊓ b) :=
  numClusters_supermodular _ a b

-- Log-supermodularity of the FK weight at `p = 1/2`, `q = 3`.
example (a b : ConfigSpace (Sym2 (Fin 3))) :
    fkWeight (⊤ : SimpleGraph (Fin 3)) (1 / 2) 3 a * fkWeight ⊤ (1 / 2) 3 b
      ≤ fkWeight ⊤ (1 / 2) 3 (a ⊔ b) * fkWeight ⊤ (1 / 2) 3 (a ⊓ b) :=
  fkWeight_logSupermodular _ (by norm_num) (by norm_num) (by norm_num) a b

-- The FK measure satisfies the FKG lattice condition.
example : FKGLatticeCondition (fun ω => fkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 ω) :=
  fkProb_FKGLatticeCondition _ (by norm_num) (by norm_num) (by norm_num)

-- The headline (FKG inequality): the indicators of the edges `{0, 1}` and `{1, 2}` of the
-- triangle are positively correlated.
example :
    (∑ ω, fkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 ω
        * (edgeOpen s(0, 1)).indicator (fun _ => (1 : ℝ)) ω)
      * (∑ ω, fkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 ω
        * (edgeOpen s(1, 2)).indicator (fun _ => (1 : ℝ)) ω)
    ≤ ∑ ω, fkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 ω
        * ((edgeOpen s(0, 1)).indicator (fun _ => (1 : ℝ)) ω
          * (edgeOpen s(1, 2)).indicator (fun _ => (1 : ℝ)) ω) :=
  fkProb_positively_associated _ (by norm_num) (by norm_num) (by norm_num)
    (edgeOpen_indicator_monotone _) (edgeOpen_indicator_monotone _)

-- The event form: `φ(A) φ(B) ≤ φ(A ∩ B)` for the same two edges.
example :
    (∑ ω, fkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 ω
        * (edgeOpen s(0, 1)).indicator (fun _ => (1 : ℝ)) ω)
      * (∑ ω, fkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 ω
        * (edgeOpen s(1, 2)).indicator (fun _ => (1 : ℝ)) ω)
    ≤ ∑ ω, fkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 ω
        * (edgeOpen s(0, 1) ∩ edgeOpen s(1, 2)).indicator (fun _ => (1 : ℝ)) ω :=
  fkProb_positively_associated_events _ (by norm_num) (by norm_num) (by norm_num)
    (edgeOpen_isIncreasing _) (edgeOpen_isIncreasing _)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKG
