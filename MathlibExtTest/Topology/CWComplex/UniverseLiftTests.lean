/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.UniverseLift

open Topology Set

universe u v

#check Topology.CWComplex.uliftCWComplex
#print axioms Topology.CWComplex.uliftCWComplex
#check Topology.CWComplex.uliftCWComplex_map
#print axioms Topology.CWComplex.uliftCWComplex_map
#check Topology.CWComplex.uliftCWComplex_zeroCell
#print axioms Topology.CWComplex.uliftCWComplex_zeroCell

-- The literal old zero-cell identifier lifts and remains that point at every coordinate.
example (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (x : X) (j : (inferInstance : CWComplex (Set.univ : Set X)).cell 0)
    (hj : (inferInstance : CWComplex (Set.univ : Set X)).map 0 j ![] = x) :
    let cw : CWComplex (Set.univ : Set (ULift.{v} X)) := CWComplex.uliftCWComplex X
    ∃ j' : cw.cell 0, ∀ z : Fin 0 → ℝ, cw.map 0 j' z = ULift.up x := by
  exact CWComplex.uliftCWComplex_zeroCell X x j hj

-- The actual lifted weak topology is usable without a separation assumption on X.
example (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Set (ULift.{v} X)) :
    let cw : CWComplex (Set.univ : Set (ULift.{v} X)) := CWComplex.uliftCWComplex X
    (∀ n j, IsClosed (A ∩ cw.map n j '' Metric.closedBall 0 1)) → IsClosed A := by
  dsimp only
  intro hA
  exact (CWComplex.uliftCWComplex X).closed' A (Set.subset_univ _) hA

-- Every lifted characteristic value follows from the public map lemma.
example (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (n : ℕ) (j : ULift.{v} ((inferInstance : CWComplex (Set.univ : Set X)).cell n))
    (z : Fin n → ℝ) :
    (CWComplex.uliftCWComplex X).map n j z =
      ULift.up ((inferInstance : CWComplex (Set.univ : Set X)).map n j.down z) := by
  exact CWComplex.uliftCWComplex_map X n j z
