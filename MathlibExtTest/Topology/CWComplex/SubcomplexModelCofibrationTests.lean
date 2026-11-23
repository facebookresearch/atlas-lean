/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.SubcomplexModelCofibration

open CategoryTheory Topology Topology.CWComplex

universe u

#check Topology.CWComplex.subcomplexInclusion_mem_realizedBoundaryLLP
#print axioms Topology.CWComplex.subcomplexInclusion_mem_realizedBoundaryLLP

-- An actual whole lifting square retains both maps and both full equations.
example (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]
    (A : Subcomplex (Set.univ : Set X)) (E B : TopCat.{u})
    (p : E ⟶ B) (hp : TopCat.realizedBoundaryInclusions.rlp p)
    (a : TopCat.of (A : Set X) ⟶ E) (b : X ⟶ B)
    (sq : CommSq a (subcomplexInclusion A) p b) :
    ∃ l : X ⟶ E, subcomplexInclusion A ≫ l = a ∧ l ≫ p = b := by
  let : HasLiftingProperty (subcomplexInclusion A) p :=
    (subcomplexInclusion_mem_realizedBoundaryLLP X A) p hp
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
