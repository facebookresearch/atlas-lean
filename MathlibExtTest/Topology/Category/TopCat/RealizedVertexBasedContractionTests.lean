/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.RealizedVertexBasedContraction

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial unitInterval

#check TopCat.pathEndpoints_mem_weakHomotopyEquivalences_of_total_conull
#print axioms TopCat.pathEndpoints_mem_weakHomotopyEquivalences_of_total_conull
#check SSet.basedContractionAtRealizedVertex
#print axioms SSet.basedContractionAtRealizedVertex

-- The initial continuous map is the identity on the whole original realization.
example (K : SSet.{u}) (x : K _⦋0⦌)
    (hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    (SSet.basedContractionAtRealizedVertex K x hK).homotopy.curry 0 =
      ContinuousMap.id (SSet.toTop.obj K) :=
  (SSet.basedContractionAtRealizedVertex K x hK).homotopy.curry_zero

-- The final continuous map is constant at the actual original realized vertex.
example (K : SSet.{u}) (x : K _⦋0⦌)
    (hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K))) :
    (SSet.basedContractionAtRealizedVertex K x hK).homotopy.curry 1 =
      ContinuousMap.const (SSet.toTop.obj K) (SSet.realizedVertex x) :=
  (SSet.basedContractionAtRealizedVertex K x hK).homotopy.curry_one

-- The actual chosen vertex stays fixed at every homotopy time.
example (K : SSet.{u}) (x : K _⦋0⦌)
    (hK : TopCat.weakHomotopyEquivalences (terminal.from (SSet.toTop.obj K)))
    (s : unitInterval) :
    (SSet.basedContractionAtRealizedVertex K x hK).homotopy
        (s, SSet.realizedVertex x) = SSet.realizedVertex x :=
  (SSet.basedContractionAtRealizedVertex K x hK).fixed s
