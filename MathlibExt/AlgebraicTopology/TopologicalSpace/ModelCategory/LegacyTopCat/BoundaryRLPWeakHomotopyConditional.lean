/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLP
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Conditional weak homotopy comparison from boundary lifting

Assume that a map between Kan complexes with the right lifting property against
all simplicial boundaries is a Kan-complex weak equivalence. Then a topological
map with the right lifting property against all realized boundaries is a weak
homotopy equivalence.

The realization–singular adjunction supplies the boundary lifting property of the
singular map, and both singular complexes are Kan, so the stated Kan-restricted
comparison hypothesis applies.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/--
If simplicial boundary-right-lifting maps between Kan complexes are Kan-complex
weak equivalences, then topological maps lifting against all realized boundary
inclusions are weak homotopy equivalences.
-/
theorem boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W
    (h : ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f) :
    realizedBoundaryInclusions.{u}.rlp ≤ weakHomotopyEquivalences := by
  intro X Y f hf
  let _ : SSet.KanComplex (toSSet.obj X) := toSSet_obj_kanComplex X
  let _ : SSet.KanComplex (toSSet.obj Y) := toSSet_obj_kanComplex Y
  have hI : SSet.modelCategoryQuillen.I.{u}.rlp (toSSet.map f) :=
    boundaryRLP_le_inverseImage_I_rlp _ hf
  have hW : SSet.KanComplex.W.{u} (toSSet.map f) := h hI
  exact (mem_weakHomotopyEquivalences_iff f).mpr hW

end TopCat
