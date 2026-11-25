/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.TopCatULiftSingularIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftKanWeak
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Genuine original topological weak class under universe lift

The full original singular-complex isomorphism retains every original
continuous source map. Actual singular Kan fibrancy and the genuine
coefficient-lift Kan weak iff prove preservation and reflection of the
same original topological weak class, across independent universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace TopCat

/-- The same original continuous map is weak exactly when its actual full topological
coefficient lift is weak. -/
theorem ulift_weakHomotopyEquivalences_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    weakHomotopyEquivalences (TopCat.uliftFunctor.{v,u}.map f) ↔ weakHomotopyEquivalences f := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  let e : Arrow.mk (TopCat.toSSet.map (TopCat.uliftFunctor.{v,u}.map f)) ≅
      Arrow.mk (SSet.uliftFunctor.{v,u}.map (TopCat.toSSet.map f)) :=
    Arrow.isoMk (AlgebraicTopology.IntegralUniverseLift.singularSSetIso X)
      (AlgebraicTopology.IntegralUniverseLift.singularSSetIso Y)
      (AlgebraicTopology.IntegralUniverseLift.singularSSetIso_hom_naturality f).symm
  exact (SSet.KanComplex.W.arrow_mk_iso_iff e).trans
    (SSet.KanComplex.W_ulift_map_iff (TopCat.toSSet.map f))

end TopCat
