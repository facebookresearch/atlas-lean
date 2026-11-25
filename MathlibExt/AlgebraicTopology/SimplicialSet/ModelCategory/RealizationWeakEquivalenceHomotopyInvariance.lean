/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.Topology.Homotopy.TopCat.ToSSet

/-!
# Homotopy invariance of realization weak equivalences

Homotopic maps between Kan complexes induce naturally isomorphic fundamental-
groupoid functors.  On every pointed homotopy group, the second map is the
first followed by transport along that isomorphism.  Hence `KanComplex.W` is
unchanged by a simplicial homotopy.  Realizing an arbitrary simplicial
homotopy and applying the singular functor gives the corresponding result for
`realizationWeakEquivalences`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace SSet

/-- Simplicially homotopic maps are realization weak equivalences
simultaneously. -/
theorem realizationWeakEquivalences_iff_of_homotopy
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    realizationWeakEquivalences f ↔ realizationWeakEquivalences g := by
  let Hreal : TopCat.Homotopy
      (SSet.toTop.map f) (SSet.toTop.map g) :=
    SSet.realizeHomotopy X Y f g H
  let Hsing : SSet.Homotopy
      (TopCat.toSSet.map (SSet.toTop.map f))
      (TopCat.toSSet.map (SSet.toTop.map g)) :=
    Hreal.toSSet
  let _ : KanComplex (TopCat.toSSet.obj (SSet.toTop.obj X)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : KanComplex (TopCat.toSSet.obj (SSet.toTop.obj Y)) :=
    TopCat.toSSet_obj_kanComplex _
  change KanComplex.W (TopCat.toSSet.map (SSet.toTop.map f)) ↔
    KanComplex.W (TopCat.toSSet.map (SSet.toTop.map g))
  exact KanComplex.W.iff_of_homotopy Hsing

end SSet

end
