/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.TopCatULiftWeak
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence

/-!
# Genuine same-map realization weak universe lift

The actual original full realization Iso retains every source simplex
and original map. The native topological universe lift preserves and
reflects the original weak class through its genuine singular Iso.
Consequently the same arbitrary original simplicial weak map is
preserved and reflected across independent coefficient universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace SSet

/-- The same arbitrary original simplicial map is realization weak exactly when its full
actual universe lift is. -/
theorem realizationWeak_ulift_map_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationWeakEquivalences (SSet.uliftFunctor.{v,u}.map f) ↔
      realizationWeakEquivalences f := by
  let e : Arrow.mk (SSet.toTop.map (SSet.uliftFunctor.{v,u}.map f)) ≅
      Arrow.mk (TopCat.uliftFunctor.{v,u}.map (SSet.toTop.map f)) :=
    Arrow.isoMk (toTopULiftIso.{u,v}.app X) (toTopULiftIso.{u,v}.app Y)
      (toTopULiftIso.{u,v}.hom.naturality f).symm
  have h := TopCat.weakHomotopyEquivalences.arrow_mk_iso_iff e
  exact h.trans (TopCat.ulift_weakHomotopyEquivalences_iff (SSet.toTop.map f))

end SSet
