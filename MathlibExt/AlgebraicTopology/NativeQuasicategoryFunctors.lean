/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
# Completed native quasicategory law for simplicial functor objects

This is the exact native Mathlib internal-Hom instance at
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0), expressed through
the existing actual simplicial-Hom definition. No new Wanted theorem is
needed for this coefficient-independent construction.
-/

@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeQuasicategoryFunctors

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalClosed

universe u

theorem mapping_quasicategory (X Y : SSet.{u}) [SSet.Quasicategory Y] :
    SSet.Quasicategory (MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.mapping X Y) := by
  exact inferInstanceAs (SSet.Quasicategory ((ihom X).obj Y))

end MathlibExt.AlgebraicTopology.NativeQuasicategoryFunctors
