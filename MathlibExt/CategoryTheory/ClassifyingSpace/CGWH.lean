/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Classifying spaces of ordinary categories in CGWH

This file defines the classifying-space functor as the ordinary nerve
followed by geometric realization in compactly generated weak Hausdorff
spaces, together with its literal underlying-Top comparison.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

/-- The classifying-space functor from ordinary categories to CGWH spaces. -/
noncomputable def classifyingSpaceCGWH :
    Cat.{v, u} ⥤ CGWH.{w, max u v} :=
  CategoryTheory.nerveFunctor.{v, u} ⋙
    SSet.toCGWH.{w, max u v}

/-- The underlying topological space of the CGWH classifying space is the
ordinary topological realization of the nerve. -/
noncomputable def classifyingSpaceCGWHToTopIso :
    CategoryTheory.classifyingSpaceCGWH.{w, v, u} ⋙
        CGWH.cgwhToTop.{w, max u v} ≅
      CategoryTheory.nerveFunctor.{v, u} ⋙
        SSet.toTop.{max u v} :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft CategoryTheory.nerveFunctor
      SSet.realizationToTopIso

end CategoryTheory
