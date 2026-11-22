/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteZero
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Pointed simplicial-set realization in CGWH

Realization and singular complexes lift to the literal undercategories of
the zero simplex and the native CGWH point.  The base-change directions are
fixed by the canonical realization-of-`Δ[0]` isomorphism, and the resulting
adjunction is the generic undercategory adjunction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u v

namespace SSet

/-- Realization of a simplicial set with a chosen vertex as a pointed CGWH
space. -/
noncomputable def pointedToCGWH :
    Under (Δ[0] : SSet.{v}) ⥤ Under CGWH.point.{u, v} :=
  Under.post SSet.toCGWH.{u, v} ⋙
    Under.map
      (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv

end SSet

namespace CGWH

/-- The pointed singular complex, right adjoint to pointed realization. -/
noncomputable def pointedToSSet :
    Under CGWH.point.{u, v} ⥤ Under (Δ[0] : SSet.{v}) :=
  Under.map
      (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).hom ⋙
    Under.post
      (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}) ⋙
      Under.map
        (SSet.sSetCGWHAdj.{u, v}.unit.app
          (Δ[0] : SSet.{v}))

end CGWH

namespace SSet

/-- The adjunction between pointed simplicial sets and pointed CGWH
spaces. -/
noncomputable def pointedToCGWHAdjunction :
    SSet.pointedToCGWH.{u, v} ⊣ CGWH.pointedToSSet.{u, v} :=
  (Under.postAdjunctionLeft SSet.sSetCGWHAdj.{u, v}).comp
    (Under.mapIso
      SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}.symm).toAdjunction

/-- The point selected by pointed realization is the realized chosen
vertex. -/
theorem pointedToCGWH_basepoint
    (A : Under (Δ[0] : SSet.{v})) :
    (CGWH.cgwhToTop.{u, v}.map
        ((SSet.pointedToCGWH.{u, v}.obj A).hom) ≫
      (SSet.realizationToTopIso.{u, v}.app A.right).hom)
        PUnit.unit =
      SSet.realizedVertex (SSet.yonedaEquiv A.hom) := by
  change SSet.toTop.map A.hom
      (CGWH.cgwhToTop.map
        (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv
        PUnit.unit) = _
  have h₀ :
      CGWH.cgwhToTop.map
          (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv
          PUnit.unit =
        SSet.realizedVertex
          (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{v}))) :=
    @Subsingleton.elim
      (SSet.toTop.obj (Δ[0] : SSet.{v})) inferInstance _ _
  rw [h₀, ← SSet.realizedVertex_naturality]
  congr 1

end SSet
