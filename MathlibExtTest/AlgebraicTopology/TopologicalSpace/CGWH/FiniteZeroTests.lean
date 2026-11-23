/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteZero

/-!
# Tests for zero-dimensional finite realizations in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

universe u v

namespace MathlibExtTest.CGWH.FiniteZeroTests

section PublicSurface

#check SSet.toCGWHOfFinite_boundary_zero_isInitial
#check SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
#check SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal

end PublicSurface

section Symbolic

example : IsInitial
    (SSet.toCGWHOfFinite (SSet.boundary.{v} 0) : CGWH.{u, v}) :=
  SSet.toCGWHOfFinite_boundary_zero_isInitial

example :
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v} :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point

example : IsTerminal
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) :=
  SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal

end Symbolic

section UniverseCorners

example : IsInitial
    (SSet.toCGWHOfFinite (SSet.boundary.{0} 0) : CGWH.{0, 0}) :=
  SSet.toCGWHOfFinite_boundary_zero_isInitial.{0, 0}

example : IsInitial
    (SSet.toCGWHOfFinite (SSet.boundary.{1} 0) : CGWH.{1, 1}) :=
  SSet.toCGWHOfFinite_boundary_zero_isInitial.{1, 1}

example : IsInitial
    (SSet.toCGWHOfFinite (SSet.boundary.{1} 0) : CGWH.{0, 1}) :=
  SSet.toCGWHOfFinite_boundary_zero_isInitial.{0, 1}

example : IsInitial
    (SSet.toCGWHOfFinite (SSet.boundary.{0} 0) : CGWH.{1, 0}) :=
  SSet.toCGWHOfFinite_boundary_zero_isInitial.{1, 0}

example :
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{0}) : CGWH.{0, 0}) ≅
      CGWH.point.{0, 0} :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{0, 0}

example :
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{1}) : CGWH.{1, 1}) ≅
      CGWH.point.{1, 1} :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{1, 1}

example :
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{1}) : CGWH.{0, 1}) ≅
      CGWH.point.{0, 1} :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{0, 1}

example :
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{0}) : CGWH.{1, 0}) ≅
      CGWH.point.{1, 0} :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{1, 0}

example : IsTerminal
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{0}) : CGWH.{0, 0}) :=
  SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal.{0, 0}

example : IsTerminal
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{1}) : CGWH.{1, 1}) :=
  SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal.{1, 1}

example : IsTerminal
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{1}) : CGWH.{0, 1}) :=
  SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal.{0, 1}

example : IsTerminal
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{0}) : CGWH.{1, 0}) :=
  SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal.{1, 0}

end UniverseCorners

section InitialityLeaves

example : IsInitial (SSet.boundary.{v} 0 : SSet.{v}) := by
  simpa only [SSet.boundary_zero] using
    (SSet.Subcomplex.isInitialBot
      (X := (Δ[0] : SSet.{v})))

example : IsInitial
    (SSet.toTop.obj (SSet.boundary.{v} 0 : SSet.{v})) := by
  letI : PreservesColimits SSet.toTop.{v} :=
    sSetTopAdj.leftAdjoint_preservesColimits
  have hS : IsInitial (SSet.boundary.{v} 0 : SSet.{v}) := by
    simpa only [SSet.boundary_zero] using
      (SSet.Subcomplex.isInitialBot
        (X := (Δ[0] : SSet.{v})))
  exact hS.isInitialObj SSet.toTop

example : IsInitial
    (SSet.toCGWHOfFinite (SSet.boundary.{v} 0) : CGWH.{u, v}) := by
  letI : PreservesColimits SSet.toTop.{v} :=
    sSetTopAdj.leftAdjoint_preservesColimits
  have hS : IsInitial (SSet.boundary.{v} 0 : SSet.{v}) := by
    simpa only [SSet.boundary_zero] using
      (SSet.Subcomplex.isInitialBot
        (X := (Δ[0] : SSet.{v})))
  have hReal : IsInitial
      (SSet.toTop.obj (SSet.boundary.{v} 0 : SSet.{v})) :=
    hS.isInitialObj SSet.toTop
  let A : CGWH.{u, v} :=
    SSet.toCGWHOfFinite (SSet.boundary.{v} 0)
  let F := CGWH.cgwhToTop.{u, v}
  let ff := CGWH.fullyFaithfulCgwhToTop.{u, v}
  have hTop : IsInitial (F.obj A) := by
    change IsInitial
      (SSet.toTop.obj (SSet.boundary.{v} 0 : SSet.{v}))
    exact hReal
  exact IsInitial.ofUniqueHom
    (fun X => ff.preimage (hTop.to (F.obj X)))
    (fun X f => ff.map_injective (by
      rw [ff.map_preimage]
      exact hTop.hom_ext (F.map f) (hTop.to (F.obj X))))

end InitialityLeaves

section PointFormulas

example : (CGWH.point.{u, v} : Type v) = PUnit.{v + 1} := rfl

example (x : (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v})) :
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.hom x =
      (PUnit.unit : PUnit.{v + 1}) :=
  rfl

example :
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv
        (PUnit.unit : PUnit.{v + 1}) =
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 0)).symm
        (Convexity.StdSimplex.single 0) :=
  rfl

example :
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.hom ≫
        SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv = 𝟙 _ :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.hom_inv_id

example :
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv ≫
        SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.hom = 𝟙 _ :=
  SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.inv_hom_id

end PointFormulas

section Negative

example : True := by
  fail_if_success
    have : IsTerminal
        (SSet.toCGWHOfFinite (SSet.boundary.{v} 0) : CGWH.{u, v}) :=
      SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal
  fail_if_success
    have : IsInitial
        (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) :=
      SSet.toCGWHOfFinite_boundary_zero_isInitial
  fail_if_success
    have :
        (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) =
          CGWH.point.{u, v} := rfl
  trivial

#guard_msgs (error, substring := true) in
#check SSet.stdSimplexZeroHomeoPUnit

end Negative

#print axioms SSet.toCGWHOfFinite_boundary_zero_isInitial
#print axioms SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
#print axioms SSet.toCGWHOfFinite_stdSimplex_zero_isTerminal

end MathlibExtTest.CGWH.FiniteZeroTests
