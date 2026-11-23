/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteRealization
public import MathlibExt.Topology.Category.CGWH.Point
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Zero-dimensional finite realizations in CGWH

This file identifies the finite realization of the zero-simplex with the
native point of `CGWH`, and proves directly that the realization of its
boundary is initial.  These statements are independent of any selected
model structure.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

universe u v

namespace SSet

/-- The finite CGWH realization of the boundary of the zero-simplex is
initial. -/
noncomputable def toCGWHOfFinite_boundary_zero_isInitial :
    IsInitial
      (SSet.toCGWHOfFinite (SSet.boundary.{v} 0) : CGWH.{u, v}) := by
  have hS : IsInitial (SSet.boundary.{v} 0 : SSet.{v}) := by
    simpa only [SSet.boundary_zero] using
      (SSet.Subcomplex.isInitialBot
        (X := (Δ[0] : SSet.{v})))
  letI : PreservesColimits SSet.toTop.{v} :=
    sSetTopAdj.leftAdjoint_preservesColimits
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

private noncomputable def stdSimplexZeroHomeoPUnit :
    Convexity.StdSimplex ℝ (Fin 1) ≃ₜ PUnit.{v + 1} where
  toFun _ := PUnit.unit
  invFun _ := Convexity.StdSimplex.single 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

/-- The finite CGWH realization of the zero-simplex is canonically
isomorphic to the native point. -/
noncomputable def toCGWHOfFinite_stdSimplex_zero_iso_point :
    (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v} := by
  apply CGWH.isoOfHomeo
  change SSet.toTop.obj (Δ[0] : SSet.{v}) ≃ₜ PUnit.{v + 1}
  exact (SimplexCategory.toTopHomeo (SimplexCategory.mk 0)).trans
    stdSimplexZeroHomeoPUnit

/-- The finite CGWH realization of the zero-simplex is terminal. -/
noncomputable def toCGWHOfFinite_stdSimplex_zero_isTerminal :
    IsTerminal
      (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) :=
  IsTerminal.ofIso CGWH.point_isTerminal
    toCGWHOfFinite_stdSimplex_zero_iso_point.symm

end SSet
