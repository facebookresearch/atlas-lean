/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

import
  MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopySurjective

/-!
# Fundamental groupoids and simplicial realization

Realizing vertices and edges defines a functor from the combinatorial
fundamental groupoid of a simplicial set to the topological fundamental
groupoid of its geometric realization.  The composition law is supplied by
the realized homotopy of a simplicial `2`-simplex.  Surjectivity of simplicial
components onto realized path components makes this functor essentially
surjective.

This file proves no fullness, faithfulness, or categorical equivalence.  Those
claims require simplicial approximation for paths and endpoint-fixed path
homotopies, which is not provided here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- Geometric realization induces a functor from the simplicial fundamental
groupoid to the topological fundamental groupoid. -/
noncomputable def realizationFundamentalGroupoidFunctor (X : SSet.{u}) :
    SSet.FundamentalGroupoid X ⥤
      _root_.FundamentalGroupoid (SSet.toTop.obj X) :=
  SSet.FundamentalGroupoid.desc
    (fun x => _root_.FundamentalGroupoid.mk (SSet.realizedVertex x))
    (fun e => Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (SSet.realizedEdgePath e)))
    (fun h => by
      rw [_root_.FundamentalGroupoid.comp_eq,
        ← Path.Homotopic.Quotient.mk_trans]
      exact Path.Homotopic.Quotient.eq.mpr
        (SSet.realizedCompStructHomotopic h).symm)

/-- The realization functor sends a simplicial vertex representative to its
realized point. -/
@[simp]
theorem realizationFundamentalGroupoidFunctor_obj_mk
    (X : SSet.{u}) (x : X _⦋0⦌) :
    (realizationFundamentalGroupoidFunctor X).obj
        (SSet.FundamentalGroupoid.mk x) =
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex x) :=
  rfl

/-- The realization functor sends a simplicial edge representative to the
homotopy class of its realized path. -/
@[simp]
theorem realizationFundamentalGroupoidFunctor_map_homMk
    (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (realizationFundamentalGroupoidFunctor X).map
        (SSet.FundamentalGroupoid.homMk e) =
      Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv (SSet.realizedEdgePath e)) :=
  SSet.FundamentalGroupoid.desc_map_homMk _ _ _ e

/-- Every point of the realization is isomorphic to a realized simplicial
vertex, so the realization fundamental-groupoid functor is essentially
surjective. -/
theorem realizationFundamentalGroupoidFunctor_essSurj (X : SSet.{u}) :
    (realizationFundamentalGroupoidFunctor X).EssSurj := by
  constructor
  rintro ⟨y⟩
  obtain ⟨c, hc⟩ := SSet.piZeroToZerothHomotopy_surjective X
    (ZerothHomotopy.mk y)
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  rw [SSet.piZeroToZerothHomotopy_mk] at hc
  have hxy : Joined (SSet.realizedVertex x) y := Quotient.exact hc
  refine ⟨SSet.FundamentalGroupoid.mk x, ?_⟩
  change Nonempty
    (_root_.FundamentalGroupoid.mk (SSet.realizedVertex x) ≅
      _root_.FundamentalGroupoid.mk y)
  exact ⟨asIso (Path.Homotopic.Quotient.mk hxy.somePath)⟩

end SSet

end
