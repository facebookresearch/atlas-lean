/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinOpposite

public section

open CategoryTheory
open scoped Simplicial

universe u

/-- Both differently sized factors retain their literal original inclusions. -/
example : SSet.opFunctor.map (SSet.joinInl (Δ[1] : SSet.{u}) Δ[2]) ≫
    (SSet.joinOppositeIso Δ[1] Δ[2]).hom = SSet.joinInr (Δ[2] : SSet.{u}).op Δ[1].op :=
  SSet.op_joinInl_comp_joinOppositeIso_hom _ _

example : SSet.opFunctor.map (SSet.joinInr (Δ[1] : SSet.{u}) Δ[2]) ≫
    (SSet.joinOppositeIso Δ[1] Δ[2]).hom = SSet.joinInl (Δ[2] : SSet.{u}).op Δ[1].op :=
  SSet.op_joinInr_comp_joinOppositeIso_hom _ _

/-- An actual face and an actual degeneracy are transported in their distinct factor roles. -/
example :
    SSet.opFunctor.map
      ((SSet.join.map (SSet.stdSimplex.δ (0 : Fin 3))).app (Δ[2] : SSet.{u}) ≫
        (SSet.join.obj (Δ[2] : SSet.{u})).map (SSet.stdSimplex.σ (1 : Fin 2))) ≫
      (SSet.joinOppositeIso (Δ[2] : SSet.{u}) Δ[1]).hom =
    (SSet.joinOppositeIso (Δ[1] : SSet.{u}) Δ[2]).hom ≫
      ((SSet.join.map (SSet.opFunctor.map (SSet.stdSimplex.σ (1 : Fin 2)))).app Δ[1].op ≫
        (SSet.join.obj (Δ[1] : SSet.{u}).op).map
          (SSet.opFunctor.map (SSet.stdSimplex.δ (0 : Fin 3)))) :=
  SSet.joinOppositeIso_hom_naturality _ _
