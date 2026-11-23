/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration

/-!
# Actual point cofibrancy of a realized vertex

The original vertex map from Δ[0] is monic by its existing terminal-object
property. Its realization is a genuine model cofibration. The original
one-point realization Iso identifies it with the literal constant point map.
No CW/model/cofibration witness is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial TopCat.modelCategory

universe u

namespace SSet

/-- The literal marked-point map into any actual realization is cofibrant,
with the original canonical realized vertex as its value. -/
public theorem realizedVertex_pointMap_cofibration (K : SSet.{u}) (v : K _⦋0⦌) :
    Cofibration (TopCat.const (SSet.realizedVertex v) :
      TopCat.of PUnit.{u + 1} ⟶ SSet.toTop.obj K) := by
  let m : (Δ[0] : SSet.{u}) ⟶ K := SSet.const v
  letI : Mono m := SSet.stdSimplex.isTerminalObj₀.mono_from m
  letI : Cofibration (SSet.toTop.map m) :=
    (cofibration_iff _).mpr (SSet.toTop_map_mem_realizedBoundaryLLP m)
  let e : TopCat.of PUnit.{u + 1} ≅ SSet.toTop.obj (Δ[0] : SSet.{u}) :=
    TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique _ _)
  have he : e.hom ≫ SSet.toTop.map m =
      (TopCat.const (SSet.realizedVertex v) :
        TopCat.of PUnit.{u + 1} ⟶ SSet.toTop.obj K) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    exact (congrArg (SSet.toTop.map m)
      (Subsingleton.elim (e.hom a) (default : SSet.toTop.obj (Δ[0] : SSet.{u})))).trans
        (SSet.realizedVertex_eq_const v).symm
  rw [← he]
  infer_instance

end SSet

end
