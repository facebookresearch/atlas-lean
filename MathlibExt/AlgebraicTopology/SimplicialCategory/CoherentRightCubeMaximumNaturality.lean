/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeCosimplicial
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeMaximum

/-!
# Actual cosimplicial naturality of the original right-cube maximum

Every original right-join operator preserves the maximum-labelled front
simplex. The constructed quotient maximum maps therefore form a genuine
natural transformation to the standard cosimplicial simplex. Its
relative frame properties remain separate proofs.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.RightCubeMaximumNaturality
open PathLastMaximum
variable {n m : ℕ}

/-- The actual whole quotient maximum square commutes under each supplied original right-join operator. -/
theorem naturality (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    RightCubeCosimplicialMaps.map.{u} θ ≫ RightCubeMaximum.map m =
      RightCubeMaximum.map n ≫ SSet.stdSimplex.map θ := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    induction q using Opposite.rec with
    | _ q =>
      induction q using SimplexCategory.rec with
      | _ d =>
        apply SSet.stdSimplex.ext
        intro j
        exact RightCubeOperator.maximum_operator θ (a.obj j)

/-- The actual natural maximum map from the constructed original quotient-cube diagram to the standard
  cosimplicial simplex. -/
def map : RightCubeCosimplicial.diagram.{u} ⟶ SSet.stdSimplex.{u} where
  app n := RightCubeMaximum.map n.len
  naturality n m θ := by
    induction n using SimplexCategory.rec with
    | _ n =>
      induction m using SimplexCategory.rec with
      | _ m => exact naturality θ

end CategoryTheory.CoherentRealization.RightCubeMaximumNaturality
