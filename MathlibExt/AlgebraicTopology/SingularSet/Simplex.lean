/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# Singular simplices as continuous maps

This file exposes the continuous map represented by a singular simplex and its
naturality.
-/

@[expose] public section

universe w

open CategoryTheory

namespace TopCat

/-- The continuous map represented by a singular simplex. -/
noncomputable def toSSetTopHom (X : TopCat.{w})
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    SimplexCategory.toTop.{w}.obj n.unop ⟶ X :=
  ULift.down σ

/-- Naturality of `toSSetTopHom` in the simplex variable. -/
@[reassoc]
lemma toSSetTopHom_naturality_simplex {X : TopCat.{w}}
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (σ : (TopCat.toSSet.obj X).obj n) :
    TopCat.toSSetTopHom X m ((TopCat.toSSet.obj X).map f σ) =
      SimplexCategory.toTop.{w}.map f.unop ≫ TopCat.toSSetTopHom X n σ := by
  rfl

/-- Naturality of `toSSetTopHom` in the space variable. -/
@[reassoc]
lemma toSSetTopHom_naturality_space {X Y : TopCat.{w}}
    (f : X ⟶ Y) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    TopCat.toSSetTopHom X n σ ≫ f =
      TopCat.toSSetTopHom Y n (((TopCat.toSSet.map f).app n) σ) := by
  rfl

/-- `toSSetTopHom` composed with `uliftHomeo` recovers the adjunct. -/
lemma toSSetTopHom_comp_uliftHomeo {X : TopCat.{w}}
    {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) :
    (TopCat.toSSetTopHom X n σ).hom.comp
        ⟨(TopCat.uliftFunctorObjHomeo
          (SimplexCategory.toTop₀.obj n.unop)),
          (TopCat.uliftFunctorObjHomeo
            (SimplexCategory.toTop₀.obj n.unop)).continuous_toFun⟩ =
      X.toSSetObjEquiv n σ := by
  rfl

/-- Naturality of the singular-simplex equivalence in the space variable,
evaluated at a point. -/
lemma toSSetObjEquiv_map_apply {X Y : TopCat.{w}} (f : X ⟶ Y)
    {m : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj m)
    (z : Convexity.StdSimplex ℝ (Fin (m.unop.len + 1))) :
    Y.toSSetObjEquiv m ((TopCat.toSSet.map f).app m σ) z
      = f ((X.toSSetObjEquiv m σ) z) := rfl

end TopCat
