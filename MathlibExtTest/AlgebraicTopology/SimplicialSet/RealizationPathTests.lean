/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

@[expose] public section

/-!
# Realized simplicial edge path consumer tests

Focused downstream checks for the public `SSet.realizedVertex` /
`SSet.realizedEdgePath` API: vertex type and constant form, naturality under a
simplicial map, edge-path type (orientation), public hom formula, and
source/target endpoint equations via `TopCat.Path.hom₀` / `hom₁`. Uses only
public declarations; does not unfold endpoint helpers and introduces no
Quillen-specific API or implementation proofs.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizationPathTests

universe u

variable {X Y : SSet.{u}}

/-- Realized vertex has the inferred realized-point type. Catches inference drift. -/
noncomputable example (x : X _⦋0⦌) : SSet.toTop.obj X :=
  SSet.realizedVertex x

/-- Realized vertex equals the constant-map realization. Catches constant-form drift. -/
example (x : X _⦋0⦌) :
    SSet.realizedVertex x =
      SSet.toTop.map (SSet.const x) (default : SSet.toTop.obj (Δ[0] : SSet.{u})) :=
  SSet.realizedVertex_eq_const x

/-- Realized vertex is natural under a simplicial map. Catches naturality drift. -/
example (f : X ⟶ Y) (x : X _⦋0⦌) :
    SSet.realizedVertex (f.app _ x) = SSet.toTop.map f (SSet.realizedVertex x) :=
  SSet.realizedVertex_naturality f x

/-- Realized edge path has the oriented path type. Catches orientation drift. -/
noncomputable example {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (SSet.toTop.obj X).Path (SSet.realizedVertex x₀) (SSet.realizedVertex x₁) :=
  SSet.realizedEdgePath e

/-- Public hom formula for the realized edge path. Catches composition drift. -/
example {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (SSet.realizedEdgePath e).hom =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) :=
  SSet.realizedEdgePath_hom e

/-- Source endpoint of the realized edge path. Catches orientation drift. -/
example {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (SSet.realizedEdgePath e).hom (0 : TopCat.I.{u}) = SSet.realizedVertex x₀ :=
  (SSet.realizedEdgePath e).hom₀

/-- Target endpoint of the realized edge path. Catches orientation drift. -/
example {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (SSet.realizedEdgePath e).hom (1 : TopCat.I.{u}) = SSet.realizedVertex x₁ :=
  (SSet.realizedEdgePath e).hom₁

/-- Realized edge-path hom is natural under a simplicial map.
    Catches map/composition orientation drift. -/
example (f : X ⟶ Y) {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (SSet.realizedEdgePath (e.map f)).hom =
      (SSet.realizedEdgePath e).hom ≫ SSet.toTop.map f :=
  SSet.realizedEdgePath_naturality_hom f e

end MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizationPathTests

end
