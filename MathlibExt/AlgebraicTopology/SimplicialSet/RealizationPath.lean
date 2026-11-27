/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import MathlibExt.Topology.Homotopy.TopCat.Path

/-!
# Realized vertices and edge paths

For a simplicial set `X`, a vertex `x : X _⦋0⦌` realizes to the point
`SSet.toTop.map (SSet.yonedaEquiv.symm x) default` in `|X|`, and an edge
`e : X.Edge x₀ x₁` realizes to a `TopCat.Path` in `|X|` with hom
`SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)`.

Orientation convention (do not flip): `δ 1` is the source face and points at
`0 : TopCat.I`, while `δ 0` is the target face and points at `1 : TopCat.I`.
This matches `SSet.Edge.src_eq` (`X.δ 1 e.edge = x₀`) and `SSet.Edge.tgt_eq`
(`X.δ 0 e.edge = x₁`).

Nonclaims: no strict pointed functoriality, no general realization-of-homotopy
statement, no loop-space, homotopy-group, weak-equivalence, Q/S-comparison,
spectral, or Milnor material. Hom-level naturality of realized edge paths is
proved here; realized-edge path naturality and composition coherence are left
to the consumer handoff and are not claimed here.
-/

@[expose] public section

open CategoryTheory Simplicial Convexity

universe u

namespace SSet

/-- A simplicial vertex realized as a point of `|X|`, via Yoneda and `default`. -/
noncomputable def realizedVertex {X : SSet.{u}} (x : X _⦋0⦌) : SSet.toTop.obj X :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x) default

/-- The realized vertex equals the constant-map realization, by `yonedaEquiv_symm_zero`. -/
theorem realizedVertex_eq_const {X : SSet.{u}} (x : X _⦋0⦌) :
    realizedVertex x =
      SSet.toTop.map (SSet.const x) (default : SSet.toTop.obj (Δ[0] : SSet.{u})) := by
  simp [realizedVertex]

/-- Simplicial-map naturality of the realized vertex. -/
@[simp]
theorem realizedVertex_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    realizedVertex (f.app _ x) = SSet.toTop.map f (realizedVertex x) := by
  unfold realizedVertex
  rw [← SSet.yonedaEquiv_symm_comp, Functor.map_comp]
  rfl

/-- The iso sends `0 : TopCat.I` to the `δ 1` vertex of `|Δ[1]|`. -/
theorem toTopObjIsoI_inv_zero :
    SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I.{u}) =
      SSet.toTop.map (SSet.stdSimplex.δ 1) default := by
  have hmap : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.stdSimplex.δ 1) default) = (0 : TopCat.I.{u}) := by
    have hvertex : (⦋1⦌.toTopHomeo
        (SSet.toTop.map (SSet.stdSimplex.δ 1) default)) =
        StdSimplex.single (0 : Fin 2) := by
      refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
      rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (StdSimplex.single 0),
        StdSimplex.map_single]
      rfl
    change TopCat.stdSimplexHomeomorphI (⦋1⦌.toTopHomeo
      (SSet.toTop.map (SSet.stdSimplex.δ 1) default)) = _
    rw [hvertex, TopCat.stdSimplexHomeomorphI_vertex_zero]
  have h := congrArg SSet.stdSimplex.toTopObjIsoI.inv hmap
  simpa [Iso.hom_inv_id] using h.symm

/-- The iso sends `1 : TopCat.I` to the `δ 0` vertex of `|Δ[1]|`. -/
theorem toTopObjIsoI_inv_one :
    SSet.stdSimplex.toTopObjIsoI.inv (1 : TopCat.I.{u}) =
      SSet.toTop.map (SSet.stdSimplex.δ 0) default := by
  have hmap : SSet.stdSimplex.toTopObjIsoI.hom
      (SSet.toTop.map (SSet.stdSimplex.δ 0) default) = (1 : TopCat.I.{u}) := by
    have hvertex : (⦋1⦌.toTopHomeo
        (SSet.toTop.map (SSet.stdSimplex.δ 0) default)) =
        StdSimplex.single (1 : Fin 2) := by
      refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
      rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (StdSimplex.single 0),
        StdSimplex.map_single]
      rfl
    change TopCat.stdSimplexHomeomorphI (⦋1⦌.toTopHomeo
      (SSet.toTop.map (SSet.stdSimplex.δ 0) default)) = _
    rw [hvertex, TopCat.stdSimplexHomeomorphI_vertex_one]
  have h := congrArg SSet.stdSimplex.toTopObjIsoI.inv hmap
  simpa [Iso.hom_inv_id] using h.symm

/-- A simplicial edge realized as a path between its realized endpoints.

The endpoints are inherent in the type: a `TopCat.Path` from
`realizedVertex x₀` to `realizedVertex x₁`. The `δ 1` face is the source
(`0 : TopCat.I`) and the `δ 0` face is the target (`1 : TopCat.I`). -/
noncomputable def realizedEdgePath {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    (e : X.Edge x₀ x₁) :
    (SSet.toTop.obj X).Path (realizedVertex x₀) (realizedVertex x₁) where
  hom :=
    SSet.stdSimplex.toTopObjIsoI.inv ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)
  hom₀ := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)
      (SSet.stdSimplex.toTopObjIsoI.inv (0 : TopCat.I)) = _
    rw [toTopObjIsoI_inv_zero]
    change (SSet.toTop.map (SSet.stdSimplex.δ 1) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) default = _
    rw [← Functor.map_comp,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq]
    rfl
  hom₁ := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)
      (SSet.stdSimplex.toTopObjIsoI.inv (1 : TopCat.I)) = _
    rw [toTopObjIsoI_inv_one]
    change (SSet.toTop.map (SSet.stdSimplex.δ 0) ≫
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) default = _
    rw [← Functor.map_comp,
      SSet.stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq]
    rfl

/-- The hom of the realized edge path, unfolded. -/
theorem realizedEdgePath_hom {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    (e : X.Edge x₀ x₁) :
    (realizedEdgePath e).hom =
      SSet.stdSimplex.toTopObjIsoI.inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) :=
  rfl

/-- Hom-level naturality of the realized edge path under a simplicial map. -/
@[simp]
theorem realizedEdgePath_naturality_hom {X Y : SSet.{u}} (f : X ⟶ Y)
    {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (realizedEdgePath (e.map f)).hom =
      (realizedEdgePath e).hom ≫ SSet.toTop.map f := by
  rw [realizedEdgePath_hom, SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp,
    Functor.map_comp, realizedEdgePath_hom, Category.assoc]

end SSet

end
