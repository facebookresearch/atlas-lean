/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Topology.Homotopy.TopCat.Path
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Path
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

/-!
# Realized composition structure as path homotopy

For a simplicial set `X`, a composition structure `h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂`
realizes to a `_root_.Path.Homotopic` between the realized direct edge `e₀₂` and the
concatenation of realized `e₀₁` then `e₁₂`, with orientation and endpoints exactly matching
`SSet.realizedEdgePath` (`δ 1` source at `0 : TopCat.I`, `δ 0` target at `1 : TopCat.I`) and
`_root_.Path.trans` (first path on `[0, 1/2]`, second on `[1/2, 1]`).

It also includes the degenerate identity-edge corollary, with the realized identity
edge shown endpoint-fixed homotopic to the constant path.

Bridge: reduce to the universal `Δ[2]` inner horn via `f := SSet.yonedaEquiv.symm h.simplex`, using
`SSet.stdSimplex.δ_comp_yonedaEquiv_symm`, `SSet.yonedaEquiv_symm_comp`, `Functor.map_comp`,
and the explicit Yoneda/functoriality equalities for transport with `Path.Homotopic.map` and
`Path.map_trans`. The universal `d₁` edge is homotopic to the `d₂`-then-`d₀` concatenation
by straight-line interpolation in the convex topological `2`-simplex
(`Convexity.convexCombPair` via `convexHomotopy₂`), transferred across `⦋2⦌.toTopHomeo`
with `Path.map` and back along its inverse. Endpoint alignment uses `pathCast`/`cast_trans`
with `realizedVertex_naturality`; no ad-hoc time-warp.

Universe generality: the statement is in `SSet.{u}`. The topological filler lives
in `Convexity.StdSimplex ℝ (Fin 3) : Type 0`; transport uses `TopCat.pathEquiv`.

Nonclaims: no strict path/hom equality (direct `d₁` vs `1/2`-split concatenation differ by
parametrization), no general realization of simplicial homotopies (one explicit `2`-simplex
only), no filling/anodyne/weak-equivalence/model-category, loop/`K`-group, `Q`/`S`, or spectrum
results. No strict pointed functoriality (endpoint-fixing only).
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial unitInterval

universe u

namespace SSet

/-- Straight-line homotopy between two paths sharing endpoints in the convex `2`-simplex.

Given `p q : Path v₀ v₂` in `Convexity.StdSimplex ℝ (Fin 3)`, binary convex combination
with weights `(1 - t, t)` stays in the simplex by `Convexity.convexCombPair` and fixes
`{0, 1}` since both paths share endpoints. -/
private noncomputable def convexHomotopy₂
    {v₀ v₂ : Convexity.StdSimplex ℝ (Fin 3)}
    (p q : Path v₀ v₂) : p.Homotopy q where
  toFun x :=
    Convexity.convexCombPair (1 - (x.1 : ℝ)) (x.1 : ℝ) (by unit_interval)
      (by unit_interval) (by simp) (p x.2) (q x.2)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
    unfold Function.comp
    refine continuous_pi (fun i => ?_)
    have hp : Continuous (fun x : I × I => (p x.2).weights i) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
        (p.continuous.comp continuous_snd)
    have hq : Continuous (fun x : I × I => (q x.2).weights i) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
        (q.continuous.comp continuous_snd)
    have h1 : Continuous (fun x : I × I => (1 - (x.1 : ℝ))) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous (fun x : I × I => (x.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hEq : (fun x : I × I =>
        ((Convexity.convexCombPair (1 - (x.1 : ℝ)) (x.1 : ℝ) (by unit_interval)
          (by unit_interval) (by simp) (p x.2) (q x.2)).weights i)) =
        (fun x : I × I =>
          (1 - (x.1 : ℝ)) * (p x.2).weights i + (x.1 : ℝ) * (q x.2).weights i) := by
      funext x
      simp [Convexity.StdSimplex.weights_convexCombPair, smul_eq_mul]
    rw [hEq]
    exact (h1.mul hp).add (h2.mul hq)
  map_zero_left x := by
    simp
  map_one_left x := by
    simp
  prop' t x hx := by
    rcases hx with rfl | hx
    · simp [p.source, q.source, Convexity.convexCombPair_same]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      simp [p.target, q.target, Convexity.convexCombPair_same]

/-- Universal vertices of `Δ[2]`, via `obj₀Equiv`. Shared so `Path.trans` typechecks. -/
private noncomputable def univVertex₀ : (Δ[2] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 3)

private noncomputable def univVertex₁ : (Δ[2] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.{u}.symm (1 : Fin 3)

private noncomputable def univVertex₂ : (Δ[2] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.{u}.symm (2 : Fin 3)

/-- Universal edges from the `1`-skeleton of `Δ[2]`, via `Edge.mk` over shared vertices.
Orientation follows `Edge.src_eq`/`tgt_eq` (`δ 1` source, `δ 0` target). -/
private noncomputable def univEdge₀₁ : (Δ[2] : SSet.{u}).Edge univVertex₀.{u} univVertex₁.{u} :=
  SSet.Edge.mk (SSet.stdSimplex.edge.{u} 2 (0 : Fin 3) (1 : Fin 3) (by decide))
    (by decide) (by decide)

private noncomputable def univEdge₁₂ : (Δ[2] : SSet.{u}).Edge univVertex₁.{u} univVertex₂.{u} :=
  SSet.Edge.mk (SSet.stdSimplex.edge.{u} 2 (1 : Fin 3) (2 : Fin 3) (by decide))
    (by decide) (by decide)

private noncomputable def univEdge₀₂ : (Δ[2] : SSet.{u}).Edge univVertex₀.{u} univVertex₂.{u} :=
  SSet.Edge.mk (SSet.stdSimplex.edge.{u} 2 (0 : Fin 3) (2 : Fin 3) (by decide))
    (by decide) (by decide)

/-- Universal realized homotopy in `|Δ[2]|`: the direct edge is homotopic to the concatenation.

Proof: transfer the three realized universal paths across `⦋2⦌.toTopHomeo` to the convex
`Convexity.StdSimplex ℝ (Fin 3)` type via `Path.map`, apply `convexHomotopy₂` (both sides share
realized-vertex endpoints by `hom₀`/`hom₁`), then map back along the inverse homeomorphism
and close with `Path.map_trans`. Claims only `Homotopic`. -/
private theorem univRealizedHomotopic₂ :
    (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₂.{u})).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{u})).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{u}))) := by
  let φ := (⦋2⦌.toTopHomeo.{u} : |(Δ[2] : SSet.{u})| ≃ₜ Convexity.StdSimplex ℝ (Fin 3))
  let q₀₂ := (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₂.{u})).map φ.continuous_toFun
  let q₀₁ := (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{u})).map φ.continuous_toFun
  let q₁₂ := (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{u})).map φ.continuous_toFun
  have hHomotopic : q₀₂.Homotopic (q₀₁.trans q₁₂) :=
    ⟨convexHomotopy₂ q₀₂ (q₀₁.trans q₁₂)⟩
  have hBack := hHomotopic.map ⟨φ.symm, φ.symm.continuous_toFun⟩
  rw [Path.map_trans] at hBack
  have e₀ : φ.symm (φ.toFun (realizedVertex univVertex₀.{u})) = realizedVertex univVertex₀.{u} := by
    simp
  have e₁ : φ.symm (φ.toFun (realizedVertex univVertex₁.{u})) = realizedVertex univVertex₁.{u} := by
    simp
  have e₂ : φ.symm (φ.toFun (realizedVertex univVertex₂.{u})) = realizedVertex univVertex₂.{u} := by
    simp
  have hCast := hBack.pathCast e₀.symm e₂.symm
  rw [Path.cast_trans _ _ e₀.symm e₁.symm e₂.symm] at hCast
  have h₀₂ : ((q₀₂.map φ.symm.continuous_toFun).cast e₀.symm e₂.symm) =
      (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₂.{u})) := by
    ext t
    simp [q₀₂, Path.map_coe, Path.cast_coe, Function.comp_apply]
  have h₀₁ : ((q₀₁.map φ.symm.continuous_toFun).cast e₀.symm e₁.symm) =
      (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{u})) := by
    ext t
    simp [q₀₁, Path.map_coe, Path.cast_coe, Function.comp_apply]
  have h₁₂ : ((q₁₂.map φ.symm.continuous_toFun).cast e₁.symm e₂.symm) =
      (TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{u})) := by
    ext t
    simp [q₁₂, Path.map_coe, Path.cast_coe, Function.comp_apply]
  rw [h₀₂, h₀₁, h₁₂] at hCast
  exact hCast

/-- Realized composition structure as path homotopy (universe-polymorphic).

From `h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂` in `SSet.{u}`, the realized direct edge is
`Path.Homotopic` to the concatenation of realized `e₀₁` then `e₁₂`, with orientation and
endpoints exactly matching `realizedEdgePath` and `Path.trans`. Both sides are
`_root_.Path (realizedVertex x₀) (realizedVertex x₂)`. -/
theorem realizedCompStructHomotopic {X : SSet.{u}}
    {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    (TopCat.pathEquiv (SSet.realizedEdgePath e₀₂)).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath e₀₁)).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath e₁₂))) := by
  let f : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.{u}.symm h.simplex
  have hMap := univRealizedHomotopic₂.{u}.map (SSet.toTop.map f).hom
  rw [Path.map_trans] at hMap
  have hY₀₁ : SSet.yonedaEquiv.{u}.symm (univEdge₀₁.{u}.edge) = SSet.stdSimplex.{u}.δ 2 := by
    decide
  have hY₁₂ : SSet.yonedaEquiv.{u}.symm (univEdge₁₂.{u}.edge) = SSet.stdSimplex.{u}.δ 0 := by
    decide
  have hY₀₂ : SSet.yonedaEquiv.{u}.symm (univEdge₀₂.{u}.edge) = SSet.stdSimplex.{u}.δ 1 := by
    decide
  have e₀₁Eq : (univEdge₀₁.{u}.map f).edge = e₀₁.edge := by
    apply SSet.yonedaEquiv.{u}.symm.injective
    rw [SSet.Edge.map_edge.{u}, ← SSet.yonedaEquiv_symm_comp.{u}, hY₀₁]
    simp [f, SSet.stdSimplex.δ_comp_yonedaEquiv_symm.{u}]
  have e₁₂Eq : (univEdge₁₂.{u}.map f).edge = e₁₂.edge := by
    apply SSet.yonedaEquiv.{u}.symm.injective
    rw [SSet.Edge.map_edge.{u}, ← SSet.yonedaEquiv_symm_comp.{u}, hY₁₂]
    simp [f, SSet.stdSimplex.δ_comp_yonedaEquiv_symm.{u}]
  have e₀₂Eq : (univEdge₀₂.{u}.map f).edge = e₀₂.edge := by
    apply SSet.yonedaEquiv.{u}.symm.injective
    rw [SSet.Edge.map_edge.{u}, ← SSet.yonedaEquiv_symm_comp.{u}, hY₀₂]
    simp [f, SSet.stdSimplex.δ_comp_yonedaEquiv_symm.{u}]
  have hv₀ : f.app _ univVertex₀.{u} = x₀ := by
    have h1 := (univEdge₀₁.{u}.map f).src_eq
    rw [e₀₁Eq, e₀₁.src_eq] at h1
    exact h1.symm
  have hv₁ : f.app _ univVertex₁.{u} = x₁ := by
    have h1 := (univEdge₀₁.{u}.map f).tgt_eq
    rw [e₀₁Eq, e₀₁.tgt_eq] at h1
    exact h1.symm
  have hv₂ : f.app _ univVertex₂.{u} = x₂ := by
    have h1 := (univEdge₁₂.{u}.map f).tgt_eq
    rw [e₁₂Eq, e₁₂.tgt_eq] at h1
    exact h1.symm
  have he₀ : realizedVertex x₀ = (SSet.toTop.map f) (realizedVertex univVertex₀.{u}) := by
    simp [← hv₀, SSet.realizedVertex_naturality]
  have he₁ : realizedVertex x₁ = (SSet.toTop.map f) (realizedVertex univVertex₁.{u}) := by
    simp [← hv₁, SSet.realizedVertex_naturality]
  have he₂ : realizedVertex x₂ = (SSet.toTop.map f) (realizedVertex univVertex₂.{u}) := by
    simp [← hv₂, SSet.realizedVertex_naturality]
  have hCast := hMap.pathCast he₀ he₂
  rw [Path.cast_trans _ _ he₀ he₁ he₂] at hCast
  have hComp₀₂ : (SSet.yonedaEquiv.{u}.symm univEdge₀₂.{u}.edge ≫ f) =
      SSet.yonedaEquiv.{u}.symm e₀₂.edge := by
    rw [SSet.yonedaEquiv_symm_comp.{u}, ← SSet.Edge.map_edge.{u}, e₀₂Eq]
  have hTop₀₂ : (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm univEdge₀₂.{u}.edge) ≫
      SSet.toTop.map f) = SSet.toTop.map (SSet.yonedaEquiv.{u}.symm e₀₂.edge) := by
    rw [← Functor.map_comp, hComp₀₂]
  have hFun₀₂ (y) : TopCat.Hom.hom (SSet.toTop.map f)
      (TopCat.Hom.hom (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm univEdge₀₂.{u}.edge)) y) =
      TopCat.Hom.hom (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm e₀₂.edge)) y := by
    have h := congrArg (fun g => TopCat.Hom.hom g y) hTop₀₂
    simpa using h
  have hp₀₂ : ((((TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₂.{u})).map
      (SSet.toTop.map f).hom.continuous).cast he₀ he₂)) =
      (TopCat.pathEquiv (SSet.realizedEdgePath e₀₂)) := by
    ext t
    simp [TopCat.pathEquiv, Path.map_coe, Path.cast_coe, Function.comp_apply,
      SSet.realizedEdgePath_hom, hFun₀₂]
  have hComp₀₁ : (SSet.yonedaEquiv.{u}.symm univEdge₀₁.{u}.edge ≫ f) =
      SSet.yonedaEquiv.{u}.symm e₀₁.edge := by
    rw [SSet.yonedaEquiv_symm_comp.{u}, ← SSet.Edge.map_edge.{u}, e₀₁Eq]
  have hTop₀₁ : (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm univEdge₀₁.{u}.edge) ≫
      SSet.toTop.map f) = SSet.toTop.map (SSet.yonedaEquiv.{u}.symm e₀₁.edge) := by
    rw [← Functor.map_comp, hComp₀₁]
  have hFun₀₁ (y) : TopCat.Hom.hom (SSet.toTop.map f)
      (TopCat.Hom.hom (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm univEdge₀₁.{u}.edge)) y) =
      TopCat.Hom.hom (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm e₀₁.edge)) y := by
    have h := congrArg (fun g => TopCat.Hom.hom g y) hTop₀₁
    simpa using h
  have hp₀₁ : ((((TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{u})).map
      (SSet.toTop.map f).hom.continuous).cast he₀ he₁)) =
      (TopCat.pathEquiv (SSet.realizedEdgePath e₀₁)) := by
    ext t
    simp [TopCat.pathEquiv, Path.map_coe, Path.cast_coe, Function.comp_apply,
      SSet.realizedEdgePath_hom, hFun₀₁]
  have hComp₁₂ : (SSet.yonedaEquiv.{u}.symm univEdge₁₂.{u}.edge ≫ f) =
      SSet.yonedaEquiv.{u}.symm e₁₂.edge := by
    rw [SSet.yonedaEquiv_symm_comp.{u}, ← SSet.Edge.map_edge.{u}, e₁₂Eq]
  have hTop₁₂ : (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm univEdge₁₂.{u}.edge) ≫
      SSet.toTop.map f) = SSet.toTop.map (SSet.yonedaEquiv.{u}.symm e₁₂.edge) := by
    rw [← Functor.map_comp, hComp₁₂]
  have hFun₁₂ (y) : TopCat.Hom.hom (SSet.toTop.map f)
      (TopCat.Hom.hom (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm univEdge₁₂.{u}.edge)) y) =
      TopCat.Hom.hom (SSet.toTop.map (SSet.yonedaEquiv.{u}.symm e₁₂.edge)) y := by
    have h := congrArg (fun g => TopCat.Hom.hom g y) hTop₁₂
    simpa using h
  have hp₁₂ : ((((TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{u})).map
      (SSet.toTop.map f).hom.continuous).cast he₁ he₂)) =
      (TopCat.pathEquiv (SSet.realizedEdgePath e₁₂)) := by
    ext t
    simp [TopCat.pathEquiv, Path.map_coe, Path.cast_coe, Function.comp_apply,
      SSet.realizedEdgePath_hom, hFun₁₂]
  rw [hp₀₂, hp₀₁, hp₁₂] at hCast
  exact hCast

/-- The realized identity edge is strictly the constant path. -/
theorem realizedEdgePath_id_eq_refl {X : SSet.{u}} (x : X _⦋0⦌) :
    TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id x)) =
      _root_.Path.refl (SSet.realizedVertex x) := by
  have hEdge : (SSet.Edge.id x).edge = X.σ (0 : Fin 1) x :=
    SSet.Edge.id_edge x
  have hYoneda : SSet.yonedaEquiv.symm (X.σ (0 : Fin 1) x) =
      SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.yonedaEquiv.symm x :=
    (SSet.stdSimplex.σ_comp_yonedaEquiv_symm x _).symm
  have hVert : SSet.realizedVertex x =
      SSet.toTop.map (SSet.yonedaEquiv.symm x) default := rfl
  apply _root_.Path.ext
  ext t
  change (SSet.realizedEdgePath (SSet.Edge.id x)).hom.hom
      (TopCat.I.homeomorph.symm t) = SSet.realizedVertex x
  rw [SSet.realizedEdgePath_hom, hEdge, hYoneda, Functor.map_comp]
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
  rw [hVert]
  exact congrArg _ (Subsingleton.elim _ _)


/-- Degenerate realized edge path is null-homotopic (universe-polymorphic).

For `x : X _⦋0⦌` in `SSet.{u}`, the realized identity edge path is endpoint-fixed
homotopic to the constant path at the realized vertex. Orientation matches
`SSet.realizedEdgePath` (`δ 1` source at `0 : TopCat.I`, `δ 0` target at
`1 : TopCat.I`) and `_root_.Path.trans` (first path on `[0, 1/2]`, second on
`[1/2, 1]`); both sides are `_root_.Path (realizedVertex x) (realizedVertex x)`.

Proof factors the identity edge through `Δ[0]` via `SSet.Edge.id_edge` and
`SSet.stdSimplex.σ_comp_yonedaEquiv_symm`, shows the realized path equals
`Path.refl` by `Path.ext` with the subsingleton `|Δ[0]|` domain, and concludes
by reflexive homotopy.
No K-theory-specific assumption.

Nonclaims: no general realization-of-simplicial-homotopy,
no additivity or `π₀` claim. -/
theorem realizedEdgePath_id_homotopic {X : SSet.{u}} (x : X _⦋0⦌) :
    (TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id x))).Homotopic
      (Path.refl (SSet.realizedVertex x)) := by
  rw [realizedEdgePath_id_eq_refl]

end SSet

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial ContinuousMap unitInterval

namespace SSet

private def finitePrismProductBridge (X K : SSet.{u}) :
    ((Limits.prod.functor.obj X).obj K) ≅ (X ⨯ K) :=
  Iso.refl _

@[reassoc]
private theorem finitePrismProductBridge_tensor_naturality
    (X : SSet.{u}) {K L : SSet.{u}} (f : K ⟶ L) :
    Limits.prod.map (𝟙 X) f ≫ (finitePrismProductBridge X L).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app L =
      (finitePrismProductBridge X K).inv ≫
        (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K ≫ (X ◁ f) := by
  change (Limits.prod.functor.obj X).map f ≫
      (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app L =
    (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app K ≫
      (MonoidalCategory.tensorLeft X).map f
  exact (CartesianMonoidalCategory.tensorLeftIsoProd X).inv.naturality f

private def finitePrismProductIso (X : SSet.{u}) (n : ℕ) :
    SSet.toTop.obj (X ⨯ (Δ[n] : SSet.{u})) ≅
      SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[n] : SSet.{u}) := by
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[n] : SSet.{u}) X) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let hIso : IsIso (Limits.prodComparison SSet.toTop
      X (Δ[n] : SSet.{u})) :=
    SSet.isIso_prodComparison_swap _ _
  exact @asIso _ _ _ _ (Limits.prodComparison SSet.toTop
    X (Δ[n] : SSet.{u})) hIso

private theorem finitePrismProductIso_hom (X : SSet.{u}) (n : ℕ) :
    (finitePrismProductIso X n).hom =
      Limits.prodComparison SSet.toTop X (Δ[n] : SSet.{u}) := by
  rfl

/-- The original ordinary product comparison needs only the finite
parameter simplex; the entire active simplicial carrier remains arbitrary. -/
private def finitePrismEvaluation {X Y : SSet.{u}} {n : ℕ}
    (Φ : X ⊗ (Δ[n] : SSet.{u}) ⟶ Y) :
    SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶
      SSet.toTop.obj Y :=
  (finitePrismProductIso X n).inv ≫
    SSet.toTop.map (finitePrismProductBridge X (Δ[n] : SSet.{u})).inv ≫
    SSet.toTop.map
      ((CartesianMonoidalCategory.tensorLeftIsoProd X).inv.app (Δ[n] : SSet.{u})) ≫
    SSet.toTop.map Φ

private theorem finitePrismEvaluation_face
    {X Y : SSet.{u}} {n : ℕ}
    (Φ : X ⊗ (Δ[n + 1] : SSet.{u}) ⟶ Y) (i : Fin (n + 2)) :
    Limits.prod.map (𝟙 (SSet.toTop.obj X))
        (SSet.toTop.map (stdSimplex.δ i)) ≫ finitePrismEvaluation Φ =
      finitePrismEvaluation ((X ◁ stdSimplex.δ i) ≫ Φ) := by
  apply (cancel_epi (finitePrismProductIso X n).hom).mp
  rw [finitePrismProductIso_hom]
  rw [← SSet.toTop.map_id]
  rw [← Category.assoc, ← Limits.prodComparison_natural]
  unfold finitePrismEvaluation
  rw [← finitePrismProductIso_hom X (n + 1)]
  rw [← finitePrismProductIso_hom X n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [← Functor.map_comp]
  rw [finitePrismProductBridge_tensor_naturality_assoc]

private theorem finitePrismEvaluation_realizeHomotopyMap
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.realizeHomotopyMap X Y f g H =
      (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj X))
          SSet.stdSimplex.toTopObjIsoI.inv ≫ finitePrismEvaluation H.h := by
  unfold SSet.realizeHomotopyMap finitePrismEvaluation
  rfl

/-- This formula compares the WHOLE original realization family, with
its original interval clock and original product point, to prism evaluation. -/
private theorem finitePrismEvaluation_realizeHomotopy_apply
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (x : SSet.toTop.obj X) (t : unitInterval) :
    finitePrismEvaluation H.h
        ((TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
            (x, SSet.stdSimplex.toTopObjIsoI.inv (TopCat.I.homeomorph.symm t))) =
      (SSet.realizeHomotopy X Y f g H).toContinuousMap (t, x) := by
  let τ := TopCat.I.homeomorph.{u}.symm t
  let b := (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom
  have hbValue : b = (Limits.prod.braiding TopCat.I.{u} (SSet.toTop.obj X)).hom := rfl
  let q := (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj X)).inv (τ, x)
  have hBraid : b q =
      (TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv (x, τ) := by
    apply TopCat.prod_point_ext
    · have hb : b ≫
          (Limits.prod.fst : SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ SSet.toTop.obj X) =
        (Limits.prod.snd : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X) := by
        rw [hbValue, Limits.prod.braiding_hom, Limits.prod.lift_fst]
      calc
        (Limits.prod.fst : SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ SSet.toTop.obj X) (b q) =
            (Limits.prod.snd : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ SSet.toTop.obj X) q :=
          ConcreteCategory.congr_hom hb q
        _ = x := ConcreteCategory.congr_hom
          (TopCat.prodIsoProd_inv_snd TopCat.I.{u} (SSet.toTop.obj X)) (τ, x)
        _ = (Limits.prod.fst :
            SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ SSet.toTop.obj X)
              ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv (x, τ)) :=
          (ConcreteCategory.congr_hom
            (TopCat.prodIsoProd_inv_fst (SSet.toTop.obj X) TopCat.I.{u}) (x, τ)).symm
    · have hb : b ≫
          (Limits.prod.snd : SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ TopCat.I.{u}) =
        (Limits.prod.fst : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ TopCat.I.{u}) := by
        rw [hbValue, Limits.prod.braiding_hom, Limits.prod.lift_snd]
      calc
        (Limits.prod.snd : SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ TopCat.I.{u}) (b q) =
            (Limits.prod.fst : TopCat.I.{u} ⨯ SSet.toTop.obj X ⟶ TopCat.I.{u}) q :=
          ConcreteCategory.congr_hom hb q
        _ = τ := ConcreteCategory.congr_hom
          (TopCat.prodIsoProd_inv_fst TopCat.I.{u} (SSet.toTop.obj X)) (τ, x)
        _ = (Limits.prod.snd : SSet.toTop.obj X ⨯ TopCat.I.{u} ⟶ TopCat.I.{u})
              ((TopCat.prodIsoProd (SSet.toTop.obj X) TopCat.I.{u}).inv (x, τ)) :=
          (ConcreteCategory.congr_hom
            (TopCat.prodIsoProd_inv_snd (SSet.toTop.obj X) TopCat.I.{u}) (x, τ)).symm
  change finitePrismEvaluation H.h
      ((TopCat.prodIsoProd (SSet.toTop.obj X)
        (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
          (x, SSet.stdSimplex.toTopObjIsoI.inv τ)) =
    SSet.realizeHomotopyMap X Y f g H q
  rw [finitePrismEvaluation_realizeHomotopyMap]
  simp only [ConcreteCategory.comp_apply]
  rw [hBraid, TopCat.prodMap_prodIso_inv_apply]

private theorem finitePrismEvaluation_edge_apply
    {X Y : SSet.{u}} (Φ : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (i : Fin 3) (x : SSet.toTop.obj X) (t : unitInterval) :
    finitePrismEvaluation Φ
        ((TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[2] : SSet.{u}))).inv
            (x, SSet.toTop.map (stdSimplex.δ i)
              (stdSimplex.toTopObjIsoI.inv (TopCat.I.homeomorph.symm t)))) =
      finitePrismEvaluation ((X ◁ stdSimplex.δ i) ≫ Φ)
        ((TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv
            (x, stdSimplex.toTopObjIsoI.inv (TopCat.I.homeomorph.symm t))) := by
  let τ : SSet.toTop.obj (Δ[1] : SSet.{u}) :=
    stdSimplex.toTopObjIsoI.inv (TopCat.I.homeomorph.symm t)
  have hPoint :
      (Limits.prod.map (𝟙 (SSet.toTop.obj X)) (SSet.toTop.map (stdSimplex.δ i)))
          ((TopCat.prodIsoProd (SSet.toTop.obj X)
            (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv (x, τ)) =
        (TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[2] : SSet.{u}))).inv
            (x, SSet.toTop.map (stdSimplex.δ i) τ) :=
    TopCat.prodMap_prodIso_inv_apply
      (K := SSet.toTop.obj X)
      (X := SSet.toTop.obj (Δ[1] : SSet.{u}))
      (Y := SSet.toTop.obj (Δ[2] : SSet.{u}))
      (SSet.toTop.map (stdSimplex.δ i)) x τ
  have hFace :
      finitePrismEvaluation Φ
          ((Limits.prod.map (𝟙 (SSet.toTop.obj X)) (SSet.toTop.map (stdSimplex.δ i)))
            ((TopCat.prodIsoProd (SSet.toTop.obj X)
              (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv (x, τ))) =
        finitePrismEvaluation ((X ◁ stdSimplex.δ i) ≫ Φ)
          ((TopCat.prodIsoProd (SSet.toTop.obj X)
            (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv (x, τ)) := by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (finitePrismEvaluation_face Φ i)
        ((TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[1] : SSet.{u}))).inv (x, τ))
  exact (congrArg (fun z => finitePrismEvaluation Φ z) hPoint.symm).trans hFace

/-- An actual finite-parameter two-simplex prism compares the WHOLE
original long-edge realization with the WHOLE original pasted realizations.
The resulting two-parameter family fixes BOTH entire original endpoint
faces, for every point of an arbitrary active simplicial carrier. The only
compatibility inputs are the raw prism's three literal cylinder faces. -/
public def realizedPrismCompositionHomotopy
    {X Y : SSet.{u}} {f g h : X ⟶ Y}
    (Φ : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (H₀₁ : SSet.Homotopy f g) (H₁₂ : SSet.Homotopy g h)
    (H₀₂ : SSet.Homotopy f h)
    (h₀₁ : (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ Φ = H₀₁.h)
    (h₁₂ : (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ Φ = H₁₂.h)
    (h₀₂ : (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ Φ = H₀₂.h) :
    ContinuousMap.HomotopyRel
      (SSet.realizeHomotopy X Y f h H₀₂).toContinuousMap
      ((SSet.realizeHomotopy X Y f g H₀₁).trans
        (SSet.realizeHomotopy X Y g h H₁₂)).toContinuousMap
      (Set.ofPred (fun z : unitInterval × SSet.toTop.obj X => z.1 = 0 ∨ z.1 = 1)) := by
  let L := univRealizedHomotopic₂.{u}.some
  let p₀₂ := TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₂.{u})
  let p₀₁ := TopCat.pathEquiv (SSet.realizedEdgePath univEdge₀₁.{u})
  let p₁₂ := TopCat.pathEquiv (SSet.realizedEdgePath univEdge₁₂.{u})
  let e := finitePrismEvaluation Φ
  let q := TopCat.prodIsoProd (SSet.toTop.obj X)
    (SSet.toTop.obj (Δ[2] : SSet.{u}))
  have hy₀₂ : SSet.yonedaEquiv.symm univEdge₀₂.{u}.edge =
      stdSimplex.δ (1 : Fin 3) := by decide
  have hy₀₁ : SSet.yonedaEquiv.symm univEdge₀₁.{u}.edge =
      stdSimplex.δ (2 : Fin 3) := by decide
  have hy₁₂ : SSet.yonedaEquiv.symm univEdge₁₂.{u}.edge =
      stdSimplex.δ (0 : Fin 3) := by decide
  have hDirect (x : SSet.toTop.obj X) (t : unitInterval) :
      e (q.inv (x, p₀₂ t)) =
        (SSet.realizeHomotopy X Y f h H₀₂).toContinuousMap (t, x) := by
    change finitePrismEvaluation Φ
        (q.inv (x, (SSet.realizedEdgePath univEdge₀₂.{u}).hom
          (TopCat.I.homeomorph.symm t))) = _
    rw [SSet.realizedEdgePath_hom, hy₀₂]
    have hFace := finitePrismEvaluation_edge_apply Φ (1 : Fin 3) x t
    rw [h₀₂] at hFace
    exact hFace.trans (finitePrismEvaluation_realizeHomotopy_apply H₀₂ x t)
  have hFirst (x : SSet.toTop.obj X) (t : unitInterval) :
      e (q.inv (x, p₀₁ t)) =
        (SSet.realizeHomotopy X Y f g H₀₁).toContinuousMap (t, x) := by
    change finitePrismEvaluation Φ
        (q.inv (x, (SSet.realizedEdgePath univEdge₀₁.{u}).hom
          (TopCat.I.homeomorph.symm t))) = _
    rw [SSet.realizedEdgePath_hom, hy₀₁]
    have hFace := finitePrismEvaluation_edge_apply Φ (2 : Fin 3) x t
    rw [h₀₁] at hFace
    exact hFace.trans (finitePrismEvaluation_realizeHomotopy_apply H₀₁ x t)
  have hSecond (x : SSet.toTop.obj X) (t : unitInterval) :
      e (q.inv (x, p₁₂ t)) =
        (SSet.realizeHomotopy X Y g h H₁₂).toContinuousMap (t, x) := by
    change finitePrismEvaluation Φ
        (q.inv (x, (SSet.realizedEdgePath univEdge₁₂.{u}).hom
          (TopCat.I.homeomorph.symm t))) = _
    rw [SSet.realizedEdgePath_hom, hy₁₂]
    have hFace := finitePrismEvaluation_edge_apply Φ (0 : Fin 3) x t
    rw [h₁₂] at hFace
    exact hFace.trans (finitePrismEvaluation_realizeHomotopy_apply H₁₂ x t)
  let F : C(unitInterval × (unitInterval × SSet.toTop.obj X), SSet.toTop.obj Y) :=
    { toFun := fun z => e (q.inv (z.2.2, L (z.1, z.2.1)))
      continuous_toFun := e.hom.continuous.comp
        (q.inv.hom.continuous.comp
          ((continuous_snd.comp continuous_snd).prodMk
            (L.continuous.comp
              (continuous_fst.prodMk (continuous_fst.comp continuous_snd))))) }
  refine
    { toContinuousMap := F
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro z
    change e (q.inv (z.2, L (0, z.1))) =
      (SSet.realizeHomotopy X Y f h H₀₂).toContinuousMap (z.1, z.2)
    have hL : L (0, z.1) = p₀₂ z.1 :=
      ContinuousMap.HomotopyWith.apply_zero L z.1
    exact (congrArg (fun y => e (q.inv (z.2, y))) hL).trans (hDirect z.2 z.1)
  · intro z
    change e (q.inv (z.2, L (1, z.1))) =
      ((SSet.realizeHomotopy X Y f g H₀₁).trans
        (SSet.realizeHomotopy X Y g h H₁₂)).toContinuousMap (z.1, z.2)
    have hL : L (1, z.1) = (p₀₁.trans p₁₂) z.1 :=
      ContinuousMap.HomotopyWith.apply_one L z.1
    have hPasted : e (q.inv (z.2, (p₀₁.trans p₁₂) z.1)) =
        ((SSet.realizeHomotopy X Y f g H₀₁).trans
          (SSet.realizeHomotopy X Y g h H₁₂)).toContinuousMap (z.1, z.2) := by
      change e (q.inv (z.2, (p₀₁.trans p₁₂) z.1)) =
        ((SSet.realizeHomotopy X Y f g H₀₁).trans
          (SSet.realizeHomotopy X Y g h H₁₂)) (z.1, z.2)
      rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
      split_ifs with ht
      · exact hFirst z.2 _
      · exact hSecond z.2 _
    exact (congrArg (fun y => e (q.inv (z.2, y))) hL).trans hPasted
  · intro s z hz
    rcases z with ⟨t, x⟩
    change t = 0 ∨ t = 1 at hz
    rcases hz with ht | ht
    · subst t
      change e (q.inv (x, L (s, 0))) =
        (SSet.realizeHomotopy X Y f h H₀₂).toContinuousMap (0, x)
      exact (congrArg (fun y => e (q.inv (x, y)))
        ((L.source s).trans p₀₂.source.symm)).trans (hDirect x 0)
    · subst t
      change e (q.inv (x, L (s, 1))) =
        (SSet.realizeHomotopy X Y f h H₀₂).toContinuousMap (1, x)
      exact (congrArg (fun y => e (q.inv (x, y)))
        ((L.target s).trans p₀₂.target.symm)).trans (hDirect x 1)

end SSet

end


@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial ContinuousMap unitInterval

universe u

namespace SSet

/-- The original vertex of the actual standard two-simplex. -/
def realizedPrismVertexSimplex (i : Fin 3) : (Δ[2] : SSet.{u}) _⦋0⦌ :=
  stdSimplex.obj₀Equiv.{u}.symm i

/-- Realize the same native vertex, without a chosen replacement point. -/
def realizedPrismVertex (i : Fin 3) : toTop.obj (Δ[2] : SSet.{u}) :=
  realizedVertex (realizedPrismVertexSimplex i)

/-- The original short edge from the first native vertex to the middle native vertex. -/
@[no_expose] def realizedPrismEdge01 :
    (Δ[2] : SSet.{u}).Edge (realizedPrismVertexSimplex 0) (realizedPrismVertexSimplex 1) :=
  univEdge₀₁.{u}

/-- The original short edge from the middle native vertex to the last native vertex. -/
@[no_expose] def realizedPrismEdge12 :
    (Δ[2] : SSet.{u}).Edge (realizedPrismVertexSimplex 1) (realizedPrismVertexSimplex 2) :=
  univEdge₁₂.{u}

/-- The original direct edge from the first native vertex to the last native vertex. -/
@[no_expose] def realizedPrismEdge02 :
    (Δ[2] : SSet.{u}).Edge (realizedPrismVertexSimplex 0) (realizedPrismVertexSimplex 2) :=
  univEdge₀₂.{u}

private theorem realizedPrismEdge01YonedaComputed :
    yonedaEquiv.symm realizedPrismEdge01.{u}.edge = stdSimplex.δ (2 : Fin 3) := by decide

/-- The original 01 edge is exactly the second boundary face of the actual two-simplex. -/
theorem realizedPrismEdge01_yoneda :
    yonedaEquiv.symm realizedPrismEdge01.{u}.edge = stdSimplex.δ (2 : Fin 3) :=
  realizedPrismEdge01YonedaComputed

private theorem realizedPrismEdge12YonedaComputed :
    yonedaEquiv.symm realizedPrismEdge12.{u}.edge = stdSimplex.δ (0 : Fin 3) := by decide

/-- The original 12 edge is exactly the zeroth boundary face of the actual two-simplex. -/
theorem realizedPrismEdge12_yoneda :
    yonedaEquiv.symm realizedPrismEdge12.{u}.edge = stdSimplex.δ (0 : Fin 3) :=
  realizedPrismEdge12YonedaComputed

private theorem realizedPrismEdge02YonedaComputed :
    yonedaEquiv.symm realizedPrismEdge02.{u}.edge = stdSimplex.δ (1 : Fin 3) := by decide

/-- The original 02 edge is exactly the first boundary face of the actual two-simplex. -/
theorem realizedPrismEdge02_yoneda :
    yonedaEquiv.symm realizedPrismEdge02.{u}.edge = stdSimplex.δ (1 : Fin 3) :=
  realizedPrismEdge02YonedaComputed

/-- The native 01 path in the actual realization of the original two-simplex. -/
def realizedPrismStandardPath01 :
    _root_.Path (realizedPrismVertex 0) (realizedPrismVertex 1) :=
  TopCat.pathEquiv (realizedEdgePath realizedPrismEdge01.{u})

/-- The native 12 path in the actual realization of the original two-simplex. -/
def realizedPrismStandardPath12 :
    _root_.Path (realizedPrismVertex 1) (realizedPrismVertex 2) :=
  TopCat.pathEquiv (realizedEdgePath realizedPrismEdge12.{u})

/-- The native 02 path in the actual realization of the original two-simplex. -/
def realizedPrismStandardPath02 :
    _root_.Path (realizedPrismVertex 0) (realizedPrismVertex 2) :=
  TopCat.pathEquiv (realizedEdgePath realizedPrismEdge02.{u})

/-- The actual universal filler already used by the canonical finite-prism composition.
This exposes its direct-to-concatenated path family without a second choice. -/
@[no_expose] public def realizedPrismCanonicalCompositionCell :
    realizedPrismStandardPath02.{u}.Homotopy
      (realizedPrismStandardPath01.{u}.trans realizedPrismStandardPath12.{u}) :=
  univRealizedHomotopic₂.{u}.some

/-- Reverse the same canonical filler to the full concatenation-to-direct two-cell. -/
@[no_expose] def realizedPrismUniversalCompositionCell :
    (realizedPrismStandardPath01.{u}.trans realizedPrismStandardPath12.{u}).Homotopy
      realizedPrismStandardPath02.{u} :=
  realizedPrismCanonicalCompositionCell.{u}.symm

/-- The tensor chart built from the product comparison already used by the canonical prism. -/
@[no_expose] def realizedPrismProductIso (X : SSet.{u}) (n : ℕ) :
    toTop.obj (X ⊗ (Δ[n] : SSet.{u})) ≅
      toTop.obj X ⨯ toTop.obj (Δ[n] : SSet.{u}) :=
  toTop.mapIso ((CartesianMonoidalCategory.tensorLeftIsoProd X).app (Δ[n] : SSet.{u})) ≪≫
    finitePrismProductIso X n

private theorem realizedPrismProductIsoHomComputed (X : SSet.{u}) (n : ℕ) :
    (realizedPrismProductIso X n).hom =
      toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[n] : SSet.{u})) ≫
        Limits.prodComparison toTop X (Δ[n] : SSet.{u}) := rfl

/-- The complete forward tensor chart is the existing original product comparison. -/
theorem realizedPrismProductIso_hom (X : SSet.{u}) (n : ℕ) :
    (realizedPrismProductIso X n).hom =
      toTop.map ((CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app (Δ[n] : SSet.{u})) ≫
        Limits.prodComparison toTop X (Δ[n] : SSet.{u}) :=
  realizedPrismProductIsoHomComputed X n

/-- The original canonical finite-prism evaluation, with its actual product chart. -/
@[no_expose] public def realizedPrismEvaluation
    {X Y : SSet.{u}} {n : ℕ} (Phi : X ⊗ (Δ[n] : SSet.{u}) ⟶ Y) :
    SSet.toTop.obj X ⨯ SSet.toTop.obj (Δ[n] : SSet.{u}) ⟶ SSet.toTop.obj Y :=
  finitePrismEvaluation Phi

private theorem realizedPrismEvaluationEqComputed {X Y : SSet.{u}} {n : ℕ}
    (Phi : X ⊗ (Δ[n] : SSet.{u}) ⟶ Y) :
    realizedPrismEvaluation Phi =
      (realizedPrismProductIso X n).inv ≫ toTop.map Phi := by
  unfold realizedPrismEvaluation realizedPrismProductIso finitePrismEvaluation
  dsimp [finitePrismProductBridge]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]

/-- The existing finite-prism evaluation uses this same tensor-chart inverse. -/
theorem realizedPrismEvaluation_eq {X Y : SSet.{u}} {n : ℕ}
    (Phi : X ⊗ (Δ[n] : SSet.{u}) ⟶ Y) :
    realizedPrismEvaluation Phi =
      (realizedPrismProductIso X n).inv ≫ toTop.map Phi :=
  realizedPrismEvaluationEqComputed Phi

/-- The original realized one-simplex homotopy uses the same canonical prism evaluation. -/
theorem realizedPrismEvaluation_realizeHomotopyMap
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    realizeHomotopyMap X Y f g H =
      (Limits.prod.braiding TopCat.I.{u} (toTop.obj X)).hom ≫
        Limits.prod.map (𝟙 (toTop.obj X)) stdSimplex.toTopObjIsoI.inv ≫
          realizedPrismEvaluation H.h :=
  finitePrismEvaluation_realizeHomotopyMap H

/-- The existing evaluation proof preserves each original homotopy point and interval value. -/
theorem realizedPrismEvaluation_realizeHomotopy_apply
    {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g)
    (x : toTop.obj X) (t : unitInterval) :
    realizedPrismEvaluation H.h
        ((TopCat.prodIsoProd (toTop.obj X) (toTop.obj (Δ[1] : SSet.{u}))).inv
          (x, stdSimplex.toTopObjIsoI.inv (TopCat.I.homeomorph.symm t))) =
      realizeHomotopy X Y f g H (t, x) :=
  finitePrismEvaluation_realizeHomotopy_apply H x t

/-- The whole canonical finite-prism family, before requiring its three cylinder-face witnesses.
Its filler, evaluation, product chart and both clocks are those of the existing relative homotopy.
-/
@[no_expose] def realizedPrismCanonicalCompositionMap {X Y : SSet.{u}}
    (Phi : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y) :
    C(unitInterval × (unitInterval × toTop.obj X), toTop.obj Y) where
  toFun z := realizedPrismEvaluation Phi
    ((TopCat.prodIsoProd (toTop.obj X) (toTop.obj (Δ[2] : SSet.{u}))).inv
      (z.2.2, realizedPrismCanonicalCompositionCell (z.1, z.2.1)))
  continuous_toFun := (realizedPrismEvaluation Phi).hom.continuous.comp
    ((TopCat.prodIsoProd (toTop.obj X) (toTop.obj (Δ[2] : SSet.{u}))).inv.hom.continuous.comp
      ((continuous_snd.comp continuous_snd).prodMk
        (realizedPrismCanonicalCompositionCell.continuous.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))))

private theorem realizedPrismCanonicalCompositionMapApplyComputed
    {X Y : SSet.{u}} (Phi : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (s t : unitInterval) (x : toTop.obj X) :
    realizedPrismCanonicalCompositionMap Phi (s, (t, x)) =
      realizedPrismEvaluation Phi
        ((TopCat.prodIsoProd (toTop.obj X) (toTop.obj (Δ[2] : SSet.{u}))).inv
          (x, realizedPrismCanonicalCompositionCell (s, t))) := rfl

/-- The complete canonical family retains its original evaluation, point and two clocks. -/
theorem realizedPrismCanonicalCompositionMap_apply
    {X Y : SSet.{u}} (Phi : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (s t : unitInterval) (x : toTop.obj X) :
    realizedPrismCanonicalCompositionMap Phi (s, (t, x)) =
      realizedPrismEvaluation Phi
        ((TopCat.prodIsoProd (toTop.obj X) (toTop.obj (Δ[2] : SSet.{u}))).inv
          (x, realizedPrismCanonicalCompositionCell (s, t))) :=
  realizedPrismCanonicalCompositionMapApplyComputed Phi s t x

private theorem realizedPrismUniversalCompositionCellApplyComputed (s t : unitInterval) :
    realizedPrismUniversalCompositionCell.{u} (s, t) =
      realizedPrismCanonicalCompositionCell.{u} (unitInterval.symm s, t) := rfl

/-- Reversal changes only the homotopy clock of the same original canonical filler. -/
theorem realizedPrismUniversalCompositionCell_apply (s t : unitInterval) :
    realizedPrismUniversalCompositionCell.{u} (s, t) =
      realizedPrismCanonicalCompositionCell.{u} (unitInterval.symm s, t) :=
  realizedPrismUniversalCompositionCellApplyComputed s t

private theorem realizedPrismCompositionHomotopyMapComputed
    {X Y : SSet.{u}} {f g h : X ⟶ Y}
    (Phi : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (H01 : SSet.Homotopy f g) (H12 : SSet.Homotopy g h) (H02 : SSet.Homotopy f h)
    (h01 : (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ Phi = H01.h)
    (h12 : (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ Phi = H12.h)
    (h02 : (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ Phi = H02.h) :
    (realizedPrismCompositionHomotopy Phi H01 H12 H02 h01 h12 h02).toContinuousMap =
      realizedPrismCanonicalCompositionMap Phi := rfl

/-- The entire existing relative homotopy is this canonical family for any legitimate faces. -/
theorem realizedPrismCompositionHomotopy_toContinuousMap
    {X Y : SSet.{u}} {f g h : X ⟶ Y}
    (Phi : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (H01 : SSet.Homotopy f g) (H12 : SSet.Homotopy g h) (H02 : SSet.Homotopy f h)
    (h01 : (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ Phi = H01.h)
    (h12 : (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ Phi = H12.h)
    (h02 : (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ Phi = H02.h) :
    (realizedPrismCompositionHomotopy Phi H01 H12 H02 h01 h12 h02).toContinuousMap =
      realizedPrismCanonicalCompositionMap Phi :=
  realizedPrismCompositionHomotopyMapComputed Phi H01 H12 H02 h01 h12 h02

private theorem realizedPrismCompositionHomotopyApplyComputed
    {X Y : SSet.{u}} {f g h : X ⟶ Y}
    (Phi : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (H01 : SSet.Homotopy f g) (H12 : SSet.Homotopy g h) (H02 : SSet.Homotopy f h)
    (h01 : (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ Phi = H01.h)
    (h12 : (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ Phi = H12.h)
    (h02 : (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ Phi = H02.h)
    (s t : unitInterval) (x : SSet.toTop.obj X) :
    realizedPrismCompositionHomotopy Phi H01 H12 H02 h01 h12 h02 (s, (t, x)) =
      realizedPrismEvaluation Phi
        ((TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[2] : SSet.{u}))).inv
            (x, realizedPrismCanonicalCompositionCell (s, t))) :=
  by rfl

/-- Every point and both family clocks retain the canonical finite-prism program. -/
public theorem realizedPrismCompositionHomotopy_apply
    {X Y : SSet.{u}} {f g h : X ⟶ Y}
    (Phi : X ⊗ (Δ[2] : SSet.{u}) ⟶ Y)
    (H01 : SSet.Homotopy f g) (H12 : SSet.Homotopy g h) (H02 : SSet.Homotopy f h)
    (h01 : (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ Phi = H01.h)
    (h12 : (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ Phi = H12.h)
    (h02 : (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ Phi = H02.h)
    (s t : unitInterval) (x : SSet.toTop.obj X) :
    realizedPrismCompositionHomotopy Phi H01 H12 H02 h01 h12 h02 (s, (t, x)) =
      realizedPrismEvaluation Phi
        ((TopCat.prodIsoProd (SSet.toTop.obj X)
          (SSet.toTop.obj (Δ[2] : SSet.{u}))).inv
            (x, realizedPrismCanonicalCompositionCell (s, t))) :=
  realizedPrismCompositionHomotopyApplyComputed Phi H01 H12 H02 h01 h12 h02 s t x


end SSet

end

end
