/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoid
public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy
import
  MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# The fundamental groupoid of a singular simplicial set

For a topological space `Y`, the combinatorial fundamental groupoid of its
singular simplicial set is equivalent to the ordinary fundamental groupoid of
`Y`.  A path homotopy relative to its endpoints supplies the two singular
triangles needed for faithfulness.

The construction is universe polymorphic.  It makes no claim about the
realization unit, weak equivalences, simplicial approximation, Waldhausen
additivity, or K-theory.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u

namespace TopCat

@[simp]
private theorem toSSetObjEquiv_map_apply
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (s : (TopCat.toSSet.obj X).obj n)
    (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n s) z =
      f (X.toSSetObjEquiv n s z) :=
  rfl

@[simp]
private theorem toSSetObjEquiv_mu_apply
    (X Y : TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (s : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y).obj n)
    (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (X ⊗ Y).toSSetObjEquiv n
        ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n s) z =
      (X.toSSetObjEquiv n s.1 z, Y.toSSetObjEquiv n s.2 z) := by
  apply Prod.ext
  · have h := congrArg (fun k => k.app n s)
      (Functor.Monoidal.μ_fst (F := TopCat.toSSet) X Y)
    exact congrArg (fun t => X.toSSetObjEquiv n t z) h
  · have h := congrArg (fun k => k.app n s)
      (Functor.Monoidal.μ_snd (F := TopCat.toSSet) X Y)
    exact congrArg (fun t => Y.toSSetObjEquiv n t z) h

@[simp]
private theorem toSSetObjEquiv_yonedaEquiv_toSSetObjI :
    TopCat.I.toSSetObjEquiv (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI) =
      (TopCat.stdSimplexHomeomorphI.{u} : C(_, _)) := by
  ext z
  rw [SSet.stdSimplex.toSSetObjI, Adjunction.homEquiv_unit,
    SSet.yonedaEquiv_comp]
  rw [TopCat.toSSetObjEquiv_map_apply]
  let a : (Δ[1] : SSet.{u}) _⦋1⦌ := SSet.yonedaEquiv (𝟙 _)
  have hy : SSet.yonedaEquiv
      (sSetTopAdj.unit.app (Δ[1] : SSet.{u})) =
      (sSetTopAdj.unit.app (Δ[1] : SSet.{u})).app _ a := by
    dsimp [a]
    rw [← SSet.yonedaEquiv_comp]
    simp
  have hunit := sSetTopAdj_unit_app_app_down
    (Δ[1] : SSet.{u}) (Opposite.op ⦋1⦌) a
  have hunit' :
      (SSet.yonedaEquiv
        (sSetTopAdj.unit.app (Δ[1] : SSet.{u}))).down =
        SSet.toTopSimplex.inv.app _ ≫
          SSet.toTop.map (SSet.yonedaEquiv.symm a) := by
    rw [hy]
    exact hunit
  have hunit'' :
      (SSet.yonedaEquiv
        (sSetTopAdj.unit.app (Δ[1] : SSet.{u}))).down =
        SSet.toTopSimplex.inv.app ⦋1⦌ := by
    simpa [a] using hunit'
  have hsimplex :
      SSet.yonedaEquiv (sSetTopAdj.unit.app (Δ[1] : SSet.{u})) =
        ULift.up (SSet.toTopSimplex.inv.app ⦋1⦌) := by
    apply ULift.ext
    exact hunit''
  have hvalue := congrArg
    (fun s => ((SSet.toTop.obj (Δ[1] : SSet.{u})).toSSetObjEquiv
      (Opposite.op ⦋1⦌) s) z) hsimplex
  have hvalue' := congrArg
    (fun w => TopCat.I.homeomorph
      (SSet.stdSimplex.toTopObjIsoI.{u}.hom w)) hvalue
  have hvalue'' := congrArg Subtype.val hvalue'
  exact hvalue''.trans (by
    have hcancel := ConcreteCategory.congr_hom
      (Iso.inv_hom_id (SSet.toTopSimplex.app ⦋1⦌))
      (ULift.up.{u} z)
    have hfinal := congrArg
      (fun w => ((TopCat.I.homeomorph
        (TopCat.stdSimplexHomeomorphI.{u} (Homeomorph.ulift w))) : ℝ))
      hcancel
    with_unfolding_all
      exact hfinal)

/-- The canonical singular interval followed by a map `p : I ⟶ Y` is the
Yoneda representative of the singular edge corresponding to `p`. -/
theorem toSSetObjI_comp_map_eq_yonedaEdge
    {Y : TopCat.{u}} (p : TopCat.I.{u} ⟶ Y) :
    SSet.stdSimplex.toSSetObjI ≫ TopCat.toSSet.map p =
      SSet.yonedaEquiv.symm (TopCat.toSSetObj₁Equiv.symm p) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  apply TopCat.toSSetObj₁Equiv.injective
  apply TopCat.hom_ext
  ext t
  simp only [Equiv.apply_symm_apply]
  simp only [TopCat.toSSetObj₁Equiv, Equiv.trans_apply, Equiv.coe_fn_mk]
  change p
      ((TopCat.I.toSSetObjEquiv (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI))
          (TopCat.stdSimplexHomeomorphI.{u}.symm t)) = p t
  rw [toSSetObjEquiv_yonedaEquiv_toSSetObjI]
  simp

/-- The canonical singular interval represents the identity interval map. -/
@[simp]
theorem yonedaEquiv_toSSetObjI :
    SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI =
      TopCat.toSSetObj₁Equiv.symm (𝟙 TopCat.I.{u}) := by
  apply SSet.yonedaEquiv.symm.injective
  simpa using TopCat.toSSetObjI_comp_map_eq_yonedaEdge
    (𝟙 TopCat.I.{u})

/-- The path represented by an arbitrary singular edge.  Its endpoints are
first transported to the canonical singular vertices corresponding to the
points represented by the original endpoints. -/
noncomputable def singularEdgePath
    {Y : TopCat.{u}}
    {x y : (TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (TopCat.toSSet.obj Y).Edge x y) :
    Y.Path (TopCat.toSSetObj₀Equiv x) (TopCat.toSSetObj₀Equiv y) :=
  TopCat.toSSetObjEdgeEquiv
    (SSet.Edge.ofEq e
      ((TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply x).symm
      ((TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply y).symm)

/-- Canonicalizing a singular edge and converting the resulting path back to
an edge recovers the explicit endpoint transport. -/
@[simp]
theorem toSSetObjEdgeEquiv_symm_singularEdgePath
    {Y : TopCat.{u}}
    {x y : (TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (TopCat.toSSet.obj Y).Edge x y) :
    TopCat.toSSetObjEdgeEquiv.symm (singularEdgePath e) =
      SSet.Edge.ofEq e
        ((TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply x).symm
        ((TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply y).symm :=
  (TopCat.toSSetObjEdgeEquiv (X := Y)).symm_apply_apply _

@[simp]
theorem toSSetObjEdgeEquiv_symm_singularEdgePath_edge
    {Y : TopCat.{u}}
    {x y : (TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (TopCat.toSSet.obj Y).Edge x y) :
    (TopCat.toSSetObjEdgeEquiv.symm (singularEdgePath e)).edge = e.edge := by
  exact congrArg SSet.Edge.edge
    (TopCat.toSSetObjEdgeEquiv_symm_singularEdgePath e)

/-- On canonically represented singular vertices, `singularEdgePath` is the
existing singular-edge/path equivalence without additional transport. -/
@[simp]
theorem singularEdgePath_of_canonical
    {Y : TopCat.{u}} {x y : Y}
    (e : (TopCat.toSSet.obj Y).Edge
      (TopCat.toSSetObj₀Equiv.symm x)
      (TopCat.toSSetObj₀Equiv.symm y)) :
    singularEdgePath e = TopCat.toSSetObjEdgeEquiv e := by
  apply TopCat.Path.ext
  rfl

/-- Endpoint transport after a canonically represented edge does not change
the represented path. -/
@[simp]
theorem singularEdgePath_ofEq
    {Y : TopCat.{u}} {x y : Y}
    {x' y' : (TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (TopCat.toSSet.obj Y).Edge
      (TopCat.toSSetObj₀Equiv.symm x)
      (TopCat.toSSetObj₀Equiv.symm y))
    (hx : TopCat.toSSetObj₀Equiv.symm x = x')
    (hy : TopCat.toSSetObj₀Equiv.symm y = y') :
    singularEdgePath (SSet.Edge.ofEq e hx hy) =
      (TopCat.toSSetObjEdgeEquiv e).cast
        (congrArg TopCat.toSSetObj₀Equiv hx).symm
        (congrArg TopCat.toSSetObj₀Equiv hy).symm := by
  apply TopCat.Path.ext
  rfl

namespace Path

/-- Convert an endpoint-fixed homotopy of ordinary paths into a `TopCat`
homotopy of their interval maps.  The first coordinate remains homotopy time;
the second is converted from the lifted categorical interval. -/
noncomputable def homotopyOfPathHomotopy
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q)) :
    TopCat.Homotopy p.hom q.hom where
  toFun z := H (z.1, TopCat.I.homeomorph z.2)
  continuous_toFun :=
    H.continuous_toFun.comp
      (continuous_fst.prodMk
        (TopCat.I.homeomorph.continuous.comp continuous_snd))
  map_zero_left z := by
    simpa [TopCat.pathEquiv] using H.apply_zero
      (TopCat.I.homeomorph z)
  map_one_left z := by
    simpa [TopCat.pathEquiv] using H.apply_one
      (TopCat.I.homeomorph z)

@[simp]
theorem homotopyOfPathHomotopy_apply
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q))
    (t : unitInterval) (s : TopCat.I.{u}) :
    homotopyOfPathHomotopy H (t, s) =
      H (t, TopCat.I.homeomorph s) :=
  rfl

@[simp]
theorem homotopyOfPathHomotopy_source
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q))
    (t : unitInterval) :
    homotopyOfPathHomotopy H (t, (0 : TopCat.I.{u})) = x := by
  change H (t, TopCat.I.homeomorph (0 : TopCat.I.{u})) = x
  rw [TopCat.I.homeomorph_zero]
  exact H.source t

@[simp]
theorem homotopyOfPathHomotopy_target
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q))
    (t : unitInterval) :
    homotopyOfPathHomotopy H (t, (1 : TopCat.I.{u})) = y := by
  change H (t, TopCat.I.homeomorph (1 : TopCat.I.{u})) = y
  rw [TopCat.I.homeomorph_one]
  exact H.target t

end Path

end TopCat

namespace Path.Homotopy

/-- An endpoint-fixed path homotopy gives a singular homotopy between the
Yoneda maps representing the two paths.  Its product order is path coordinate
first and homotopy time second, as required by `SSet.Homotopy`. -/
noncomputable def toSingularHomotopy
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q)) :
    SSet.Homotopy
      (SSet.yonedaEquiv.symm
        (TopCat.toSSetObjEdgeEquiv.symm p).edge)
      (SSet.yonedaEquiv.symm
        (TopCat.toSSetObjEdgeEquiv.symm q).edge) where
  h := SSet.stdSimplex.toSSetObjI ▷ (Δ[1] : SSet.{u}) ≫
    (TopCat.Path.homotopyOfPathHomotopy H).toSSet.h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc,
      SSet.Homotopy.h₀]
    exact TopCat.toSSetObjI_comp_map_eq_yonedaEdge p.hom
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc,
      SSet.Homotopy.h₁]
    exact TopCat.toSSetObjI_comp_map_eq_yonedaEdge q.hom
  rel := by
    ext n ⟨⟨z, hz⟩, t⟩
    cases hz

@[no_expose]
noncomputable def intervalVertexZero :
    (Δ[1] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)

@[no_expose]
noncomputable def intervalVertexOne :
    (Δ[1] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)

@[no_expose]
noncomputable def intervalEdge :
    (Δ[1] : SSet.{u}).Edge
      intervalVertexZero.{u} intervalVertexOne.{u} :=
  SSet.Edge.mk
    (SSet.stdSimplex.edge 1 (0 : Fin 2) (1 : Fin 2) (by decide))
    (by decide) (by decide)

theorem yonedaEdge_app_intervalVertexZero
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.yonedaEquiv.symm e.edge).app _ intervalVertexZero.{u} = x := by
  have hv : intervalVertexZero.{u} =
      SSet.yonedaEquiv (SSet.stdSimplex.δ 1) := by
    rw [SSet.stdSimplex.δ_one_eq_const, SSet.yonedaEquiv_const]
    rfl
  rw [hv, ← SSet.yonedaEquiv_comp,
    SSet.Edge.δ_one_yonedaEquiv_symm, Equiv.apply_symm_apply]

theorem yonedaEdge_app_intervalVertexOne
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.yonedaEquiv.symm e.edge).app _ intervalVertexOne.{u} = y := by
  have hv : intervalVertexOne.{u} =
      SSet.yonedaEquiv (SSet.stdSimplex.δ 0) := by
    rw [SSet.stdSimplex.δ_zero_eq_const, SSet.yonedaEquiv_const]
    rfl
  rw [hv, ← SSet.yonedaEquiv_comp,
    SSet.Edge.δ_zero_yonedaEquiv_symm, Equiv.apply_symm_apply]

@[no_expose]
noncomputable def intervalEdgeMap
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) : X.Edge x y :=
  SSet.Edge.ofEq
    (intervalEdge.{u}.map (SSet.yonedaEquiv.symm e.edge))
    (yonedaEdge_app_intervalVertexZero e)
    (yonedaEdge_app_intervalVertexOne e)

@[simp]
theorem intervalEdgeMap_eq
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    intervalEdgeMap e = e := by
  apply SSet.Edge.ext
  change (SSet.yonedaEquiv.symm e.edge).app _
    (SSet.stdSimplex.edge 1 (0 : Fin 2) (1 : Fin 2) (by decide)) = e.edge
  rw [show SSet.stdSimplex.edge 1 (0 : Fin 2) (1 : Fin 2) (by decide) =
    SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) by decide]
  exact SSet.yonedaEquiv_symm_app_id e.edge

/-- The source vertical edge of an endpoint-fixed singular square, transported
to the canonical singular vertex. -/
noncomputable def toSingularHomotopySourceEdge
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q)) :
    (TopCat.toSSet.obj Y).Edge
      (TopCat.toSSetObj₀Equiv.symm x)
      (TopCat.toSSetObj₀Equiv.symm x) :=
  SSet.Edge.ofEq
    (SSet.Edge.ofSimplicialObjectHomotopy
      (toSingularHomotopy H).toSimplicialObjectHomotopy
      intervalVertexZero.{u})
    (yonedaEdge_app_intervalVertexZero
      (TopCat.toSSetObjEdgeEquiv.symm p))
    (yonedaEdge_app_intervalVertexZero
      (TopCat.toSSetObjEdgeEquiv.symm q))

/-- The source vertical edge of the singular square is constant. -/
@[simp]
theorem toSingularHomotopy_sourceEdge
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q)) :
    toSingularHomotopySourceEdge H =
      SSet.Edge.id (TopCat.toSSetObj₀Equiv.symm x) := by
  apply SSet.Edge.ext
  change (SSet.Edge.ofSimplicialObjectHomotopy
    (toSingularHomotopy H).toSimplicialObjectHomotopy
    intervalVertexZero.{u}).edge = _
  rw [SSet.Edge.ofSimplicialObjectHomotopy_edge, SSet.Edge.id_edge]
  apply TopCat.toSSetObj₁Equiv.injective
  ext t
  let s := (SSet.prodStdSimplex₁.nonDegenerateEquiv
    (0 : Fin 1)).1
  let pre := (((SSet.yonedaEquiv.symm intervalVertexZero.{u} ▷
      (Δ[1] : SSet.{u})) ≫
      (SSet.stdSimplex.toSSetObjI ▷ (Δ[1] : SSet.{u})) ≫
      (TopCat.toSSet.obj TopCat.I ◁
        SSet.stdSimplex.toSSetObjI)).app _ s)
  change Y.toSSetObjEquiv _
      ((TopCat.toSSet.map
        (TopCat.Path.homotopyOfPathHomotopy H).h).app _
          ((Functor.LaxMonoidal.μ TopCat.toSSet TopCat.I TopCat.I).app _ pre))
        (TopCat.stdSimplexHomeomorphI.symm t) = _
  rw [TopCat.toSSetObjEquiv_map_apply,
    TopCat.toSSetObjEquiv_mu_apply]
  have hpre₀' : pre.1 = (TopCat.toSSet.obj TopCat.I).σ 0
      (TopCat.toSSetObj₀Equiv.symm 0) := by
    change SSet.stdSimplex.toSSetObjI.app _
      ((SSet.yonedaEquiv.symm intervalVertexZero.{u}).app _ s.1) = _
    have hs₀ : s.1 = SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.σ (0 : Fin 1)) := by
      simp [s]
    rw [hs₀, SSet.yonedaEquiv_symm_app_objEquiv_symm]
    change SSet.stdSimplex.toSSetObjI.app _
      ((Δ[1] : SSet.{u}).σ 0 intervalVertexZero.{u}) = _
    rw [SSet.σ_naturality_apply]
    simp [intervalVertexZero]
  have hpre₁' : pre.2 =
      SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI := by
    change SSet.stdSimplex.toSSetObjI.app _ s.2 = _
    have hs₁ : s.2 = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
      calc
        s.2 = SSet.stdSimplex.objMk₁ (0 : Fin 1).succ.castSucc := by
          simp [s]
        _ = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
          apply SSet.stdSimplex.objEquiv.injective
          decide
    rw [hs₁,
      ← SSet.yonedaEquiv_comp]
    simp
  have hpre₀ : TopCat.I.toSSetObjEquiv (Opposite.op ⦋1⦌) pre.1
      (TopCat.stdSimplexHomeomorphI.symm t) = 0 := by
    rw [hpre₀']
    simp [TopCat.toSSetObj₀Equiv]
  have hpre₁ : TopCat.I.toSSetObjEquiv (Opposite.op ⦋1⦌) pre.2
      (TopCat.stdSimplexHomeomorphI.symm t) = t := by
    rw [hpre₁', TopCat.toSSetObjEquiv_yonedaEquiv_toSSetObjI]
    simp
  rw [hpre₀, hpre₁]
  change H (TopCat.I.homeomorph t,
      TopCat.I.homeomorph (0 : TopCat.I.{u})) =
    Y.toSSetObjEquiv (Opposite.op ⦋0⦌)
      (TopCat.toSSetObj₀Equiv.symm x)
      (Convexity.StdSimplex.map (Fin.predAbove 0)
        (TopCat.stdSimplexHomeomorphI.symm t))
  rw [TopCat.I.homeomorph_zero, H.source]
  rw [Subsingleton.elim
    (Convexity.StdSimplex.map (Fin.predAbove 0)
      (TopCat.stdSimplexHomeomorphI.symm t)) default]
  change x = TopCat.toSSetObj₀Equiv
    (TopCat.toSSetObj₀Equiv.symm x)
  exact ((TopCat.toSSetObj₀Equiv (X := Y)).apply_symm_apply x).symm

/-- The target vertical edge of an endpoint-fixed singular square, transported
to the canonical singular vertex. -/
noncomputable def toSingularHomotopyTargetEdge
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q)) :
    (TopCat.toSSet.obj Y).Edge
      (TopCat.toSSetObj₀Equiv.symm y)
      (TopCat.toSSetObj₀Equiv.symm y) :=
  SSet.Edge.ofEq
    (SSet.Edge.ofSimplicialObjectHomotopy
      (toSingularHomotopy H).toSimplicialObjectHomotopy
      intervalVertexOne.{u})
    (yonedaEdge_app_intervalVertexOne
      (TopCat.toSSetObjEdgeEquiv.symm p))
    (yonedaEdge_app_intervalVertexOne
      (TopCat.toSSetObjEdgeEquiv.symm q))

/-- The target vertical edge of the singular square is constant. -/
@[simp]
theorem toSingularHomotopy_targetEdge
    {Y : TopCat.{u}} {x y : Y} {p q : Y.Path x y}
    (H : (TopCat.pathEquiv p).Homotopy (TopCat.pathEquiv q)) :
    toSingularHomotopyTargetEdge H =
      SSet.Edge.id (TopCat.toSSetObj₀Equiv.symm y) := by
  apply SSet.Edge.ext
  change (SSet.Edge.ofSimplicialObjectHomotopy
    (toSingularHomotopy H).toSimplicialObjectHomotopy
    intervalVertexOne.{u}).edge = _
  rw [SSet.Edge.ofSimplicialObjectHomotopy_edge, SSet.Edge.id_edge]
  apply TopCat.toSSetObj₁Equiv.injective
  ext t
  let s := (SSet.prodStdSimplex₁.nonDegenerateEquiv
    (0 : Fin 1)).1
  let pre := (((SSet.yonedaEquiv.symm intervalVertexOne.{u} ▷
      (Δ[1] : SSet.{u})) ≫
      (SSet.stdSimplex.toSSetObjI ▷ (Δ[1] : SSet.{u})) ≫
      (TopCat.toSSet.obj TopCat.I ◁
        SSet.stdSimplex.toSSetObjI)).app _ s)
  change Y.toSSetObjEquiv _
      ((TopCat.toSSet.map
        (TopCat.Path.homotopyOfPathHomotopy H).h).app _
          ((Functor.LaxMonoidal.μ TopCat.toSSet TopCat.I TopCat.I).app _ pre))
        (TopCat.stdSimplexHomeomorphI.symm t) = _
  rw [TopCat.toSSetObjEquiv_map_apply,
    TopCat.toSSetObjEquiv_mu_apply]
  have hpre₀' : pre.1 = (TopCat.toSSet.obj TopCat.I).σ 0
      (TopCat.toSSetObj₀Equiv.symm 1) := by
    change SSet.stdSimplex.toSSetObjI.app _
      ((SSet.yonedaEquiv.symm intervalVertexOne.{u}).app _ s.1) = _
    have hs₀ : s.1 = SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.σ (0 : Fin 1)) := by
      simp [s]
    rw [hs₀, SSet.yonedaEquiv_symm_app_objEquiv_symm]
    change SSet.stdSimplex.toSSetObjI.app _
      ((Δ[1] : SSet.{u}).σ 0 intervalVertexOne.{u}) = _
    rw [SSet.σ_naturality_apply]
    simp [intervalVertexOne]
  have hpre₁' : pre.2 =
      SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI := by
    change SSet.stdSimplex.toSSetObjI.app _ s.2 = _
    have hs₁ : s.2 = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
      calc
        s.2 = SSet.stdSimplex.objMk₁ (0 : Fin 1).succ.castSucc := by
          simp [s]
        _ = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
          apply SSet.stdSimplex.objEquiv.injective
          decide
    rw [hs₁, ← SSet.yonedaEquiv_comp]
    simp
  have hpre₀ : TopCat.I.toSSetObjEquiv (Opposite.op ⦋1⦌) pre.1
      (TopCat.stdSimplexHomeomorphI.symm t) = 1 := by
    rw [hpre₀']
    simp [TopCat.toSSetObj₀Equiv]
  have hpre₁ : TopCat.I.toSSetObjEquiv (Opposite.op ⦋1⦌) pre.2
      (TopCat.stdSimplexHomeomorphI.symm t) = t := by
    rw [hpre₁', TopCat.toSSetObjEquiv_yonedaEquiv_toSSetObjI]
    simp
  rw [hpre₀, hpre₁]
  change H (TopCat.I.homeomorph t,
      TopCat.I.homeomorph (1 : TopCat.I.{u})) =
    Y.toSSetObjEquiv (Opposite.op ⦋0⦌)
      (TopCat.toSSetObj₀Equiv.symm y)
      (Convexity.StdSimplex.map (Fin.predAbove 0)
        (TopCat.stdSimplexHomeomorphI.symm t))
  rw [TopCat.I.homeomorph_one, H.target]
  rw [Subsingleton.elim
    (Convexity.StdSimplex.map (Fin.predAbove 0)
      (TopCat.stdSimplexHomeomorphI.symm t)) default]
  change y = TopCat.toSSetObj₀Equiv
    (TopCat.toSSetObj₀Equiv.symm y)
  exact ((TopCat.toSSetObj₀Equiv (X := Y)).apply_symm_apply y).symm

end Path.Homotopy

namespace TopCat

/-- The realization of a singular edge, followed by the adjunction counit,
has the interval map represented by that singular edge. -/
private theorem realizedEdgePath_counit_hom
    {Y : TopCat.{u}}
    {x y : (TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (TopCat.toSSet.obj Y).Edge x y) :
    (SSet.realizedEdgePath e).hom ≫ sSetTopAdj.counit.app Y =
      (TopCat.singularEdgePath e).hom := by
  rw [SSet.realizedEdgePath_hom, Category.assoc]
  apply (cancel_epi SSet.stdSimplex.toTopObjIsoI.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← TopCat.toSSetObjEdgeEquiv_symm_singularEdgePath_edge e]
  change SSet.toTop.map (SSet.yonedaEquiv.symm
      (TopCat.toSSetObj₁Equiv.symm (TopCat.singularEdgePath e).hom)) ≫
      sSetTopAdj.counit.app Y = _
  rw [← TopCat.toSSetObjI_comp_map_eq_yonedaEdge
      (TopCat.singularEdgePath e).hom,
    Functor.map_comp, Category.assoc]
  have hnat := sSetTopAdj.counit.naturality
    (TopCat.singularEdgePath e).hom
  change SSet.toTop.map
      (TopCat.toSSet.map (TopCat.singularEdgePath e).hom) ≫
        sSetTopAdj.counit.app Y =
    sSetTopAdj.counit.app TopCat.I ≫
      (TopCat.singularEdgePath e).hom at hnat
  rw [hnat]
  have hI := (sSetTopAdj.homEquiv (Δ[1] : SSet.{u}) TopCat.I).symm_apply_apply
    SSet.stdSimplex.toTopObjIsoI.hom
  rw [← Category.assoc]
  simpa only [SSet.stdSimplex.toSSetObjI,
    Adjunction.homEquiv_counit] using
      congrArg (fun k => k ≫ (TopCat.singularEdgePath e).hom) hI

/-- The adjunction counit sends a realized singular vertex back to the point
represented by that singular vertex. -/
theorem counit_realizedVertex
    {Y : TopCat.{u}} (x : (TopCat.toSSet.obj Y) _⦋0⦌) :
    sSetTopAdj.counit.app Y (SSet.realizedVertex x) =
      TopCat.toSSetObj₀Equiv x := by
  have h := ConcreteCategory.congr_hom
    (realizedEdgePath_counit_hom (SSet.Edge.id x)) (0 : TopCat.I.{u})
  simpa using h

/-- The canonical comparison from the combinatorial fundamental groupoid of
the singular simplicial set to the topological fundamental groupoid. -/
noncomputable def singularFundamentalGroupoidFunctor (Y : TopCat.{u}) :
    SSet.FundamentalGroupoid (TopCat.toSSet.obj Y) ⥤
      _root_.FundamentalGroupoid Y :=
  SSet.realizationFundamentalGroupoidFunctor (TopCat.toSSet.obj Y) ⋙
    _root_.FundamentalGroupoid.map (sSetTopAdj.counit.app Y).hom

/-- The singular comparison sends a vertex to its represented point. -/
@[simp]
theorem singularFundamentalGroupoidFunctor_obj_mk
    (Y : TopCat.{u}) (x : (TopCat.toSSet.obj Y) _⦋0⦌) :
    (singularFundamentalGroupoidFunctor Y).obj
        (SSet.FundamentalGroupoid.mk x) =
      _root_.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv x) := by
  apply _root_.FundamentalGroupoid.ext
  exact counit_realizedVertex x

/-- The singular comparison sends a singular edge to the homotopy class of
the path represented by that edge. -/
@[simp]
theorem singularFundamentalGroupoidFunctor_map_homMk
    (Y : TopCat.{u})
    {x y : (TopCat.toSSet.obj Y) _⦋0⦌}
    (e : (TopCat.toSSet.obj Y).Edge x y) :
    (singularFundamentalGroupoidFunctor Y).map
        (SSet.FundamentalGroupoid.homMk e) =
      Path.Homotopic.Quotient.mk
        ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
          (counit_realizedVertex x) (counit_realizedVertex y)) := by
  change (_root_.FundamentalGroupoid.map
    (sSetTopAdj.counit.app Y).hom).map
      ((SSet.realizationFundamentalGroupoidFunctor
        (TopCat.toSSet.obj Y)).map
          (SSet.FundamentalGroupoid.homMk e)) = _
  rw [SSet.realizationFundamentalGroupoidFunctor_map_homMk]
  apply congrArg Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  funext t
  exact ConcreteCategory.congr_hom (realizedEdgePath_counit_hom e)
    (TopCat.I.homeomorph.symm t)

/-- The singular comparison is essentially surjective. -/
theorem singularFundamentalGroupoidFunctor_essSurj (Y : TopCat.{u}) :
    (singularFundamentalGroupoidFunctor Y).EssSurj := by
  constructor
  rintro ⟨y⟩
  refine ⟨SSet.FundamentalGroupoid.mk
    (TopCat.toSSetObj₀Equiv.symm y), ⟨?_⟩⟩
  simpa using Iso.refl (_root_.FundamentalGroupoid.mk y)

/-- The singular comparison is fully faithful.  Faithfulness is the two
shuffle-triangle decomposition of an endpoint-fixed path homotopy square. -/
@[no_expose]
noncomputable def singularFundamentalGroupoidFunctor_fullyFaithful
    (Y : TopCat.{u}) :
    (singularFundamentalGroupoidFunctor Y).FullyFaithful := by
  let F := singularFundamentalGroupoidFunctor Y
  letI : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex Y
  letI : F.Full := by
    constructor
    intro a b f
    induction a using SSet.FundamentalGroupoid.rec with
    | mk x =>
      induction b using SSet.FundamentalGroupoid.rec with
      | mk y =>
        change Path.Homotopic.Quotient
          (sSetTopAdj.counit.app Y (SSet.realizedVertex x))
          (sSetTopAdj.counit.app Y (SSet.realizedVertex y)) at f
        obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
        let p' : Path (TopCat.toSSetObj₀Equiv x)
            (TopCat.toSSetObj₀Equiv y) :=
          p.cast (counit_realizedVertex x).symm
            (counit_realizedVertex y).symm
        let e₀ := TopCat.toSSetObjEdgeEquiv.symm
          (TopCat.pathEquiv.symm p')
        let e : (TopCat.toSSet.obj Y).Edge x y :=
          SSet.Edge.ofEq e₀
            ((TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply x)
            ((TopCat.toSSetObj₀Equiv (X := Y)).symm_apply_apply y)
        refine ⟨SSet.FundamentalGroupoid.homMk e, ?_⟩
        rw [singularFundamentalGroupoidFunctor_map_homMk]
        apply Path.Homotopic.Quotient.eq.mpr
        have hp :
            ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
              (counit_realizedVertex x) (counit_realizedVertex y)) = p := by
          apply _root_.Path.ext
          change ⇑(TopCat.pathEquiv (TopCat.toSSetObjEdgeEquiv e₀)) = ⇑p
          have he₀ : TopCat.toSSetObjEdgeEquiv e₀ =
              TopCat.pathEquiv.symm p' :=
            (TopCat.toSSetObjEdgeEquiv (X := Y)).apply_symm_apply _
          rw [he₀, Equiv.apply_symm_apply]
          exact Path.cast_coe p _ _
        rw [hp]
  letI : F.Faithful := by
    constructor
    intro a b f g hfg
    induction a using SSet.FundamentalGroupoid.rec with
    | mk x =>
      induction b using SSet.FundamentalGroupoid.rec with
      | mk y =>
        obtain ⟨x, rfl⟩ :=
          (TopCat.toSSetObj₀Equiv (X := Y)).symm.surjective x
        obtain ⟨y, rfl⟩ :=
          (TopCat.toSSetObj₀Equiv (X := Y)).symm.surjective y
        obtain ⟨e, rfl⟩ := SSet.FundamentalGroupoid.homMk_surjective f
        obtain ⟨e', rfl⟩ := SSet.FundamentalGroupoid.homMk_surjective g
        rw [singularFundamentalGroupoidFunctor_map_homMk,
          singularFundamentalGroupoidFunctor_map_homMk] at hfg
        change Path.Homotopic.Quotient.mk
            ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
              (counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x))
              (counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm y))) =
          Path.Homotopic.Quotient.mk
            ((TopCat.pathEquiv (TopCat.singularEdgePath e')).cast
              (counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x))
              (counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm y))) at hfg
        simp only [singularEdgePath_of_canonical,
          Path.Homotopic.Quotient.mk_cast] at hfg
        have hfg' :
            Path.Homotopic.Quotient.mk
                (TopCat.pathEquiv (TopCat.toSSetObjEdgeEquiv e)) =
              Path.Homotopic.Quotient.mk
                (TopCat.pathEquiv (TopCat.toSSetObjEdgeEquiv e')) := by
          let q := Path.Homotopic.Quotient.mk
            (TopCat.pathEquiv (TopCat.toSSetObjEdgeEquiv e))
          let q' := Path.Homotopic.Quotient.mk
            (TopCat.pathEquiv (TopCat.toSSetObjEdgeEquiv e'))
          have heq₀ :
              (q.cast
                (counit_realizedVertex
                  (TopCat.toSSetObj₀Equiv.symm x))
                (counit_realizedVertex
                  (TopCat.toSSetObj₀Equiv.symm y))) ≍ q :=
            Path.Homotopic.Quotient.cast_heq _ _
          have heq₁ :
              (q'.cast
                (counit_realizedVertex
                  (TopCat.toSSetObj₀Equiv.symm x))
                (counit_realizedVertex
                  (TopCat.toSSetObj₀Equiv.symm y))) ≍ q' :=
            Path.Homotopic.Quotient.cast_heq _ _
          exact eq_of_heq (heq₀.symm.trans ((heq_of_eq hfg).trans heq₁))
        obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hfg'
        let K := Path.Homotopy.toSingularHomotopy H
        let h := K.toSimplicialObjectHomotopy
        let d := Path.Homotopy.intervalEdge.{u}
        let diag : (TopCat.toSSet.obj Y).Edge
            (TopCat.toSSetObj₀Equiv.symm x)
            (TopCat.toSSetObj₀Equiv.symm y) :=
          SSet.Edge.ofEq
            (SSet.Edge.diagOfSimplicialObjectHomotopy h d)
            (by simpa [K] using
              Path.Homotopy.yonedaEdge_app_intervalVertexZero e)
            (by simpa [K] using
              Path.Homotopy.yonedaEdge_app_intervalVertexOne e')
        let c₀ : SSet.Edge.CompStruct
            (Path.Homotopy.intervalEdgeMap e)
            (Path.Homotopy.toSingularHomotopyTargetEdge H) diag :=
          (SSet.Edge.CompStruct.ofSimplicialObjectHomotopy h d).ofEq
            (by
              have he := congrArg SSet.Edge.edge
                ((TopCat.toSSetObjEdgeEquiv (X := Y)).symm_apply_apply e)
              dsimp [d, Path.Homotopy.intervalEdgeMap]
              rw [he]
              with_unfolding_all rfl) rfl rfl
        let c₁ : SSet.Edge.CompStruct
            (Path.Homotopy.toSingularHomotopySourceEdge H)
            (Path.Homotopy.intervalEdgeMap e') diag :=
          (SSet.Edge.CompStruct.ofSimplicialObjectHomotopy' h d).ofEq
            rfl (by
              have he' := congrArg SSet.Edge.edge
                ((TopCat.toSSetObjEdgeEquiv (X := Y)).symm_apply_apply e')
              dsimp [d, Path.Homotopy.intervalEdgeMap]
              rw [he']
              with_unfolding_all rfl) rfl
        calc
          SSet.FundamentalGroupoid.homMk e =
              SSet.FundamentalGroupoid.homMk
                (Path.Homotopy.intervalEdgeMap e) := by
            rw [Path.Homotopy.intervalEdgeMap_eq]
          _ =
              SSet.FundamentalGroupoid.homMk diag := by
            simpa only [Path.Homotopy.toSingularHomotopy_targetEdge,
              SSet.FundamentalGroupoid.homMk_id, Category.comp_id] using
                c₀.homMk_comp
          _ = SSet.FundamentalGroupoid.homMk
                (Path.Homotopy.intervalEdgeMap e') := by
            simpa only [Path.Homotopy.toSingularHomotopy_sourceEdge,
              SSet.FundamentalGroupoid.homMk_id, Category.id_comp] using
                c₁.homMk_comp.symm
          _ = SSet.FundamentalGroupoid.homMk e' := by
            rw [Path.Homotopy.intervalEdgeMap_eq]
  exact Functor.FullyFaithful.ofFullyFaithful F

/-- The combinatorial fundamental groupoid of the singular simplicial set is
equivalent to the ordinary topological fundamental groupoid. -/
noncomputable def singularFundamentalGroupoidEquivalence (Y : TopCat.{u}) :
    SSet.FundamentalGroupoid (TopCat.toSSet.obj Y) ≌
      _root_.FundamentalGroupoid Y := by
  let F := singularFundamentalGroupoidFunctor Y
  let hFF := singularFundamentalGroupoidFunctor_fullyFaithful Y
  let hES := singularFundamentalGroupoidFunctor_essSurj Y
  letI : F.IsEquivalence :=
    { faithful := hFF.faithful
      full := hFF.full
      essSurj := hES }
  exact F.asEquivalence

end TopCat

end
