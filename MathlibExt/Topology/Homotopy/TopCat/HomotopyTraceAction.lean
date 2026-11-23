/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy

/-!
# Homotopy traces and basepoint transport

The point trace of a continuous homotopy agrees with the corresponding
arrow in the singular fundamental groupoid. The induced maps on positive
homotopy groups are compared using that actual trace as the basepoint path,
including formulas with explicit endpoint equalities.

Homotopic paths induce the same basepoint transport. These comparisons use
the existing singular-complex and simplicial-homotopy APIs.
-/

@[expose] public section

universe u

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial Topology Topology.Homotopy

namespace TopCat

section Part1


private theorem trace_toSSetObjEquiv_map_apply
    {X Y : TopCat.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (s : (TopCat.toSSet.obj X).obj n)
    (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n s) z =
      f (X.toSSetObjEquiv n s z) :=
  rfl

private theorem trace_toSSetObjEquiv_mu_apply
    (X Y : TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (s : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y).obj n)
    (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (X ⊗ Y).toSSetObjEquiv n
        ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n s) z =
      (X.toSSetObjEquiv n s.1 z, Y.toSSetObjEquiv n s.2 z) := by
  apply _root_.Prod.ext
  · have h := congrArg (fun k => k.app n s)
      (Functor.Monoidal.μ_fst (F := TopCat.toSSet) X Y)
    exact congrArg (fun t => X.toSSetObjEquiv n t z) h
  · have h := congrArg (fun k => k.app n s)
      (Functor.Monoidal.μ_snd (F := TopCat.toSSet) X Y)
    exact congrArg (fun t => Y.toSSetObjEquiv n t z) h

/-- The degree-one vertex trace of the singular homotopy is the singular
edge of the original ordinary trace, with time directed from `f` to `g`. -/
theorem singularHomotopy_trace_edge
    {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (x : X) :
    (SSet.Edge.ofSimplicialObjectHomotopy
      H.toSSet.toSimplicialObjectHomotopy (TopCat.toSSetObj₀Equiv.symm x)).edge =
      TopCat.toSSetObj₁Equiv.symm
        ((TopCat.pathEquiv (X := Y)).symm (H.evalAt x)).hom := by
  rw [SSet.Edge.ofSimplicialObjectHomotopy_edge]
  apply (TopCat.toSSetObj₁Equiv (X := Y)).injective
  ext t
  let s := (SSet.prodStdSimplex₁.nonDegenerateEquiv (0 : Fin 1)).1
  let pre := (((SSet.yonedaEquiv.symm (TopCat.toSSetObj₀Equiv.symm x) ▷
      (Δ[1] : SSet.{u})) ≫
      (TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI)).app _ s)
  change Y.toSSetObjEquiv _
      ((TopCat.toSSet.map H.h).app _
        ((Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app _ pre))
      (TopCat.stdSimplexHomeomorphI.symm t) = _
  rw [trace_toSSetObjEquiv_map_apply, trace_toSSetObjEquiv_mu_apply]
  have hpre₀' : pre.1 = (TopCat.toSSet.obj X).σ 0
      (TopCat.toSSetObj₀Equiv.symm x) := by
    change (SSet.yonedaEquiv.symm (TopCat.toSSetObj₀Equiv.symm x)).app _ s.1 = _
    have hs₀ : s.1 = SSet.stdSimplex.objEquiv.symm
        (SimplexCategory.σ (0 : Fin 1)) := by
      simp [s]
    rewrite [hs₀, SSet.yonedaEquiv_symm_app_objEquiv_symm]
    rfl
  have hpre₁' : pre.2 = SSet.yonedaEquiv SSet.stdSimplex.toSSetObjI := by
    change SSet.stdSimplex.toSSetObjI.app _ s.2 = _
    have hs₁ : s.2 = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
      calc
        s.2 = SSet.stdSimplex.objMk₁ (0 : Fin 1).succ.castSucc := by
          simp [s]
        _ = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
          apply SSet.stdSimplex.objEquiv.injective
          decide
    rewrite [hs₁, ← SSet.yonedaEquiv_comp]
    simp
  have hpre₀ : X.toSSetObjEquiv (op ⦋1⦌) pre.1
      (TopCat.stdSimplexHomeomorphI.symm t) = x := by
    rw [hpre₀']
    simp [TopCat.toSSetObj₀Equiv]
  have hpre₁ : TopCat.I.toSSetObjEquiv (op ⦋1⦌) pre.2
      (TopCat.stdSimplexHomeomorphI.symm t) = t := by
    rw [hpre₁', TopCat.yonedaEquiv_toSSetObjI]
    exact ConcreteCategory.congr_hom
      ((TopCat.toSSetObj₁Equiv (X := TopCat.I)).apply_symm_apply (𝟙 TopCat.I)) t
  rw [hpre₀, hpre₁]
  change H (TopCat.I.homeomorph t, x) =
    TopCat.toSSetObj₁Equiv
      (TopCat.toSSetObj₁Equiv.symm
        ((TopCat.pathEquiv (X := Y)).symm (H.evalAt x)).hom) t
  rewrite [Equiv.apply_symm_apply]
  rfl

/-- The natural isomorphism on singular fundamental groupoids follows
the exact ordinary basepoint trace. -/
theorem singularHomotopy_trace
    {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (x : X) :
    (SSet.congrMapFundamentalGroupoid H.toSSet).hom.app
        (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x)) =
      TopCat.singularPathHom Y (H.evalAt x) := by
  change SSet.FundamentalGroupoid.homMk
      (SSet.Edge.ofSimplicialObjectHomotopy
        H.toSSet.toSimplicialObjectHomotopy (TopCat.toSSetObj₀Equiv.symm x)) =
    SSet.FundamentalGroupoid.homMk
      ((TopCat.toSSetObjEdgeEquiv (X := Y)).symm
        ((TopCat.pathEquiv (X := Y)).symm (H.evalAt x)))
  congr 1
  apply SSet.Edge.ext
  exact singularHomotopy_trace_edge H x

private theorem trace_singularPi_map
    {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) (x : X)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    let KX := TopCat.toSSet.obj X
    let KY := TopCat.toSSet.obj Y
    let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
    TopCat.homotopyGroupSingularMulEquiv n Y (f x) (HomotopyGroup.map f.hom a) =
      SSet.KanComplex.π.map (TopCat.toSSet.map f) rfl (n + 1)
        (TopCat.homotopyGroupSingularMulEquiv n X x a) := by
  let E := TopCat.homotopyGroupSingularMulEquiv n Y (f x)
  have hNat := TopCat.homotopyGroupSingularMulEquiv_naturality.{u}
    (X := X) (Y := Y) n f (x := x) (y := f x) rfl a
  have hNative : HomotopyGroup.mapHomOfEq f.hom (rfl : f x = f x) n a =
      HomotopyGroup.map f.hom a := HomotopyGroup.mapHomOfEq_apply f.hom rfl n a
  exact (congrArg E hNative).symm.trans hNat

/-- Induced positive homotopy-group maps of an ordinary homotopy differ
by transport along its actual basepoint trace. -/
theorem homotopyGroup_map_homotopy_trace
    {X Y : TopCat.{u}} (n : ℕ) {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (x : X)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n Y (H.evalAt x)
        (HomotopyGroup.map f.hom a) =
      HomotopyGroup.map g.hom a := by
  let KX := TopCat.toSSet.obj X
  let KY := TopCat.toSSet.obj Y
  let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
  apply (TopCat.homotopyGroupSingularMulEquiv n Y (g x)).injective
  rw [TopCat.homotopyGroupSingularMulEquiv_basepointChange,
    trace_singularPi_map, trace_singularPi_map, ← singularHomotopy_trace H x]
  exact SSet.KanComplex.π.action_map_eq_map_of_homotopy H.toSSet
    (TopCat.homotopyGroupSingularMulEquiv n X x a)

/-- Endpoint-fixed homotopic paths have the same morphism in the actual
singular fundamental groupoid. -/
theorem singularPathHom_eq_of_homotopic
    (X : TopCat.{u}) {x y : X} {p q : _root_.Path x y} (h : p.Homotopic q) :
    TopCat.singularPathHom X p = TopCat.singularPathHom X q := by
  apply (TopCat.singularFundamentalGroupoidFunctor_fullyFaithful X).map_injective
  simp only [TopCat.singularPathHom,
    TopCat.singularFundamentalGroupoidFunctor_map_homMk,
    TopCat.singularEdgePath_of_canonical, Equiv.apply_symm_apply,
    Path.Homotopic.Quotient.mk_cast]
  exact congrArg
    (fun r : Path.Homotopic.Quotient x y => r.cast
      (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x))
      (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm y)))
    (Path.Homotopic.Quotient.eq.mpr h)

/-- Endpoint-fixed path homotopy leaves positive basepoint transport
unchanged; this uses the existing transport, not a replacement definition. -/
theorem homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic
    (n : ℕ) (X : TopCat.{u}) {x y : X} {p q : _root_.Path x y}
    (h : p.Homotopic q) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p =
      TopCat.homotopyGroupBasepointChangeMulEquiv n X q := by
  unfold TopCat.homotopyGroupBasepointChangeMulEquiv
  rw [singularPathHom_eq_of_homotopic X h]

end Part1

section Part2


/-- The actual homotopy trace formula with explicitly aligned endpoint
basepoints.  Both maps and the path are transported by the same equalities. -/
theorem homotopyGroup_map_homotopy_trace_of_eq
    {X Y : TopCat.{u}} (n : ℕ) {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (x : X) {y₀ y₁ : Y}
    (h₀ : f x = y₀) (h₁ : g x = y₁)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n Y
        ((H.evalAt x).cast h₀.symm h₁.symm)
        (HomotopyGroup.mapHomOfEq f.hom h₀ n a) =
      HomotopyGroup.mapHomOfEq g.hom h₁ n a := by
  cases h₀
  cases h₁
  change TopCat.homotopyGroupBasepointChangeMulEquiv n Y (H.evalAt x)
    (HomotopyGroup.map f.hom a) = HomotopyGroup.map g.hom a
  exact TopCat.homotopyGroup_map_homotopy_trace n H x a

end Part2

end TopCat

end
