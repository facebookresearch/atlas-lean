/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.ThresholdCoordinates
public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Finite
public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Nonsingular
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellCover
public import MathlibExt.Topology.Convenient.StdSimplexMinimalFace
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Topology.Homeomorph.Lemmas
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Realization isomorphisms of nonsingular subdivision

For a nonsingular simplicial set `X`, the realization of its categorical subdivision
is isomorphic to `|X|`. On each nondegenerate cell, the comparison is the affine
barycentric subdivision map. The pointwise cell law is stated in every universe;
the corresponding categorical cell-map equation here is stated in universe zero.

The comparison commutes with maps preserving nondegenerate simplices, in particular
with monomorphisms. Iterating the comparison gives realization isomorphisms for every
subdivision depth and isomorphisms of the corresponding realized arrows under these
monomorphism hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Simplicial Topology
open scoped Simplicial

noncomputable section

namespace SSet

private theorem nondegenerateMap_injective
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Function.Injective (SSet.N.map f) := by
  intro x y hxy
  apply SSet.N.subcomplex_injective
  apply le_antisymm
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]
  · rw [← SSet.Subcomplex.image_le_image_iff f]
    rw [← SSet.N.map_subcomplex, ← SSet.N.map_subcomplex, hxy]

private theorem mono_nondegenerateNerve_map
    {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (SSet.nondegenerateNerve.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  apply ComposableArrows.ext
    (h := fun i => nondegenerateMap_injective f
      (congrArg (fun z => z.obj i) hab))
    (w := by
      intro i hi
      subsingleton)

private theorem mono_sd_map_of_nonsingular
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] : Mono (SSet.sd.map f) := by
  have h :
      SSet.sd.map f ≫ (SSet.sdIsoNondegenerateNerve Y).hom =
        (SSet.sdIsoNondegenerateNerve X).hom ≫
          SSet.nondegenerateNerve.map f := by
    rw [SSet.sdIsoNondegenerateNerve_hom,
      SSet.sdIsoNondegenerateNerve_hom]
    exact SSet.sdToNondegenerateNerve.naturality f
  let _ : Mono (SSet.nondegenerateNerve.map f) :=
    mono_nondegenerateNerve_map f
  have : Mono ((SSet.sdIsoNondegenerateNerve X).hom ≫
      SSet.nondegenerateNerve.map f) := inferInstance
  exact mono_of_mono_fac h

private noncomputable def sdCellMapUp (n : SimplexCategory)
    {d : SimplexCategoryᵒᵖ}
    (σ : (SimplexCategory.sd.{u}.obj n).obj d) :
    C(Convexity.StdSimplex ℝ (Fin (d.unop.len + 1)),
      ULift.{u} (Convexity.StdSimplex ℝ (Fin (n.len + 1)))) :=
  ⟨fun q => ULift.up (SimplexCategory.sdCellMap σ q),
    continuous_uliftUp.comp (SimplexCategory.sdCellMap σ).continuous⟩

private noncomputable def sdCellSingularMap (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶
      TopCat.toSSet.obj
        (TopCat.uliftFunctor.obj
          (TopCat.of (Convexity.StdSimplex ℝ (Fin (n.len + 1))))) where
  app d := ↾fun σ =>
    (TopCat.toSSetObjEquiv
      (TopCat.uliftFunctor.obj
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n.len + 1))))) d).symm
      (sdCellMapUp n σ)
  naturality d e f := by
    obtain ⟨d, rfl⟩ : ∃ k, Opposite.op (SimplexCategory.mk k) = d :=
      ⟨d.unop.len, congrArg Opposite.op d.unop.mk_len⟩
    obtain ⟨e, rfl⟩ : ∃ k, Opposite.op (SimplexCategory.mk k) = e :=
      ⟨e.unop.len, congrArg Opposite.op e.unop.mk_len⟩
    ext σ
    apply (TopCat.toSSetObjEquiv
      (TopCat.uliftFunctor.obj
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n.len + 1)))))
      (Opposite.op (SimplexCategory.mk e))).injective
    change sdCellMapUp n ((SimplexCategory.sd.obj n).map f σ) =
      (sdCellMapUp n σ).comp
        ⟨Convexity.StdSimplex.map f.unop, by fun_prop⟩
    apply ContinuousMap.ext
    intro q
    change ULift.up (SimplexCategory.sdCellMap
      ((SimplexCategory.sd.obj n).map f σ) q) =
      ULift.up ((SimplexCategory.sdCellMap σ).comp
        (SSet.stdSimplex.toTopMap f.unop).hom q)
    exact congrArg ULift.up
      (DFunLike.congr_fun
        (SimplexCategory.sdCellMap_face σ f.unop).symm q)

private noncomputable def sdBarycentricMap (n : SimplexCategory) :
    SSet.toTop.obj (SimplexCategory.sd.{u}.obj n) ⟶
      TopCat.uliftFunctor.obj
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n.len + 1)))) :=
  (sSetTopAdj.homEquiv _ _).symm (sdCellSingularMap n)

private theorem sdBarycentricMap_cell_apply (n : SimplexCategory) {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    sdBarycentricMap n
        (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) =
      ULift.up (SimplexCategory.sdCellMap σ q) := by
  have hAdj := (sSetTopAdj.homEquiv
    (SimplexCategory.sd.{u}.obj n)
    (TopCat.uliftFunctor.obj
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n.len + 1)))))).apply_symm_apply
      (sdCellSingularMap n)
  rw [Adjunction.homEquiv_unit] at hAdj
  have hDown := congrArg (fun r => (r.app _ σ).down) hAdj
  change ((sSetTopAdj.unit.app
      (SimplexCategory.sd.{u}.obj n)).app _ σ).down ≫
        sdBarycentricMap n =
      ((sdCellSingularMap n).app _ σ).down at hDown
  rw [sSetTopAdj_unit_app_app_down] at hDown
  exact ConcreteCategory.congr_hom hDown (ULift.up q)

private theorem sdBarycentricMap_surjective (n : SimplexCategory) :
    Function.Surjective (sdBarycentricMap.{u} n) := by
  intro x
  let a : SSet.toTop.obj (SimplexCategory.sd.{u}.obj n) :=
    SSet.toTop.map
      (SSet.yonedaEquiv.symm (thresholdSimplex.{u} x.down))
      ((SimplexCategory.toTopHomeo.{u} ⦋thresholdDim x.down⦌).symm
        (thresholdWeights x.down))
  refine ⟨a, ?_⟩
  change sdBarycentricMap n
      (SSet.toTop.map
        (SSet.yonedaEquiv.symm (thresholdSimplex.{u} x.down))
        ((SimplexCategory.toTopHomeo.{u} ⦋thresholdDim x.down⦌).symm
          (thresholdWeights x.down))) = x
  rw [sdBarycentricMap_cell_apply, sdCellMap_threshold]
  exact ULift.up_down x

private theorem sdBarycentricMap_injective (n : SimplexCategory) :
    Function.Injective (sdBarycentricMap.{u} n) := by
  intro a b hab
  obtain ⟨d₁, σ₁, hσ₁, q₁, hq₁, ha⟩ :=
    SSet.exists_nonDegenerate_interior_presentation
      (SimplexCategory.sd.{u}.obj n) a
  obtain ⟨d₂, σ₂, hσ₂, q₂, hq₂, hb⟩ :=
    SSet.exists_nonDegenerate_interior_presentation
      (SimplexCategory.sd.{u}.obj n) b
  change ∀ i, 0 < q₁.weights i at hq₁
  change ∀ i, 0 < q₂.weights i at hq₂
  have hcell₁ : ULift.up (SimplexCategory.sdCellMap σ₁ q₁) =
      sdBarycentricMap n a := by
    rw [← ha]
    exact (sdBarycentricMap_cell_apply n σ₁ q₁).symm
  have hcell₂ : ULift.up (SimplexCategory.sdCellMap σ₂ q₂) =
      sdBarycentricMap n b := by
    rw [← hb]
    exact (sdBarycentricMap_cell_apply n σ₂ q₂).symm
  have hcell : SimplexCategory.sdCellMap σ₁ q₁ =
      SimplexCategory.sdCellMap σ₂ q₂ := by
    apply ULift.up_injective
    rw [hcell₁, hcell₂, hab]
  let c₁ : ThresholdCoordinates.{u} n.len :=
    ⟨SSet.N.mk σ₁ hσ₁, q₁, hq₁⟩
  let c₂ : ThresholdCoordinates.{u} n.len :=
    ⟨SSet.N.mk σ₂ hσ₂, q₂, hq₂⟩
  have hcoordinates : c₁ = c₂ :=
    (thresholdCoordinatesEquiv.{u} n.len).symm.injective hcell
  have hc : SSet.N.mk σ₁ hσ₁ = SSet.N.mk σ₂ hσ₂ :=
    congrArg ThresholdCoordinates.carrier hcoordinates
  have hpoint : HEq q₁ q₂ := by
    change HEq c₁.point c₂.point
    rw [hcoordinates]
  have hS := (SSet.N.ext_iff _ _).mp hc
  have hd := congrArg
    (fun s : (SimplexCategory.sd.{u}.obj n).S => s.dim) hS
  change d₁ = d₂ at hd
  subst d₂
  have hs : σ₁ = σ₂ := by
    change SSet.S.mk σ₁ = SSet.S.mk σ₂ at hS
    apply (SSet.S.ext_iff σ₁ σ₂).mp
    exact hS
  subst σ₂
  have hq : q₁ = q₂ := eq_of_heq hpoint
  rw [← ha, ← hb, hq]

private theorem sdBarycentricMap_isIso (n : SimplexCategory) :
    IsIso (sdBarycentricMap.{u} n) := by
  let _ : SSet.Finite (SimplexCategory.sd.{u}.obj n) := finite_sd_simplex n
  let _ : T2Space ↑(TopCat.uliftFunctor.obj
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n.len + 1))))) :=
    (TopCat.uliftFunctorObjHomeo
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n.len + 1))))).t2Space
  apply (TopCat.isIso_iff_isHomeomorph (sdBarycentricMap n)).mpr
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨(sdBarycentricMap n).hom.continuous,
    sdBarycentricMap_injective n, sdBarycentricMap_surjective n⟩

private theorem sdBarycentricMap_naturality {n m : SimplexCategory}
    (f : n ⟶ m) [Mono f] :
    SSet.toTop.map (SimplexCategory.sd.{u}.map f) ≫ sdBarycentricMap m =
      sdBarycentricMap n ≫
        TopCat.uliftFunctor.map (SSet.stdSimplex.toTopMap f) := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [sSetTopAdj.homEquiv_naturality_left,
    sSetTopAdj.homEquiv_naturality_right]
  simp only [sdBarycentricMap, Equiv.apply_symm_apply]
  ext d σ
  apply (TopCat.toSSetObjEquiv
    (TopCat.uliftFunctor.obj
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (m.len + 1))))) d).injective
  apply ContinuousMap.ext
  intro q
  change ULift.up (SimplexCategory.sdCellMap
      ((SimplexCategory.sd.map f).app d σ) q) =
    ULift.up ((SSet.stdSimplex.toTopMap f).hom
      (SimplexCategory.sdCellMap σ q))
  exact congrArg ULift.up
    (DFunLike.congr_fun
      (SimplexCategory.sdCellMap_natural_mono f σ) q)

private theorem realizedSimplexIsoUlift_naturality
    {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.toTop.map (SSet.stdSimplex.map f) ≫
        (TopCat.realizedSimplexIsoUlift.{u} m.len).hom =
      (TopCat.realizedSimplexIsoUlift.{u} n.len).hom ≫
        TopCat.uliftFunctor.map (SSet.stdSimplex.toTopMap f) := by
  apply TopCat.ext
  intro x
  apply ULift.down_injective
  exact SimplexCategory.toTopHomeo_naturality_apply f x

private theorem uliftMap_comp_realizedSimplexIsoUlift_inv
    {n m : SimplexCategory} (f : n ⟶ m) :
    TopCat.uliftFunctor.map (SSet.stdSimplex.toTopMap f) ≫
        (TopCat.realizedSimplexIsoUlift.{u} m.len).inv =
      (TopCat.realizedSimplexIsoUlift.{u} n.len).inv ≫
        SSet.toTop.map (SSet.stdSimplex.map f) := by
  apply (cancel_mono
    (TopCat.realizedSimplexIsoUlift.{u} m.len).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [realizedSimplexIsoUlift_naturality,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private noncomputable def representableSdIso (n : SimplexCategory) :
    SSet.toTop.obj
        (SSet.sd.obj (SSet.stdSimplex.obj n) : SSet.{u}) ≅
      SSet.toTop.obj (SSet.stdSimplex.obj n) :=
  let _ : IsIso (sdBarycentricMap.{u} n) :=
    sdBarycentricMap_isIso n
  SSet.toTop.mapIso (SSet.stdSimplex.sdIso.{u}.app n) ≪≫
    asIso (sdBarycentricMap.{u} n) ≪≫
      (TopCat.realizedSimplexIsoUlift.{u} n.len).symm

private theorem representableSdIso_hom_cell_apply
    (n : SimplexCategory) {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj n) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (representableSdIso n).hom
        (SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app n).app _ σ))
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) =
      (SimplexCategory.toTopHomeo.{u} n).symm
        (SimplexCategory.sdCellMap σ q) := by
  simp only [representableSdIso, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.symm_hom]
  have hsigma :
      (SSet.stdSimplex.sdIso.app n).hom.app _
          ((SSet.stdSimplex.sdIso.inv.app n).app _ σ) = σ := by
    have hcomp := Iso.inv_hom_id_app SSet.stdSimplex.sdIso n
    exact congrArg (fun f => f.app _ σ) hcomp
  have hcomp :
      SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app n).app _ σ)) ≫
        SSet.toTop.map (SSet.stdSimplex.sdIso.app n).hom =
      SSet.toTop.map (SSet.yonedaEquiv.symm σ) := by
    rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp, hsigma]
  change (TopCat.realizedSimplexIsoUlift n.len).inv
      (sdBarycentricMap n
        ((SSet.toTop.map
            (SSet.yonedaEquiv.symm
              ((SSet.stdSimplex.sdIso.inv.app n).app _ σ)) ≫
          SSet.toTop.map (SSet.stdSimplex.sdIso.app n).hom)
          ((SimplexCategory.toTopHomeo ⦋d⦌).symm q))) =
    (SimplexCategory.toTopHomeo n).symm
      (SimplexCategory.sdCellMap σ q)
  rw [hcomp, sdBarycentricMap_cell_apply]
  rfl

private theorem representableSdIso_naturality {n m : SimplexCategory}
    (f : n ⟶ m) [Mono f] :
    SSet.toTop.map
        (SSet.sd.map (SSet.stdSimplex.map f) :
          (SSet.sd.obj (SSet.stdSimplex.obj n) : SSet.{u}) ⟶ _) ≫
        (representableSdIso m).hom =
      (representableSdIso n).hom ≫
        SSet.toTop.map (SSet.stdSimplex.map f) := by
  simp only [representableSdIso, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.symm_hom, Category.assoc]
  have hsd : SSet.sd.map (SSet.stdSimplex.map f) ≫
      (SSet.stdSimplex.sdIso.{u}.app m).hom =
    (SSet.stdSimplex.sdIso.{u}.app n).hom ≫
      SimplexCategory.sd.{u}.map f :=
    SSet.stdSimplex.sdIso.{u}.hom.naturality f
  rw [← SSet.toTop.map_comp_assoc, hsd,
    SSet.toTop.map_comp_assoc]
  rw [reassoc_of% sdBarycentricMap_naturality.{u} f]
  rw [uliftMap_comp_realizedSimplexIsoUlift_inv f]
private noncomputable def representableDiagramIso
    (X : SSet.{u}) [X.Nonsingular] :
    X.functorN' ⋙ SSet.sd ⋙ SSet.toTop ≅ X.functorN' ⋙ SSet.toTop :=
  NatIso.ofComponents
    (fun x => representableSdIso ⦋x.dim⦌)
    (fun {x y} f => by
      change SSet.toTop.map
            (SSet.sd.map (SSet.stdSimplex.map
              (SSet.N.monoOfLE (leOfHom f)))) ≫
          (representableSdIso ⦋y.dim⦌).hom =
        (representableSdIso ⦋x.dim⦌).hom ≫
          SSet.toTop.map (SSet.stdSimplex.map
            (SSet.N.monoOfLE (leOfHom f)))
      exact representableSdIso_naturality
        (SSet.N.monoOfLE (leOfHom f)))

private noncomputable def sdFaceCocone
    (X : SSet.{u}) [X.Nonsingular] :=
  SSet.toTop.mapCocone (SSet.sd.mapCocone X.coconeN')

private noncomputable def topFaceCocone
    (X : SSet.{u}) [X.Nonsingular] :=
  SSet.toTop.mapCocone X.coconeN'

private noncomputable def isColimitSdFaceCocone
    (X : SSet.{u}) [X.Nonsingular] : IsColimit (sdFaceCocone X) :=
  isColimitOfPreserves SSet.toTop
    (isColimitOfPreserves SSet.sd X.isColimitCoconeN')

private noncomputable def isColimitTopFaceCocone
    (X : SSet.{u}) [X.Nonsingular] : IsColimit (topFaceCocone X) :=
  isColimitOfPreserves SSet.toTop X.isColimitCoconeN'

private noncomputable def preTopFaceCocone
    (X : SSet.{u}) [X.Nonsingular] :=
  (Cocone.precompose (representableDiagramIso X).hom).obj
    (topFaceCocone X)

private noncomputable def isColimitPreTopFaceCocone
    (X : SSet.{u}) [X.Nonsingular] : IsColimit (preTopFaceCocone X) :=
  (IsColimit.precomposeHomEquiv (representableDiagramIso X)
    (topFaceCocone X)).symm (isColimitTopFaceCocone X)

/--
For a nonsingular simplicial set `X`, the topological isomorphism
`|sd X| ≅ |X|` defined by the barycentric maps on its nondegenerate cells.
-/
@[no_expose]
noncomputable def toTopSdIso (X : SSet.{u}) [X.Nonsingular] :
    SSet.toTop.obj (SSet.sd.obj X) ≅ SSet.toTop.obj X :=
  (isColimitSdFaceCocone X).coconePointUniqueUpToIso
    (isColimitPreTopFaceCocone X)

private theorem toTopSdIso_fac (X : SSet.{u}) [X.Nonsingular]
    (x : X.N) :
    SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        (toTopSdIso X).hom =
      (representableSdIso ⦋x.dim⦌).hom ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex) := by
  have h := (isColimitSdFaceCocone X).comp_coconePointUniqueUpToIso_hom
      (isColimitPreTopFaceCocone X) x
  exact h

/--
On a subdivision simplex in a nondegenerate carrier of `X`, the realization
comparison evaluates by the affine barycentric cell map followed by the realization
of that carrier's simplex map, in the given universe.
-/
theorem toTopSdIso_hom_cell_apply
    (X : SSet.{u}) [X.Nonsingular]
    (x : X.N) {d : ℕ}
    (σ : (SimplexCategory.sd.{u}.obj ⦋x.dim⦌) _⦋d⦌)
    (q : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    (SSet.toTopSdIso X).hom
        (SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex))
          (SSet.toTop.map
            (SSet.yonedaEquiv.symm
              ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ))
            ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex)
        ((SimplexCategory.toTopHomeo.{u} ⦋x.dim⦌).symm
          (SimplexCategory.sdCellMap σ q)) := by
  change (SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        (SSet.toTopSdIso X).hom)
      (SSet.toTop.map
        (SSet.yonedaEquiv.symm
          ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ))
        ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q)) = _
  rw [toTopSdIso_fac X x]
  change SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex)
      ((representableSdIso ⦋x.dim⦌).hom
        (SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ))
          ((SimplexCategory.toTopHomeo.{u} ⦋d⦌).symm q))) = _
  rw [representableSdIso_hom_cell_apply]

/--
For a nonsingular universe-zero simplicial set, the realization comparison on a
nondegenerate subdivision cell equals its affine barycentric map followed by the
realized carrier simplex map, as an equality of topological morphisms.
-/
@[reassoc]
theorem toTopSdIso_hom_cell (X : SSet.{0}) [X.Nonsingular]
    (x : X.N) {d : ℕ}
    (σ : (SimplexCategory.sd.{0}.obj ⦋x.dim⦌) _⦋d⦌) :
    (SSet.stdSimplex.toTopIso ⦋d⦌).inv ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm
            ((SSet.stdSimplex.sdIso.inv.app ⦋x.dim⦌).app _ σ)) ≫
        SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        (SSet.toTopSdIso X).hom =
      TopCat.ofHom (SimplexCategory.sdCellMap σ) ≫
        (SSet.stdSimplex.toTopIso ⦋x.dim⦌).inv ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex) := by
  apply TopCat.ext
  intro q
  simpa [SSet.stdSimplex.toTopIso, TopCat.isoOfHomeo] using
    toTopSdIso_hom_cell_apply X x σ q

/--
For a map between nonsingular simplicial sets that preserves nondegenerate simplices,
subdividing and then applying the realization comparison commutes with the realized map.
-/
@[reassoc]
theorem toTopSdIso_hom_naturality
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y)
    (hf : ∀ {n : ℕ} (x : X _⦋n⦌),
      x ∈ X.nonDegenerate n → f.app _ x ∈ Y.nonDegenerate n) :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map f := by
  apply (isColimitSdFaceCocone X).hom_ext
  intro x
  let y : Y.N := SSet.N.mk (f.app _ x.simplex)
    (hf x.simplex x.nonDegenerate)
  have hy : y.simplex = f.app _ x.simplex := rfl
  have hcomp : SSet.yonedaEquiv.symm x.simplex ≫ f =
      SSet.yonedaEquiv.symm y.simplex := by
    exact SSet.yonedaEquiv_symm_comp x.simplex f
  have hYfac :
      SSet.toTop.map
            (SSet.sd.map
              (SSet.yonedaEquiv.symm (f.app _ x.simplex))) ≫
          (SSet.toTopSdIso Y).hom =
        (representableSdIso ⦋x.dim⦌).hom ≫
          SSet.toTop.map
            (SSet.yonedaEquiv.symm (f.app _ x.simplex)) := by
    exact toTopSdIso_fac Y y
  change SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        (SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom) =
      SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        ((SSet.toTopSdIso X).hom ≫ SSet.toTop.map f)
  calc
    SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        (SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom) =
      SSet.toTop.map (SSet.sd.map
          (SSet.yonedaEquiv.symm x.simplex ≫ f)) ≫
        (SSet.toTopSdIso Y).hom := by
          rw [← Category.assoc, ← SSet.toTop.map_comp,
            ← SSet.sd.map_comp]
    _ = SSet.toTop.map
          (SSet.sd.map
            (SSet.yonedaEquiv.symm (f.app _ x.simplex))) ≫
        (SSet.toTopSdIso Y).hom := by
      rw [hcomp, hy]
      rfl
    _ = (representableSdIso ⦋x.dim⦌).hom ≫
        SSet.toTop.map
          (SSet.yonedaEquiv.symm (f.app _ x.simplex)) := hYfac
    _ = (representableSdIso ⦋x.dim⦌).hom ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex ≫ f) := by
      rw [hcomp, hy]
      rfl
    _ = (representableSdIso ⦋x.dim⦌).hom ≫
        (SSet.toTop.map (SSet.yonedaEquiv.symm x.simplex) ≫
          SSet.toTop.map f) := by rw [SSet.toTop.map_comp]
    _ = SSet.toTop.map
          (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)) ≫
        ((SSet.toTopSdIso X).hom ≫ SSet.toTop.map f) := by
      simpa only [Category.assoc] using congrArg
        (fun g => g ≫ SSet.toTop.map f) (toTopSdIso_fac X x).symm

/--
The realization comparison for nonsingular subdivision is natural under
monomorphisms of simplicial sets.
-/
@[reassoc]
theorem toTopSdIso_hom_naturality_of_mono
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] :
    SSet.toTop.map (SSet.sd.map f) ≫ (SSet.toTopSdIso Y).hom =
      (SSet.toTopSdIso X).hom ≫ SSet.toTop.map f :=
  toTopSdIso_hom_naturality f (fun x hx => by
    exact (SSet.nonDegenerate_iff_of_mono f x).mpr hx)

private theorem mono_sdIter_map_of_nonsingular
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    Mono ((SSet.sdIter k).map f) := by
  induction k with
  | zero =>
      change Mono f
      infer_instance
  | succ k ih =>
      rw [SSet.sdIter_map_succ]
      let _ : Mono ((SSet.sdIter k).map f) := ih
      exact mono_sd_map_of_nonsingular ((SSet.sdIter k).map f)

/--
For a nonsingular simplicial set `X`, the topological isomorphism
`|sd^k X| ≅ |X|` obtained by composing the subdivision realization comparisons.
-/
noncomputable def toTopSdIterIso (X : SSet.{u}) [X.Nonsingular]
    (k : ℕ) : SSet.toTop.obj ((SSet.sdIter k).obj X) ≅
      SSet.toTop.obj X :=
  match k with
  | 0 => Iso.refl _
  | k + 1 => SSet.toTopSdIso ((SSet.sdIter k).obj X) ≪≫
    SSet.toTopSdIterIso X k

/--
The realization comparison at subdivision depth zero is the identity isomorphism.
-/
@[simp]
theorem toTopSdIterIso_zero (X : SSet.{u}) [X.Nonsingular] :
    SSet.toTopSdIterIso X 0 = Iso.refl _ :=
  rfl

/--
The comparison for `k + 1` subdivisions is the one-step comparison on `sd^k X`
followed by the comparison for `k` subdivisions.
-/
@[simp]
theorem toTopSdIterIso_succ (X : SSet.{u}) [X.Nonsingular] (k : ℕ) :
    SSet.toTopSdIterIso X (k + 1) =
      SSet.toTopSdIso ((SSet.sdIter k).obj X) ≪≫
        SSet.toTopSdIterIso X k :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
For a monomorphism between nonsingular simplicial sets, the iterated subdivision
realization comparisons commute with the corresponding realized maps at every depth.
-/
@[reassoc]
theorem toTopSdIterIso_hom_naturality_of_mono
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    SSet.toTop.map ((SSet.sdIter k).map f) ≫
        (SSet.toTopSdIterIso Y k).hom =
      (SSet.toTopSdIterIso X k).hom ≫ SSet.toTop.map f := by
  induction k with
  | zero => simp
  | succ k ih =>
      let _ : Mono ((SSet.sdIter k).map f) :=
        mono_sdIter_map_of_nonsingular f k
      simp only [SSet.sdIter_map_succ, SSet.toTopSdIterIso_succ,
        Iso.trans_hom]
      rw [reassoc_of% SSet.toTopSdIso_hom_naturality_of_mono
        ((SSet.sdIter k).map f)]
      rw [ih, ← Category.assoc]

/--
For a monomorphism between nonsingular simplicial sets, the realized subdivided
arrow is isomorphic to the original realized arrow, using the source and target
iterated subdivision comparisons.
-/
noncomputable def toTopSdIterArrowIso
    {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) [Mono f] (k : ℕ) :
    Arrow.mk (SSet.toTop.map ((SSet.sdIter k).map f)) ≅
      Arrow.mk (SSet.toTop.map f) :=
  Arrow.isoMk (SSet.toTopSdIterIso X k)
    (SSet.toTopSdIterIso Y k)
    (SSet.toTopSdIterIso_hom_naturality_of_mono f k).symm

end SSet
