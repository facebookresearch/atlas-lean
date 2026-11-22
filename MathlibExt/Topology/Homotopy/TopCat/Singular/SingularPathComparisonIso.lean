/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathComparison

/-!
# The singular/free-path comparison is an isomorphism

The forward comparison from singular simplices in a compact-open free path
space to the simplicial internal-hom path space has an explicit inverse.  The
inverse realizes a simplicial path, uses the inverse finite-product
comparison for `Δ[1]`, evaluates, and then curries back into the compact-open
path space.

Only the free-path comparison is treated here.  There is no endpoint-fiber
restriction, based-path or loop isomorphism, weak-equivalence theorem,
homotopy-group shift, weakly pointed preservation theorem, or Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial
open scoped Simplicial

universe u

namespace SSet

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Reorder the compact-open uncurrying domain into realized interval first,
realized simplicial carrier second. -/
private noncomputable def compactOpenToRealizedPath (K : SSet.{u}) :
    TopCat.of (↑(SSet.toTop.obj K) × unitInterval) ⟶
      SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K :=
  (Limits.prod.lift
      (TopCat.ofHom ContinuousMap.fst)
      (TopCat.ofHom
        { toFun := fun z : ↑(SSet.toTop.obj K) × unitInterval =>
            TopCat.I.homeomorph.symm z.2
          continuous_toFun :=
            TopCat.I.homeomorph.symm.continuous.comp continuous_snd }) :
      TopCat.of (↑(SSet.toTop.obj K) × unitInterval) ⟶
        SSet.toTop.obj K ⨯ TopCat.I.{u}) ≫
    Limits.prod.map (𝟙 (SSet.toTop.obj K))
      SSet.stdSimplex.toTopObjIsoI.inv ≫
    (Limits.prod.braiding (SSet.toTop.obj K)
      (SSet.toTop.obj (Δ[1] : SSet.{u}))).hom

/-- Reverse the realized interval/path ordering and identify the realized
interval with the ordinary unit interval. -/
private noncomputable def realizedPathToCompactOpenDomainAux
    (K : SSet.{u}) :
    SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K ⟶
      TopCat.of (↑(SSet.toTop.obj K) × unitInterval) :=
  TopCat.ofHom
    { toFun := fun z =>
        ((Limits.prod.snd :
            SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K ⟶
              SSet.toTop.obj K) z,
          TopCat.I.homeomorph
            (SSet.stdSimplex.toTopObjIsoI.hom
              ((Limits.prod.fst :
                SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K ⟶
                  SSet.toTop.obj (Δ[1] : SSet.{u})) z)))
      continuous_toFun :=
        (Limits.prod.snd :
          SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K ⟶
            SSet.toTop.obj K).hom.continuous.prodMk
          (TopCat.I.homeomorph.continuous.comp
            (SSet.stdSimplex.toTopObjIsoI.hom.hom.continuous.comp
              (Limits.prod.fst :
                SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K ⟶
                  SSet.toTop.obj (Δ[1] : SSet.{u})).hom.continuous)) }

/-- The ordinary compact-open uncurrying domain is canonically isomorphic to
the product of the realized simplicial interval and the realized carrier. -/
noncomputable def compactOpenRealizedPathIso (K : SSet.{u}) :
    TopCat.of (↑(SSet.toTop.obj K) × unitInterval) ≅
      SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯ SSet.toTop.obj K where
  hom := compactOpenToRealizedPath K
  inv := realizedPathToCompactOpenDomainAux K
  hom_inv_id := by
    apply TopCat.hom_ext
    ext z <;> simp [compactOpenToRealizedPath,
      realizedPathToCompactOpenDomainAux]
  inv_hom_id := by
    apply Limits.prod.hom_ext
    · apply TopCat.hom_ext
      ext z
      simp [compactOpenToRealizedPath,
        realizedPathToCompactOpenDomainAux]
    · apply TopCat.hom_ext
      ext z
      simp [compactOpenToRealizedPath,
        realizedPathToCompactOpenDomainAux]

@[reassoc]
private theorem toTop_map_tensorLeftIsoProd_inv_hom
    (K : SSet.{u}) :
    SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).inv.app K) ≫
      SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).hom.app K) =
      𝟙 (SSet.toTop.obj
        ((Limits.prod.functor.obj (Δ[1] : SSet.{u})).obj K)) := by
  erw [← SSet.toTop.map_comp, Iso.inv_hom_id,
    SSet.toTop.map_id]

@[reassoc]
private theorem toTop_map_tensorLeftIsoProd_hom_inv
    (K : SSet.{u}) :
    SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).hom.app K) ≫
      SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).inv.app K) =
      𝟙 (SSet.toTop.obj
        ((tensorLeft (Δ[1] : SSet.{u})).obj K)) := by
  erw [← SSet.toTop.map_comp, Iso.hom_inv_id,
    SSet.toTop.map_id]

/-- The evaluation map used in the inverse comparison, before compact-open
currying. -/
noncomputable def pathComparisonInvEvaluation
    (X : Type u) [TopologicalSpace X] :
    TopCat.of
        (↑(SSet.toTop.obj
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) ×
            unitInterval) ⟶
      TopCat.of X := by
  let K := SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))
  let _ : IsIso
      (Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u}) K) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary (Δ[1] : SSet.{u}) K
  exact
    compactOpenToRealizedPath K ≫
      inv (Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u}) K) ≫
      SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).inv.app K) ≫
      SSet.toTop.map (MonoidalClosed.uncurry (𝟙 K)) ≫
      sSetTopAdj.counit.app (TopCat.of X)

/-- Compact-open curry of the inverse evaluation map. -/
noncomputable def singularPathComparisonInvAdjunct
    (X : Type u) [TopologicalSpace X] :
    SSet.toTop.obj
        (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ⟶
      TopCat.of C(unitInterval, X) :=
  TopCat.ofHom (ContinuousMap.curry (pathComparisonInvEvaluation X).hom)

/-- Candidate inverse to the singular/free-path comparison. -/
noncomputable def singularPathComparisonInv
    (X : Type u) [TopologicalSpace X] :
    SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) ⟶
      TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) :=
  sSetTopAdj.homEquiv _ _ (singularPathComparisonInvAdjunct X)

/-- Reorder a realized simplicial path and a realized interval into the raw
compact-open evaluation domain. -/
noncomputable def realizedPathToCompactOpenDomain
    (X : Type u) [TopologicalSpace X] :
    SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯
        SSet.toTop.obj
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ⟶
      TopCat.of
        (↑(SSet.toTop.obj
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) ×
            unitInterval) :=
  realizedPathToCompactOpenDomainAux
    (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))

/-- Exact beta square for compact-open currying and realized simplicial path
evaluation. -/
theorem singularPathComparisonInv_beta
    (X : Type u) [TopologicalSpace X] :
    Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
          (singularPathComparisonInvAdjunct X) ≫
        TopCat.intervalContinuousMapEvaluation X =
      realizedPathToCompactOpenDomain X ≫
        pathComparisonInvEvaluation X := by
  apply TopCat.hom_ext
  ext z
  have hfst := ConcreteCategory.congr_hom
    (Limits.prod.map_fst SSet.stdSimplex.toTopObjIsoI.hom
      (singularPathComparisonInvAdjunct X)) z
  have hsnd := ConcreteCategory.congr_hom
    (Limits.prod.map_snd SSet.stdSimplex.toTopObjIsoI.hom
      (singularPathComparisonInvAdjunct X)) z
  with_unfolding_all
    change
      (Limits.prod.fst : TopCat.I.{u} ⨯
          TopCat.of C(unitInterval, X) ⟶ TopCat.I.{u})
          (Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
            (singularPathComparisonInvAdjunct X) z) =
        SSet.stdSimplex.toTopObjIsoI.hom
          ((Limits.prod.fst :
            SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯
              SSet.toTop.obj
                (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ⟶
              SSet.toTop.obj (Δ[1] : SSet.{u})) z) at hfst
  with_unfolding_all
    change
      (Limits.prod.snd : TopCat.I.{u} ⨯
          TopCat.of C(unitInterval, X) ⟶
            TopCat.of C(unitInterval, X))
          (Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
            (singularPathComparisonInvAdjunct X) z) =
        singularPathComparisonInvAdjunct X
          ((Limits.prod.snd :
            SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯
              SSet.toTop.obj
                (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ⟶
              SSet.toTop.obj
                (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) z) at hsnd
  with_unfolding_all
    change
      ((Limits.prod.snd : TopCat.I.{u} ⨯
          TopCat.of C(unitInterval, X) ⟶
            TopCat.of C(unitInterval, X))
          (Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
            (singularPathComparisonInvAdjunct X) z))
        (TopCat.I.homeomorph
          ((Limits.prod.fst : TopCat.I.{u} ⨯
            TopCat.of C(unitInterval, X) ⟶ TopCat.I.{u})
              (Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
                (singularPathComparisonInvAdjunct X) z))) =
      singularPathComparisonInvAdjunct X
        ((Limits.prod.snd :
          SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯
            SSet.toTop.obj
              (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ⟶
            SSet.toTop.obj
              (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) z)
        (TopCat.I.homeomorph
          (SSet.stdSimplex.toTopObjIsoI.hom
            ((Limits.prod.fst :
              SSet.toTop.obj (Δ[1] : SSet.{u}) ⨯
                SSet.toTop.obj
                  (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ⟶
                SSet.toTop.obj (Δ[1] : SSet.{u})) z)))
  rw [hfst, hsnd]

@[reassoc]
private theorem singularPathComparisonInv_product_maps
    (X : Type u) [TopologicalSpace X] :
    (Limits.prod.map
        (SSet.toTop.map (𝟙 (Δ[1] : SSet.{u})))
        (SSet.toTop.map (singularPathComparisonInv X)) ≫
      (Limits.prod.functor.map
        SSet.stdSimplex.toTopObjIsoI.hom).app
          (SSet.toTop.obj
            (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))))) ≫
      (Limits.prod.functor.obj TopCat.I.{u}).map
        (sSetTopAdj.counit.app (TopCat.of C(unitInterval, X))) =
    Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
      (singularPathComparisonInvAdjunct X) := by
  have hInvAdj :
      SSet.toTop.map (singularPathComparisonInv X) ≫
          sSetTopAdj.counit.app (TopCat.of C(unitInterval, X)) =
        singularPathComparisonInvAdjunct X := by
    exact (sSetTopAdj.homEquiv _ _).symm_apply_apply
      (singularPathComparisonInvAdjunct X)
  erw [SSet.toTop.map_id]
  rw [Limits.prod.functor_map_app,
    Limits.prod.functor_obj_map]
  erw [Limits.prod.map_map]
  simp only [Category.comp_id]
  erw [Limits.prod.map_map]
  simp only [Category.id_comp, Category.comp_id]
  rw [hInvAdj]

@[reassoc]
private theorem singularPathComparisonInv_prodComparison_product_maps
    (X : Type u) [TopologicalSpace X] :
    Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u})
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ≫
        (Limits.prod.map
            (SSet.toTop.map (𝟙 (Δ[1] : SSet.{u})))
            (SSet.toTop.map (singularPathComparisonInv X)) ≫
          (Limits.prod.functor.map
            SSet.stdSimplex.toTopObjIsoI.hom).app
              (SSet.toTop.obj
                (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))))) ≫
          (Limits.prod.functor.obj TopCat.I.{u}).map
            (sSetTopAdj.counit.app (TopCat.of C(unitInterval, X))) =
      Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u})
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ≫
        Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
          (singularPathComparisonInvAdjunct X) := by
  rw [singularPathComparisonInv_product_maps]

private theorem singularPathComparisonInv_forward_prefix
    (X : Type u) [TopologicalSpace X] :
    SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            (Δ[1] : SSet.{u})).hom.app
              (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) ≫
        (((Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u})
              (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ≫
            Limits.prod.map
              (SSet.toTop.map (𝟙 (Δ[1] : SSet.{u})))
              (SSet.toTop.map (singularPathComparisonInv X))) ≫
          (Limits.prod.functor.map
            SSet.stdSimplex.toTopObjIsoI.hom).app
              (SSet.toTop.obj
                (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))))) ≫
          (Limits.prod.functor.obj TopCat.I.{u}).map
            (sSetTopAdj.counit.app (TopCat.of C(unitInterval, X)))) ≫
        TopCat.intervalContinuousMapEvaluation X =
      (SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            (Δ[1] : SSet.{u})).hom.app
              (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) ≫
        Limits.prodComparison SSet.toTop (Δ[1] : SSet.{u})
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) ≫
        Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
          (singularPathComparisonInvAdjunct X)) ≫
        TopCat.intervalContinuousMapEvaluation X := by
  simpa only [Category.assoc] using
    congrArg
      (fun f => SSet.toTop.map
        ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).hom.app
            (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) ≫
        f ≫ TopCat.intervalContinuousMapEvaluation X)
      (singularPathComparisonInv_prodComparison_product_maps X)

private noncomputable def intervalUncurry
    {A : TopCat.{u}} {X : Type u} [TopologicalSpace X]
    (f : A ⟶ TopCat.of C(unitInterval, X)) :
    TopCat.of (↑A × unitInterval) ⟶ TopCat.of X :=
  TopCat.ofHom (ContinuousMap.uncurry f.hom)

private theorem intervalUncurry_injective
    {A : TopCat.{u}} {X : Type u} [TopologicalSpace X] :
    Function.Injective
      (intervalUncurry (A := A) (X := X)) := by
  intro f g h
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro t
  exact ConcreteCategory.congr_hom h (a, t)

private noncomputable def compactOpenDomainMap
    {A B : TopCat.{u}} (f : A ⟶ B) :
    TopCat.of (↑A × unitInterval) ⟶
      TopCat.of (↑B × unitInterval) :=
  TopCat.ofHom
    { toFun := fun z => (f z.1, z.2)
      continuous_toFun := f.hom.continuous.comp continuous_fst |>.prodMk
        continuous_snd }

private theorem intervalUncurry_comp_curry
    {A B : TopCat.{u}} {X : Type u} [TopologicalSpace X]
    (f : A ⟶ B) (e : TopCat.of (↑B × unitInterval) ⟶ TopCat.of X) :
    intervalUncurry
        (f ≫ TopCat.ofHom (ContinuousMap.curry e.hom)) =
      compactOpenDomainMap f ≫ e := by
  apply TopCat.hom_ext
  ext z
  rfl

private theorem compactOpenToRealizedPath_naturality
    {K L : SSet.{u}} (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L) :
    compactOpenDomainMap f ≫ compactOpenToRealizedPath L =
      compactOpenToRealizedPath K ≫
        Limits.prod.map (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u}))) f := by
  apply Limits.prod.hom_ext
  · apply TopCat.hom_ext
    ext z
    simp [compactOpenDomainMap, compactOpenToRealizedPath]
  · apply TopCat.hom_ext
    ext z
    simp [compactOpenDomainMap, compactOpenToRealizedPath]

private theorem intervalUncurry_factorization
    (K : SSet.{u}) {X : Type u} [TopologicalSpace X]
    (f : SSet.toTop.obj K ⟶ TopCat.of C(unitInterval, X)) :
    intervalUncurry f =
      compactOpenToRealizedPath K ≫
        Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom f ≫
          TopCat.intervalContinuousMapEvaluation X := by
  apply TopCat.hom_ext
  ext z
  simp [intervalUncurry, compactOpenToRealizedPath,
    TopCat.intervalContinuousMapEvaluation]
  rfl

/-- The forward comparison followed by the explicit inverse is the identity. -/
theorem singularPathComparison_hom_inv_id
    (X : Type u) [TopologicalSpace X] :
    singularPathComparison X ≫ singularPathComparisonInv X = 𝟙 _ := by
  apply (sSetTopAdj.homEquiv
    (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))
    (TopCat.of C(unitInterval, X))).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hInvAdj :
      SSet.toTop.map (singularPathComparisonInv X) ≫
          sSetTopAdj.counit.app (TopCat.of C(unitInterval, X)) =
        singularPathComparisonInvAdjunct X := by
    exact (sSetTopAdj.homEquiv _ _).symm_apply_apply
      (singularPathComparisonInvAdjunct X)
  rw [hInvAdj]
  rw [SSet.toTop.map_id, Category.id_comp]
  apply intervalUncurry_injective
  rw [intervalUncurry_factorization
    (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))
    (sSetTopAdj.counit.app (TopCat.of C(unitInterval, X)))]
  unfold singularPathComparisonInvAdjunct
  rw [intervalUncurry_comp_curry]
  unfold pathComparisonInvEvaluation
  dsimp only
  rw [← Category.assoc, compactOpenToRealizedPath_naturality,
    Category.assoc]
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u})
      (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary
      (Δ[1] : SSet.{u}) _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u})
      (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary
      (Δ[1] : SSet.{u}) _
  have hProd :
      Limits.prod.map (𝟙 (SSet.toTop.obj (Δ[1] : SSet.{u})))
          (SSet.toTop.map (singularPathComparison X)) ≫
        inv (Limits.prodComparison SSet.toTop
          (Δ[1] : SSet.{u})
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) =
      inv (Limits.prodComparison SSet.toTop
          (Δ[1] : SSet.{u})
          (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))) ≫
        SSet.toTop.map (Limits.prod.map (𝟙 (Δ[1] : SSet.{u}))
          (singularPathComparison X)) := by
    simpa using
      (Limits.prodComparison_inv_natural SSet.toTop
        (𝟙 (Δ[1] : SSet.{u})) (singularPathComparison X)).symm
  slice_lhs 2 3 => rw [hProd]
  have hTensor :=
    (CartesianMonoidalCategory.tensorLeftIsoProd
      (Δ[1] : SSet.{u})).inv.naturality
        (singularPathComparison X)
  slice_lhs 3 4 =>
    rw [← Limits.prod.functor_obj_map]
    erw [← SSet.toTop.map_comp]
    erw [hTensor]
  have hUncurry :
      (tensorLeft (Δ[1] : SSet.{u})).map
          (singularPathComparison X) ≫
      MonoidalClosed.uncurry
          (𝟙 (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) =
      MonoidalClosed.uncurry (singularPathComparison X) := by
    change ((Δ[1] : SSet.{u}) ◁ singularPathComparison X) ≫
        MonoidalClosed.uncurry
          (𝟙 (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) = _
    rw [← MonoidalClosed.uncurry_natural_left]
    simp
  have hInner :
      ((CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).inv.app
            (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
        (tensorLeft (Δ[1] : SSet.{u})).map
          (singularPathComparison X)) ≫
        MonoidalClosed.uncurry
          (𝟙 (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) =
      (CartesianMonoidalCategory.tensorLeftIsoProd
          (Δ[1] : SSet.{u})).inv.app
            (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
        MonoidalClosed.uncurry (singularPathComparison X) := by
    rw [Category.assoc, hUncurry]
  slice_lhs 3 4 =>
    erw [← SSet.toTop.map_comp]
    erw [hInner]
    erw [SSet.toTop.map_comp]
  slice_lhs 4 5 => rw [singularPathComparison_adjunct]
  slice_lhs 3 5 =>
    erw [toTop_map_tensorLeftIsoProd_inv_hom_assoc]
  slice_lhs 2 4 =>
    erw [IsIso.inv_hom_id_assoc]

/-- The explicit inverse followed by the forward comparison is the identity. -/
theorem singularPathComparison_inv_hom_id
    (X : Type u) [TopologicalSpace X] :
    singularPathComparisonInv X ≫ singularPathComparison X = 𝟙 _ := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    singularPathComparison_uncurry,
    MonoidalClosed.uncurry_id_eq_ev]
  apply (sSetTopAdj.homEquiv
    ((Δ[1] : SSet.{u}) ⊗
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))
    (TopCat.of X)).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hForwardAdj :
      SSet.toTop.map
          (sSetTopAdj.homEquiv _ _
            (singularPathComparisonAdjunct X)) ≫
        sSetTopAdj.counit.app (TopCat.of X) =
      singularPathComparisonAdjunct X := by
    exact (sSetTopAdj.homEquiv _ _).symm_apply_apply
      (singularPathComparisonAdjunct X)
  slice_lhs 2 3 => rw [hForwardAdj]
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u})
      (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary
      (Δ[1] : SSet.{u}) _
  let _ : IsIso (Limits.prodComparison SSet.toTop
      (Δ[1] : SSet.{u})
      (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary
      (Δ[1] : SSet.{u}) _
  unfold singularPathComparisonAdjunct
  have hTensorHom :=
    (CartesianMonoidalCategory.tensorLeftIsoProd
      (Δ[1] : SSet.{u})).hom.naturality
        (singularPathComparisonInv X)
  slice_lhs 1 2 =>
    erw [← SSet.toTop.map_comp]
    erw [hTensorHom]
    erw [SSet.toTop.map_comp]
  have hProdNat := Limits.prodComparison_natural
    (F := SSet.toTop) (𝟙 (Δ[1] : SSet.{u}))
      (singularPathComparisonInv X)
  slice_lhs 2 3 =>
    rw [Limits.prod.functor_obj_map,
      Limits.prodComparisonNatTrans_app]
    erw [hProdNat]
  erw [singularPathComparisonInv_forward_prefix]
  erw [Category.assoc]
  erw [Category.assoc]
  erw [singularPathComparisonInv_beta]
  unfold realizedPathToCompactOpenDomain
  unfold pathComparisonInvEvaluation
  dsimp only
  rw [show realizedPathToCompactOpenDomainAux
      (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) =
        (compactOpenRealizedPathIso
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))).inv from rfl]
  rw [show compactOpenToRealizedPath
      (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X))) =
        (compactOpenRealizedPathIso
          (SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)))).hom from rfl]
  rw [Iso.inv_hom_id_assoc]
  erw [IsIso.hom_inv_id_assoc]
  erw [toTop_map_tensorLeftIsoProd_hom_inv_assoc]
  rw [MonoidalClosed.uncurry_id_eq_ev]

/-- The singular simplicial set of the compact-open free path space is
canonically isomorphic to the simplicial free path space of the singular
simplicial set. -/
noncomputable def singularPathIso
    (X : Type u) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ≅
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) where
  hom := singularPathComparison X
  inv := singularPathComparisonInv X
  hom_inv_id := singularPathComparison_hom_inv_id X
  inv_hom_id := singularPathComparison_inv_hom_id X

end SSet
