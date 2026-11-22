/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.CompactOpen
public import Mathlib.AlgebraicTopology.SingularSet
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationProductComparisonBraid
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationProductComparisonNaturality

/-!
# Singular simplices in a free path space

For a space X, the singular simplicial set of the compact-open free path
space maps naturally to the simplicial internal-hom path space of Sing X.
The construction is the adjoint of literal interval evaluation after the
realization product comparison.

Only the forward free-path comparison and strict postcomposition naturality
are asserted.  There is no inverse, isomorphism, based-path or loop factor,
weak-equivalence, homotopy-group shift, or Q/S claim.
-/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial
open scoped Simplicial

universe u

namespace TopCat

/-- Evaluate a compact-open path at the point of the ordinary unit interval
represented by an element of the universe-lifted TopCat interval. -/
noncomputable def intervalContinuousMapEvaluation
    (X : Type u) [TopologicalSpace X] :
  TopCat.I.{u} ⨯ TopCat.of C(unitInterval, X) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := fun z =>
        ((Limits.prod.snd : TopCat.I.{u} ⨯
          TopCat.of C(unitInterval, X) ⟶
            TopCat.of C(unitInterval, X)) z)
          (TopCat.I.homeomorph
            ((Limits.prod.fst : TopCat.I.{u} ⨯
              TopCat.of C(unitInterval, X) ⟶ TopCat.I.{u}) z))
      continuous_toFun := continuous_eval.comp
        ((Limits.prod.snd : TopCat.I.{u} ⨯
            TopCat.of C(unitInterval, X) ⟶
              TopCat.of C(unitInterval, X)).hom.continuous.prodMk
          (TopCat.I.homeomorph.continuous.comp
            (Limits.prod.fst : TopCat.I.{u} ⨯
              TopCat.of C(unitInterval, X) ⟶ TopCat.I.{u}).hom.continuous)) }

@[simp]
theorem intervalContinuousMapEvaluation_apply
    (X : Type u) [TopologicalSpace X]
    (z : ↑(TopCat.I.{u} ⨯ TopCat.of C(unitInterval, X))) :
    intervalContinuousMapEvaluation X z =
      ((Limits.prod.snd : TopCat.I.{u} ⨯
        TopCat.of C(unitInterval, X) ⟶
          TopCat.of C(unitInterval, X)) z)
        (TopCat.I.homeomorph
          ((Limits.prod.fst : TopCat.I.{u} ⨯
            TopCat.of C(unitInterval, X) ⟶ TopCat.I.{u}) z)) :=
  rfl

/-- Postcomposition on compact-open maps from the unit interval. -/
noncomputable def intervalContinuousMapPostcomp
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    TopCat.of C(unitInterval, X) ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom
    { toFun := ContinuousMap.comp f
      continuous_toFun := ContinuousMap.continuous_postcomp f }

@[simp]
theorem intervalContinuousMapPostcomp_apply
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (gamma : C(unitInterval, X)) :
    intervalContinuousMapPostcomp f gamma = f.comp gamma :=
  rfl

/-- Evaluation commutes strictly with postcomposition. -/
theorem intervalContinuousMapEvaluation_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    Limits.prod.map (𝟙 TopCat.I.{u})
        (intervalContinuousMapPostcomp f) ≫
        intervalContinuousMapEvaluation Y =
      intervalContinuousMapEvaluation X ≫ TopCat.ofHom f := by
  apply TopCat.hom_ext
  ext z
  let m := Limits.prod.map (𝟙 TopCat.I.{u})
    (intervalContinuousMapPostcomp f)
  let fstX : TopCat.I.{u} ⨯ TopCat.of C(unitInterval, X) ⟶
      TopCat.I.{u} := Limits.prod.fst
  let fstY : TopCat.I.{u} ⨯ TopCat.of C(unitInterval, Y) ⟶
      TopCat.I.{u} := Limits.prod.fst
  let sndX : TopCat.I.{u} ⨯ TopCat.of C(unitInterval, X) ⟶
      TopCat.of C(unitInterval, X) := Limits.prod.snd
  let sndY : TopCat.I.{u} ⨯ TopCat.of C(unitInterval, Y) ⟶
      TopCat.of C(unitInterval, Y) := Limits.prod.snd
  have hfst : fstY (m z) = fstX z := by
    simpa only [m, fstX, fstY, ConcreteCategory.comp_apply,
      CategoryTheory.id_apply] using
      ConcreteCategory.congr_hom
        (Limits.prod.map_fst (𝟙 TopCat.I.{u})
          (intervalContinuousMapPostcomp f)) z
  have hsnd : sndY (m z) = intervalContinuousMapPostcomp f (sndX z) := by
    simpa only [m, sndX, sndY, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom
        (Limits.prod.map_snd (𝟙 TopCat.I.{u})
          (intervalContinuousMapPostcomp f)) z
  change sndY (m z) (TopCat.I.homeomorph (fstY (m z))) =
    f (sndX z (TopCat.I.homeomorph (fstX z)))
  rw [hfst, hsnd]
  rfl

end TopCat

namespace SSet

/-- Topological adjoint underlying the singular/free-path comparison. -/
noncomputable def singularPathComparisonAdjunct
    (X : Type u) [TopologicalSpace X] :
    SSet.toTop.obj
        ((Δ[1] : SSet.{u}) ⊗
          TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ⟶
      TopCat.of X :=
  SSet.toTop.map
      ((CartesianMonoidalCategory.tensorLeftIsoProd
        (Δ[1] : SSet.{u})).hom.app
          (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))) ≫
    (Limits.prodComparisonNatTrans SSet.toTop
      (Δ[1] : SSet.{u})).app
        (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
    (Limits.prod.functor.map
      SSet.stdSimplex.toTopObjIsoI.hom).app
        (SSet.toTop.obj
          (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))) ≫
    (Limits.prod.functor.obj TopCat.I.{u}).map
      (sSetTopAdj.counit.app (TopCat.of C(unitInterval, X))) ≫
    TopCat.intervalContinuousMapEvaluation X

private theorem singularPathComparisonAdjunct_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    SSet.toTop.map
        ((Δ[1] : SSet.{u}) ◁
          TopCat.toSSet.map (TopCat.intervalContinuousMapPostcomp f)) ≫
        singularPathComparisonAdjunct Y =
      singularPathComparisonAdjunct X ≫ TopCat.ofHom f := by
  let SX := TopCat.toSSet.obj (TopCat.of C(unitInterval, X))
  let SY := TopCat.toSSet.obj (TopCat.of C(unitInterval, Y))
  let m := TopCat.toSSet.map (TopCat.intervalContinuousMapPostcomp f)
  let e := CartesianMonoidalCategory.tensorLeftIsoProd
    (Δ[1] : SSet.{u})
  let p := Limits.prodComparisonNatTrans SSet.toTop
    (Δ[1] : SSet.{u})
  let j := Limits.prod.functor.map
    SSet.stdSimplex.toTopObjIsoI.hom
  let pI := Limits.prod.functor.obj TopCat.I.{u}
  have hTensor := e.hom.naturality m
  have hProd :
      SSet.toTop.map ((Limits.prod.functor.obj
          (Δ[1] : SSet.{u})).map m) ≫ p.app SY =
        p.app SX ≫
          (Limits.prod.functor.obj
            (SSet.toTop.obj (Δ[1] : SSet.{u}))).map
              (SSet.toTop.map m) := by
    simpa only [SX, SY, Functor.comp_map] using p.naturality m
  have hInterval := j.naturality (SSet.toTop.map m)
  have hCounit :
      SSet.toTop.map m ≫
          sSetTopAdj.counit.app (TopCat.of C(unitInterval, Y)) =
        sSetTopAdj.counit.app (TopCat.of C(unitInterval, X)) ≫
          TopCat.intervalContinuousMapPostcomp f := by
    simpa only [m, Functor.comp_map, Functor.id_map] using
      sSetTopAdj.counit.naturality
        (TopCat.intervalContinuousMapPostcomp f)
  have hCounitProd :
      Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map m) ≫
          Limits.prod.map (𝟙 TopCat.I.{u})
            (sSetTopAdj.counit.app
              (TopCat.of C(unitInterval, Y))) =
        Limits.prod.map (𝟙 TopCat.I.{u})
            (sSetTopAdj.counit.app
              (TopCat.of C(unitInterval, X))) ≫
          Limits.prod.map (𝟙 TopCat.I.{u})
            (TopCat.intervalContinuousMapPostcomp f) := by
    rw [Limits.prod.map_map, Limits.prod.map_map,
      Category.comp_id, hCounit]
  unfold singularPathComparisonAdjunct
  change
    SSet.toTop.map ((tensorLeft (Δ[1] : SSet.{u})).map m) ≫
          SSet.toTop.map (e.hom.app SY) ≫ p.app SY ≫
            j.app (SSet.toTop.obj SY) ≫
              pI.map (sSetTopAdj.counit.app
                (TopCat.of C(unitInterval, Y))) ≫
                TopCat.intervalContinuousMapEvaluation Y =
      SSet.toTop.map (e.hom.app SX) ≫ p.app SX ≫
          j.app (SSet.toTop.obj SX) ≫
            pI.map (sSetTopAdj.counit.app
              (TopCat.of C(unitInterval, X))) ≫
              TopCat.intervalContinuousMapEvaluation X ≫
                TopCat.ofHom f
  dsimp only [pI]
  rw [← Category.assoc, ← SSet.toTop.map_comp,
    hTensor, SSet.toTop.map_comp, Category.assoc]
  slice_lhs 2 3 => rw [hProd]
  slice_lhs 3 4 => rw [hInterval]
  unfold Limits.prod.functor
  slice_lhs 4 5 => rw [hCounitProd]
  slice_lhs 5 6 =>
    rw [TopCat.intervalContinuousMapEvaluation_naturality]

/-- Forward comparison from singular simplices in the compact-open free path
space to the simplicial internal-hom path space. -/
noncomputable def singularPathComparison
    (X : Type u) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ⟶
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) :=
  MonoidalClosed.curry
    (sSetTopAdj.homEquiv _ _ (singularPathComparisonAdjunct X))

/-- Uncurrying the comparison recovers the simplicial adjunct of the stated
topological evaluation map. -/
theorem singularPathComparison_uncurry
    (X : Type u) [TopologicalSpace X] :
    MonoidalClosed.uncurry (singularPathComparison X) =
      sSetTopAdj.homEquiv _ _ (singularPathComparisonAdjunct X) := by
  unfold singularPathComparison
  rw [MonoidalClosed.uncurry_curry]

/-- The topological adjunct of the comparison is exactly interval evaluation
after the realization product comparison and the adjunction counit. -/
theorem singularPathComparison_adjunct
    (X : Type u) [TopologicalSpace X] :
    SSet.toTop.map (MonoidalClosed.uncurry (singularPathComparison X)) ≫
        sSetTopAdj.counit.app (TopCat.of X) =
      SSet.toTop.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            (Δ[1] : SSet.{u})).hom.app
              (TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))) ≫
        Limits.prodComparison SSet.toTop
          (Δ[1] : SSet.{u})
          (TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
        Limits.prod.map SSet.stdSimplex.toTopObjIsoI.hom
          (sSetTopAdj.counit.app (TopCat.of C(unitInterval, X))) ≫
        TopCat.intervalContinuousMapEvaluation X := by
  rw [singularPathComparison_uncurry]
  calc
    SSet.toTop.map
          (sSetTopAdj.homEquiv _ _ (singularPathComparisonAdjunct X)) ≫
        sSetTopAdj.counit.app (TopCat.of X) =
      (sSetTopAdj.homEquiv _ _).symm
        (sSetTopAdj.homEquiv _ _ (singularPathComparisonAdjunct X)) :=
          (sSetTopAdj.homEquiv_counit
            ((Δ[1] : SSet.{u}) ⊗
              TopCat.toSSet.obj (TopCat.of C(unitInterval, X)))
            (TopCat.of X)
            (sSetTopAdj.homEquiv _ _
              (singularPathComparisonAdjunct X))).symm
    _ = singularPathComparisonAdjunct X :=
      (sSetTopAdj.homEquiv _ _).symm_apply_apply
      (singularPathComparisonAdjunct X)
    _ = _ := by
      unfold singularPathComparisonAdjunct
      simp only [Limits.prodComparisonNatTrans_app,
        Limits.prod.functor_map_app,
        Limits.prod.functor_obj_map]
      unfold Limits.prod.functor
      slice_lhs 3 4 =>
        rw [Limits.prod.map_map, Category.comp_id,
          Category.id_comp]

/-- The singular/free-path comparison commutes strictly with
postcomposition. -/
theorem singularPathComparison_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    TopCat.toSSet.map (TopCat.intervalContinuousMapPostcomp f) ≫
        singularPathComparison Y =
      singularPathComparison X ≫
        (ihom (Δ[1] : SSet.{u})).map
          (TopCat.toSSet.map (TopCat.ofHom f)) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_natural_right]
  rw [singularPathComparison_uncurry,
    singularPathComparison_uncurry]
  calc
    ((Δ[1] : SSet.{u}) ◁
          TopCat.toSSet.map (TopCat.intervalContinuousMapPostcomp f)) ≫
        sSetTopAdj.homEquiv _ _ (singularPathComparisonAdjunct Y) =
      sSetTopAdj.homEquiv _ _
        (SSet.toTop.map
            ((Δ[1] : SSet.{u}) ◁
              TopCat.toSSet.map
                (TopCat.intervalContinuousMapPostcomp f)) ≫
          singularPathComparisonAdjunct Y) :=
            (sSetTopAdj.homEquiv_naturality_left _ _).symm
    _ = sSetTopAdj.homEquiv _ _
        (singularPathComparisonAdjunct X ≫ TopCat.ofHom f) := by
          rw [singularPathComparisonAdjunct_naturality]
    _ = sSetTopAdj.homEquiv _ _ (singularPathComparisonAdjunct X) ≫
        TopCat.toSSet.map (TopCat.ofHom f) :=
          sSetTopAdj.homEquiv_naturality_right _ _

end SSet
