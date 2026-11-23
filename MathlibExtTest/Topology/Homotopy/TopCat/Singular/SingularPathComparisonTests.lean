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
# Singular/free-path comparison clients

These tests pin the literal interval evaluation formula, both endpoints, the
adjunction characteristic, strict postcomposition naturality, and clients in
universes zero and one.  They make no inverse, based-path, loop-space,
weak-equivalence, or Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial
open scoped Simplicial

universe u

namespace TopCat

/-- Direct client for the interval evaluation morphism. -/
example (X : Type u) [TopologicalSpace X] :
    TopCat.I.{u} ⨯ TopCat.of C(unitInterval, X) ⟶ TopCat.of X :=
  intervalContinuousMapEvaluation X

/-- Evaluation has the pinned pointwise formula. -/
example (X : Type u) [TopologicalSpace X]
    (t : TopCat.I.{u}) (gamma : C(unitInterval, X)) :
    intervalContinuousMapEvaluation X
        ((TopCat.prodIsoProd TopCat.I.{u}
          (TopCat.of C(unitInterval, X))).inv (t, gamma)) =
      gamma (TopCat.I.homeomorph t) :=
  by
    rw [intervalContinuousMapEvaluation_apply,
      TopCat.prodIsoProd_inv_fst_apply,
      TopCat.prodIsoProd_inv_snd_apply]

/-- Evaluation at the zero endpoint recovers the source value of the path. -/
example (X : Type u) [TopologicalSpace X]
    (gamma : C(unitInterval, X)) :
    intervalContinuousMapEvaluation X
        ((TopCat.prodIsoProd TopCat.I.{u}
          (TopCat.of C(unitInterval, X))).inv
            ((0 : TopCat.I.{u}), gamma)) = gamma 0 := by
  rw [intervalContinuousMapEvaluation_apply,
    TopCat.prodIsoProd_inv_fst_apply,
    TopCat.prodIsoProd_inv_snd_apply,
    TopCat.I.homeomorph_zero]

/-- Evaluation at the one endpoint recovers the target value of the path. -/
example (X : Type u) [TopologicalSpace X]
    (gamma : C(unitInterval, X)) :
    intervalContinuousMapEvaluation X
        ((TopCat.prodIsoProd TopCat.I.{u}
          (TopCat.of C(unitInterval, X))).inv
            ((1 : TopCat.I.{u}), gamma)) = gamma 1 := by
  rw [intervalContinuousMapEvaluation_apply,
    TopCat.prodIsoProd_inv_fst_apply,
    TopCat.prodIsoProd_inv_snd_apply,
    TopCat.I.homeomorph_one]

/-- The postcomposition morphism has the literal continuous-map formula. -/
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (gamma : C(unitInterval, X)) :
    intervalContinuousMapPostcomp f gamma = f.comp gamma :=
  intervalContinuousMapPostcomp_apply f gamma

/-- Compact-open postcomposition preserves the identity strictly. -/
example (X : Type u) [TopologicalSpace X] :
    intervalContinuousMapPostcomp (ContinuousMap.id X) =
      𝟙 (TopCat.of C(unitInterval, X)) := by
  apply TopCat.hom_ext
  ext gamma t
  rfl

/-- Compact-open postcomposition preserves composition strictly. -/
example {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    intervalContinuousMapPostcomp f ≫
        intervalContinuousMapPostcomp g =
      intervalContinuousMapPostcomp (g.comp f) := by
  apply TopCat.hom_ext
  ext gamma t
  rfl

/-- Evaluation is strictly natural in the target space. -/
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    Limits.prod.map (𝟙 TopCat.I.{u})
          (intervalContinuousMapPostcomp f) ≫
        intervalContinuousMapEvaluation Y =
      intervalContinuousMapEvaluation X ≫ TopCat.ofHom f :=
  intervalContinuousMapEvaluation_naturality f

end TopCat

namespace SSet

/-- Universe-polymorphic forward comparison client. -/
example (X : Type u) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ⟶
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) :=
  singularPathComparison X

/-- The uncurry characteristic is available to downstream clients. -/
example (X : Type u) [TopologicalSpace X] :
    MonoidalClosed.uncurry (singularPathComparison X) =
      sSetTopAdj.homEquiv _ _ (singularPathComparisonAdjunct X) :=
  singularPathComparison_uncurry X

/-- The topological adjunct is exactly the declared evaluation composite. -/
example (X : Type u) [TopologicalSpace X] :
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
        TopCat.intervalContinuousMapEvaluation X :=
  singularPathComparison_adjunct X

/-- Strict naturality client for an arbitrary continuous map. -/
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    TopCat.toSSet.map (TopCat.intervalContinuousMapPostcomp f) ≫
        singularPathComparison Y =
      singularPathComparison X ≫
        (ihom (Δ[1] : SSet.{u})).map
          (TopCat.toSSet.map (TopCat.ofHom f)) :=
  singularPathComparison_naturality f

/-- Identity is a direct strict-naturality specialization. -/
example (X : Type u) [TopologicalSpace X] :
    TopCat.toSSet.map
          (TopCat.intervalContinuousMapPostcomp (ContinuousMap.id X)) ≫
        singularPathComparison X =
      singularPathComparison X ≫
        (ihom (Δ[1] : SSet.{u})).map
          (TopCat.toSSet.map
            (TopCat.ofHom (ContinuousMap.id X))) :=
  singularPathComparison_naturality (ContinuousMap.id X)

/-- Composition is a direct strict-naturality specialization. -/
example {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    TopCat.toSSet.map
          (TopCat.intervalContinuousMapPostcomp (g.comp f)) ≫
        singularPathComparison Z =
      singularPathComparison X ≫
        (ihom (Δ[1] : SSet.{u})).map
          (TopCat.toSSet.map (TopCat.ofHom (g.comp f))) :=
  singularPathComparison_naturality (g.comp f)

/-- Explicit universe-zero client. -/
example (X : Type) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ⟶
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) :=
  singularPathComparison X

/-- Explicit universe-one client. -/
example (X : Type 1) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of C(unitInterval, X)) ⟶
      SSet.pathSpace (TopCat.toSSet.obj (TopCat.of X)) :=
  singularPathComparison X

#print axioms TopCat.intervalContinuousMapEvaluation
#print axioms TopCat.intervalContinuousMapEvaluation_apply
#print axioms TopCat.intervalContinuousMapPostcomp
#print axioms TopCat.intervalContinuousMapPostcomp_apply
#print axioms TopCat.intervalContinuousMapEvaluation_naturality
#print axioms SSet.singularPathComparisonAdjunct
#print axioms SSet.singularPathComparison
#print axioms SSet.singularPathComparison_uncurry
#print axioms SSet.singularPathComparison_adjunct
#print axioms SSet.singularPathComparison_naturality

end SSet
