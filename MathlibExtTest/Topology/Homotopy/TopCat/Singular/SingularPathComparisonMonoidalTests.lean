/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularPathComparisonMonoidal

/-!
# Monoidal singular-path characteristic clients

These clients pin the exact uncurried formula in symbolic and concrete
universes, retain the approved strict postcomposition naturality, and verify
that the private comparison bridge and later endpoint/loop surface do not
leak from this precursor.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial
  Functor.LaxMonoidal
open scoped Simplicial

universe u

namespace SSet

/-- Symbolic-universe client for the exact lax-monoidal formula. -/
example (X : Type u) [TopologicalSpace X] :
    MonoidalClosed.uncurry (singularPathComparison X) =
      (SSet.stdSimplex.toSSetObjI.{u} ▷
          TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
        μ TopCat.toSSet TopCat.I.{u}
          (TopCat.of C(unitInterval, X)) ≫
        TopCat.toSSet.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{u}).hom.app
              (TopCat.of C(unitInterval, X))) ≫
        TopCat.toSSet.map
          ((TopCat.intervalContinuousMapEvaluation X) :
            (Limits.prod.functor.obj TopCat.I.{u}).obj
                (TopCat.of C(unitInterval, X)) ⟶
              TopCat.of X) :=
  singularPathComparison_uncurry_lax X

/-- The characteristic remains exact after taking the topological adjoint. -/
example (X : Type u) [TopologicalSpace X] :
    SSet.toTop.map
          (MonoidalClosed.uncurry (singularPathComparison X)) ≫
        sSetTopAdj.counit.app (TopCat.of X) =
      SSet.toTop.map
          ((SSet.stdSimplex.toSSetObjI.{u} ▷
              TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
            μ TopCat.toSSet TopCat.I.{u}
              (TopCat.of C(unitInterval, X)) ≫
            TopCat.toSSet.map
              ((CartesianMonoidalCategory.tensorLeftIsoProd
                TopCat.I.{u}).hom.app
                  (TopCat.of C(unitInterval, X))) ≫
            TopCat.toSSet.map
              ((TopCat.intervalContinuousMapEvaluation X) :
                (Limits.prod.functor.obj TopCat.I.{u}).obj
                    (TopCat.of C(unitInterval, X)) ⟶
                  TopCat.of X)) ≫
        sSetTopAdj.counit.app (TopCat.of X) := by
  rw [singularPathComparison_uncurry_lax]

/-- Approved strict naturality remains available to mate consumers. -/
example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    TopCat.toSSet.map (TopCat.intervalContinuousMapPostcomp f) ≫
        singularPathComparison Y =
      singularPathComparison X ≫
        (ihom (Δ[1] : SSet.{u})).map
          (TopCat.toSSet.map (TopCat.ofHom f)) :=
  singularPathComparison_naturality f

/-- Explicit universe-zero mate client. -/
example (X : Type) [TopologicalSpace X] :
    MonoidalClosed.uncurry (singularPathComparison X) =
      (SSet.stdSimplex.toSSetObjI.{0} ▷
          TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
        μ TopCat.toSSet TopCat.I.{0}
          (TopCat.of C(unitInterval, X)) ≫
        TopCat.toSSet.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{0}).hom.app
              (TopCat.of C(unitInterval, X))) ≫
        TopCat.toSSet.map
          ((TopCat.intervalContinuousMapEvaluation X) :
            (Limits.prod.functor.obj TopCat.I.{0}).obj
                (TopCat.of C(unitInterval, X)) ⟶
              TopCat.of X) :=
  singularPathComparison_uncurry_lax X

/-- Explicit universe-one mate client. -/
example (X : Type 1) [TopologicalSpace X] :
    MonoidalClosed.uncurry (singularPathComparison X) =
      (SSet.stdSimplex.toSSetObjI.{1} ▷
          TopCat.toSSet.obj (TopCat.of C(unitInterval, X))) ≫
        μ TopCat.toSSet TopCat.I.{1}
          (TopCat.of C(unitInterval, X)) ≫
        TopCat.toSSet.map
          ((CartesianMonoidalCategory.tensorLeftIsoProd
            TopCat.I.{1}).hom.app
              (TopCat.of C(unitInterval, X))) ≫
        TopCat.toSSet.map
          ((TopCat.intervalContinuousMapEvaluation X) :
            (Limits.prod.functor.obj TopCat.I.{1}).obj
                (TopCat.of C(unitInterval, X)) ⟶
              TopCat.of X) :=
  singularPathComparison_uncurry_lax X

#guard_msgs (error, substring := true) in
#check toTop_tensor_prodComparison

#guard_msgs (error, substring := true) in
#check prodFunctorFst

#guard_msgs (error, substring := true) in
#synth SSet.toTop.{0}.OplaxMonoidal

#guard_msgs (error, substring := true) in
#check singularPathComparison_eval₀

#guard_msgs (error, substring := true) in
#check singularBasedPathComparison

#guard_msgs (error, substring := true) in
#check singularLoopComparison

#print axioms SSet.singularPathComparison_uncurry_lax

end SSet
