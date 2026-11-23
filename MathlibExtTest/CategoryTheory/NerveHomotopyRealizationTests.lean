/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.NerveHomotopyRealization
import Mathlib.CategoryTheory.Category.ULift

/-!
# Realized nerve-homotopy component tests

Consumer tests for the realized natural-transformation component edge,
including identity and nonidentity transformations and a raised-universe
client.  These tests make no classifying-space, H-space, or weak-equivalence
claim.
-/

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.CategoryTheory.NerveHomotopyRealizationTests

noncomputable section

section Generic

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {F G : C ⥤ D} (alpha : F ⟶ G) (c : C)

example :
    Limits.prod.lift (𝟙 TopCat.I.{u})
        (TopCat.const
          (SSet.realizedVertex (ComposableArrows.mk₀ c))) ≫
        SSet.realizeHomotopyMap (nerve C) (nerve D)
          (nerveMap F) (nerveMap G)
          (NatTrans.nerveHomotopy alpha) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom :=
  SSet.realizeHomotopyMap_nerveHomotopy_vertex alpha c

example (t : TopCat.I.{u}) :
    SSet.realizeHomotopyMap (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (NatTrans.nerveHomotopy alpha)
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom t :=
  SSet.realizeHomotopyMap_nerveHomotopy_vertex_apply alpha c t

example :
    (SSet.realizeHomotopy (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (NatTrans.nerveHomotopy alpha)).evalAt
          (SSet.realizedVertex (ComposableArrows.mk₀ c)) =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (alpha.app c)))).cast
        (SSet.nerveMap_realizedVertex F c)
        (SSet.nerveMap_realizedVertex G c) :=
  SSet.realizeHomotopy_nerveHomotopy_evalAt alpha c

/-- The identity natural transformation is a direct client. -/
example (t : TopCat.I.{u}) :
    SSet.realizeHomotopyMap (nerve C) (nerve C)
        (nerveMap (𝟭 C)) (nerveMap (𝟭 C))
        (NatTrans.nerveHomotopy (𝟙 (𝟭 C)))
        ((TopCat.prodIsoProd TopCat.I.{u}
          (SSet.toTop.obj (nerve C))).inv
          (t, SSet.realizedVertex (ComposableArrows.mk₀ c))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (𝟙 c))).hom t :=
  SSet.realizeHomotopyMap_nerveHomotopy_vertex_apply
    (𝟙 (𝟭 C)) c t

end Generic

section Nonidentity

abbrev TestSource := Discrete PUnit

def lowerFunctor : TestSource ⥤ Fin 2 :=
  (Functor.const TestSource).obj 0

def upperFunctor : TestSource ⥤ Fin 2 :=
  (Functor.const TestSource).obj 1

def stepNat : lowerFunctor ⟶ upperFunctor where
  app _ := by
    change (0 : Fin 2) ⟶ (1 : Fin 2)
    exact homOfLE (by decide)
  naturality _ _ _ := Subsingleton.elim _ _

example (t : TopCat.I) :
    SSet.realizeHomotopyMap (nerve TestSource) (nerve (Fin 2))
        (nerveMap lowerFunctor) (nerveMap upperFunctor)
        (NatTrans.nerveHomotopy stepNat)
        ((TopCat.prodIsoProd TopCat.I
          (SSet.toTop.obj (nerve TestSource))).inv
          (t, SSet.realizedVertex
            (ComposableArrows.mk₀ (Discrete.mk PUnit.unit)))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk
          (stepNat.app (Discrete.mk PUnit.unit)))).hom t :=
  SSet.realizeHomotopyMap_nerveHomotopy_vertex_apply
    stepNat (Discrete.mk PUnit.unit) t

example :
    (SSet.realizeHomotopy (nerve TestSource) (nerve (Fin 2))
        (nerveMap lowerFunctor) (nerveMap upperFunctor)
        (NatTrans.nerveHomotopy stepNat)).evalAt
          (SSet.realizedVertex
            (ComposableArrows.mk₀ (Discrete.mk PUnit.unit))) =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk
            (stepNat.app (Discrete.mk PUnit.unit))))).cast
        (SSet.nerveMap_realizedVertex lowerFunctor
          (Discrete.mk PUnit.unit))
        (SSet.nerveMap_realizedVertex upperFunctor
          (Discrete.mk PUnit.unit)) :=
  SSet.realizeHomotopy_nerveHomotopy_evalAt
    stepNat (Discrete.mk PUnit.unit)

end Nonidentity

section RaisedUniverse

abbrev RaisedSource :=
  ULiftHom.{1} (ULift.{1} (Discrete PUnit))

def raisedIdentity : RaisedSource ⥤ RaisedSource := 𝟭 RaisedSource

def raisedObject : RaisedSource :=
  ULiftHom.objUp (ULift.up (Discrete.mk PUnit.unit))

example (t : TopCat.I.{1}) :
    SSet.realizeHomotopyMap (nerve RaisedSource) (nerve RaisedSource)
        (nerveMap raisedIdentity) (nerveMap raisedIdentity)
        (NatTrans.nerveHomotopy (𝟙 raisedIdentity))
        ((TopCat.prodIsoProd TopCat.I.{1}
          (SSet.toTop.obj (nerve RaisedSource))).inv
          (t, SSet.realizedVertex
            (ComposableArrows.mk₀ raisedObject))) =
      (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk
          (𝟙 raisedObject))).hom t :=
  SSet.realizeHomotopyMap_nerveHomotopy_vertex_apply
    (𝟙 raisedIdentity) raisedObject t

end RaisedUniverse

#print axioms SSet.intervalConstVertex
#print axioms SSet.prodComparisonToTopInvInterval
#print axioms SSet.prodComparison_toTop_inv_constVertex_apply
#print axioms SSet.prod_lift_constVertex_prodComparisonToTopInvInterval
#print axioms CategoryTheory.NatTrans.nerveHomotopyMap_component
#print axioms SSet.realizeHomotopyMap_nerveHomotopy_vertex
#print axioms SSet.realizeHomotopyMap_nerveHomotopy_vertex_apply
#print axioms SSet.nerveMap_realizedVertex
#print axioms SSet.realizeHomotopy_nerveHomotopy_evalAt

end

end MathlibExtTest.CategoryTheory.NerveHomotopyRealizationTests
