/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBKFiberTransfer

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Simplicial unitInterval

universe u

namespace SSet

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

section PublicBoundary

example (F : C ⥤ D) (d : D)
    (hFiber : TopCat.weakHomotopyEquivalences
      (bkPointFiberComparison (rightCommaNerveDiagram F) d)) :
    TopCat.weakHomotopyEquivalences
      (rightCommaHomotopyFiberComparison F d) :=
  rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences_of_bkPointFiberComparison
    F d hFiber

example (F : C ⥤ D) (d : D) :
    TopCat.weakHomotopyEquivalences
      (rightCommaBKFiberTransport F d) :=
  rightCommaBKFiberTransport_mem_weakHomotopyEquivalences F d

example (F : C ⥤ D) (d : D) :
    ContinuousMap.Homotopy
      (bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
        rightCommaBKFiberTransport F d).hom
      (rightCommaHomotopyFiberComparison F d).hom :=
  rightCommaBKFactorizationHomotopy F d

example (F : C ⥤ D) (d : D) :
    (bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
      rightCommaBKFiberTransport F d) ≫
      TopCat.homotopyFiberToTotal _ _ =
    rightCommaHomotopyFiberComparison F d ≫
      TopCat.homotopyFiberToTotal _ _ :=
  rightCommaHomotopyFiberComparison_bkFactorization_toTotal F d

example (F : C ⥤ D) (d : D)
    (z : SSet.toTop.obj ((rightCommaNerveDiagram F).obj d)) :
    (rightCommaBKFactorizationHomotopy F d).toFun (1, z) =
      rightCommaHomotopyFiberComparison F d z :=
  (rightCommaBKFactorizationHomotopy F d).apply_one z

end PublicBoundary

end SSet

end
