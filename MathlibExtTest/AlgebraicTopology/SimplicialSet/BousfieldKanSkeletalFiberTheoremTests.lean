/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSkeletalFiberTheorem

open CategoryTheory HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u}) (n : ℕ) :
    Fibration (SSet.bkNativeCellInteriorProjection D n) :=
  SSet.bkNativeCellInteriorProjection_fibration D n

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u}) (n : ℕ) :
    Fibration (SSet.bkSkeletalInteriorProjection D n) :=
  SSet.bkSkeletalInteriorProjection_fibration D n

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u})
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (SSet.toTop.map (D.map g)))
    (n : ℕ) (b : SSet.toTop.obj ((nerve J).skeleton (n + 1) : SSet.{u})) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (SSet.toTop.map (SSet.bkSkeletalProjection D n)) b) :=
  SSet.bkSkeletalProjection_strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences D hD n b

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u})
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (SSet.toTop.map (D.map g)))
    (b : SSet.toTop.obj (nerve J)) :
    TopCat.weakHomotopyEquivalences (TopCat.strictFiberToHomotopyFiber
      (SSet.toTop.map (SSet.bkHocolimToNerve D)) b) :=
  SSet.bkHocolimToNerve_strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences D hD b

example {J : Type u} [Category.{0} J] (D : J ⥤ SSet.{u})
    (hD : ∀ (j k : J) (g : j ⟶ k), TopCat.weakHomotopyEquivalences (SSet.toTop.map (D.map g)))
    (j : J) : TopCat.weakHomotopyEquivalences (SSet.bkPointFiberComparison D j) :=
  SSet.bkPointFiberComparison_mem_weakHomotopyEquivalences D hD j
