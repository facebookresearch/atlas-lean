/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.LoopBasepointChange
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHProper
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Weak equivalences of native pointed CGWH loop maps

Native basepoint change is weak because it is a genuine continuous
homotopy equivalence. Strict loops preserve pointed weak equivalences by
the right-Quillen Ken--Brown theorem, and weakly pointed loop maps are weak
by their exact strict-map/basepoint-change/isomorphism factorization.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- Native loop basepoint change is a selected CGWH weak homotopy
equivalence. -/
theorem loopBasepointChange_mem_weakHomotopyEquivalences
    (B : CGWH.{u, v}) {x y : B} (p : Path x y) :
    CGWH.weakHomotopyEquivalences
      (PointedCGWH.loopBasepointChange B p) := by
  let phi := PointedCGWH.loopBasepointChange B p
  let e := PointedCGWH.loopBasepointChangeHomotopyEquiv B p
  have hMap : CGWH.cgwhToTop.map phi = TopCat.ofHom e.toFun := by
    apply ConcreteCategory.hom_ext
    intro gamma
    change phi gamma = e.toFun gamma
    rw [PointedCGWH.loopBasepointChangeHomotopyEquiv_toFun]
  change TopCat.weakHomotopyEquivalences
    (CGWH.cgwhToTop.map phi)
  rw [hMap]
  exact TopCat.homotopyEquiv_toFun_mem e

/-- The strict native loop functor preserves selected weak equivalences of
pointed CGWH spaces. -/
theorem loop_map_mem_weakHomotopyEquivalences
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : CGWH.weakHomotopyEquivalences f.right) :
    CGWH.weakHomotopyEquivalences
      (PointedCGWH.loop.map f).right := by
  let _ : ModelCategory PointedCGWH.{u, v} :=
    PointedCGWH.modelCategory
  let _ : WeakEquivalence f.right :=
    (HomotopicalAlgebra.weakEquivalence_iff f.right).2 hf
  let _ : WeakEquivalence f :=
    (PointedCGWH.weakEquivalence_iff f).2
      (show WeakEquivalence f.right from inferInstance)
  let _ : IsFibrant X :=
    (PointedCGWH.isFibrant_iff X).2
      (CGWH.modelCategory.allObjectsFibrant X.right)
  let _ : IsFibrant Y :=
    (PointedCGWH.isFibrant_iff Y).2
      (CGWH.modelCategory.allObjectsFibrant Y.right)
  let _ : Adjunction.IsQuillenAdjunction
      PointedCGWH.suspensionLoopAdjunction.{u, v} :=
    CGWH.modelCategory.instPointedCGWHSuspensionLoopIsQuillenAdjunction
  have hLoop : WeakEquivalence (PointedCGWH.loop.map f) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant
      (adj := PointedCGWH.suspensionLoopAdjunction.{u, v}) f
  have hRight : WeakEquivalence (PointedCGWH.loop.map f).right :=
    (PointedCGWH.weakEquivalence_iff
      (PointedCGWH.loop.map f)).1 hLoop
  exact (HomotopicalAlgebra.weakEquivalence_iff _).1 hRight

namespace WeaklyPointedMap

/-- The native loop map of a weakly pointed weak equivalence is a selected
CGWH weak homotopy equivalence. -/
theorem loopMap_mem_weakHomotopyEquivalences
    {X Y : PointedCGWH.{u, v}} (f : WeaklyPointedMap X Y)
    (hf : CGWH.weakHomotopyEquivalences f.hom) :
    CGWH.weakHomotopyEquivalences f.loopMap.hom := by
  let _ : ModelCategory CGWH.{u, v} := CGWH.modelCategory
  change weakEquivalences CGWH.{u, v} f.loopMap.hom
  change weakEquivalences CGWH.{u, v} f.hom at hf
  let P := weakEquivalences CGWH.{u, v}
  let a := (PointedCGWH.loop.map f.toPointedAt).right
  let b := PointedCGWH.loopBasepointChange Y.right f.rootPath
  let c := (PointedCGWH.loop.map
    (PointedCGWH.pointedAtBasepointIso Y).hom).right
  have hfPointedAt : P f.toPointedAt.right := by
    change P f.hom
    exact hf
  have ha : P a :=
    PointedCGWH.loop_map_mem_weakHomotopyEquivalences
      f.toPointedAt hfPointedAt
  have hb : P b :=
    PointedCGWH.loopBasepointChange_mem_weakHomotopyEquivalences
      Y.right f.rootPath
  let e := PointedCGWH.pointedAtBasepointIso Y
  let eLoop := PointedCGWH.loop.mapIso e
  let eRight := PointedCGWH.pointedToCGWH.mapIso eLoop
  have hc : P c := by
    change P eRight.hom
    exact P.of_isIso eRight.hom
  rw [PointedCGWH.WeaklyPointedMap.loopMap_factorization]
  exact P.comp_mem a (b ≫ c) ha (P.comp_mem b c hb hc)

end WeaklyPointedMap

end PointedCGWH
