/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.WeaklyPointedLoopMapWeakHomotopy

/-!
# Tests for weakly pointed loop-map weak homotopy equivalences

These clients use an arbitrary chosen root path, pin the exact strict-map
then basepoint-change factorization and composition order, and elaborate in
Type 0 and Type 1.  They guard the same-universe and non-Q/S boundaries.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped Topology

universe u v

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace WeaklyPointedLoopMapWeakHomotopyTests

section ArbitraryRootPath

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y} (g : C(X, Y)) (p : Path (g x) y)

example
    (hg : TopCat.weakHomotopyEquivalences (TopCat.ofHom g)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom
        ((ContinuousMap.WeaklyPointed.mk g p).loopMap)) :=
  ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences
    (ContinuousMap.WeaklyPointed.mk g p) hg

example :
    (ContinuousMap.WeaklyPointed.mk g p).loopMap =
      (ContinuousMap.loopBasepointChange p).comp
        (ContinuousMap.strictLoopMap g x) :=
  ContinuousMap.WeaklyPointed.loopMap_eq_loopBasepointChange_comp_strictLoopMap
    (ContinuousMap.WeaklyPointed.mk g p)

example
    (hg : TopCat.weakHomotopyEquivalences (TopCat.ofHom g)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom
        ((ContinuousMap.loopBasepointChange p).comp
          (ContinuousMap.strictLoopMap g x))) := by
  rw [TopCat.ofHom_comp]
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _
    (ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences g x hg)
    (ContinuousMap.loopBasepointChange_mem_weakHomotopyEquivalences p)

end ArbitraryRootPath

section UniverseZero

example {X Y : Type 0} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : ContinuousMap.WeaklyPointed x y)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.hom)) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap) :=
  ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences f hf

end UniverseZero

section UniverseOne

example {X Y : Type 1} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : ContinuousMap.WeaklyPointed x y)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.hom)) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap) :=
  ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences f hf

end UniverseOne

section Boundaries

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

#guard_msgs (error, substring := true) in
example (f : ContinuousMap.WeaklyPointed x y)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.hom)) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap) :=
  ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences f hf

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridToNQLoopMap_mem_weakHomotopyEquivalences

end Boundaries

#print axioms
  ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences

end WeaklyPointedLoopMapWeakHomotopyTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
