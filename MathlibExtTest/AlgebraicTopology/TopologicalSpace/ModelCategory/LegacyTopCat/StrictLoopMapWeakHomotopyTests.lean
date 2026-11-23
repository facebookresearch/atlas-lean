/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.StrictLoopMapWeakHomotopy

/-!
# Tests for strict loop-map weak homotopy equivalences

These clients pin the same-universe theorem, its singular-loop naturality
square, the required left-cancellation orientation, Type 0 and Type 1, and
the locality of the singular Kan witnesses.  They also guard the deliberate
absence of mixed-universe, weakly pointed, and Q/S conclusions.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped Simplicial Topology

universe u v

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace StrictLoopMapWeakHomotopyTests

section Generic

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (x : X)

example (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) :=
  ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences f x hf

example :
    TopCat.toSSet.map
          (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) ≫
        (SSet.singularLoopIso Y (f x)).hom =
      (SSet.singularLoopIso X x).hom ≫
        SSet.loopSpaceMap
          (x := TopCat.toSSetObj₀Equiv.symm x)
          (y := TopCat.toSSetObj₀Equiv.symm (f x))
          (TopCat.toSSet.map (TopCat.ofHom f)) (by rfl) :=
  SSet.singularLoopIso_hom_naturality f x

end Generic

section CancellationOrientation

variable {A B D : SSet.{u}} [SSet.KanComplex A]
  [SSet.KanComplex B] [SSet.KanComplex D]
variable {g : A ⟶ B} {h : B ⟶ D}

example (hh : SSet.KanComplex.W h)
    (hgh : SSet.KanComplex.W (g ≫ h)) :
    SSet.KanComplex.W g :=
  SSet.KanComplex.W.of_postcomp hh hgh

end CancellationOrientation

section UniverseZero

example {X Y : Type 0} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) :=
  ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences f x hf

end UniverseZero

section UniverseOne

example {X Y : Type 1} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) :=
  ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences f x hf

end UniverseOne

section Boundaries

variable (X : Type u) [TopologicalSpace X]

#guard_msgs (error, substring := true) in
#synth SSet.KanComplex (TopCat.toSSet.obj (TopCat.of X))

variable {Y : Type v} [TopologicalSpace Y]

#guard_msgs (error, substring := true) in
example (f : C(X, Y)) (x : X)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f)) :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (ContinuousMap.strictLoopMap f x)) :=
  ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences f x hf

#guard_msgs (error, substring := true) in
#check ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check AlgebraicKTheory.quillenStageGridToNQLoopMap_mem_weakHomotopyEquivalences

end Boundaries

#print axioms ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences

end StrictLoopMapWeakHomotopyTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
