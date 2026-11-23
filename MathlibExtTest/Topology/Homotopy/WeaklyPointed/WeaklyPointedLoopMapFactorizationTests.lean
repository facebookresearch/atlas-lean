/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.WeaklyPointed.WeaklyPointedLoopMapFactorization

/-!
# Tests for weakly pointed loop-map factorization

These clients pin the factor order and literal conjugation formula, mixed
universes for the factorization, and Type 0, Type 1, and symbolic-universe
elaboration of the basepoint-change weak equivalence.  They also guard that
the strict-loop and final weakly pointed preservation theorems remain absent.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open unitInterval

universe u v

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.WeaklyPointedLoopMapFactorizationTests

section Factorization

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

theorem factorization_mixed_universes
    (f : ContinuousMap.WeaklyPointed x y) :
    f.loopMap =
      (ContinuousMap.loopBasepointChange f.rootPath).comp
        (ContinuousMap.strictLoopMap f.hom x) :=
  f.loopMap_eq_loopBasepointChange_comp_strictLoopMap

example (f : ContinuousMap.WeaklyPointed x y)
    (gamma : LoopSpace X x) :
    ((ContinuousMap.loopBasepointChange f.rootPath).comp
        (ContinuousMap.strictLoopMap f.hom x)) gamma =
      f.rootPath.symm.trans
        ((gamma.map f.hom.continuous).trans f.rootPath) :=
  rfl

/-- A mixed-universe client with a genuinely non-reflexive root path. -/
noncomputable def intervalRoot :
    ContinuousMap.WeaklyPointed (X := PUnit.{1}) (Y := unitInterval)
      (PUnit.unit : PUnit.{1}) (1 : unitInterval) where
  hom := ContinuousMap.const PUnit.{1} (0 : unitInterval)
  rootPath := Path.id

example :
    intervalRoot.loopMap =
      (ContinuousMap.loopBasepointChange intervalRoot.rootPath).comp
        (ContinuousMap.strictLoopMap intervalRoot.hom PUnit.unit) :=
  intervalRoot.loopMap_eq_loopBasepointChange_comp_strictLoopMap

example (gamma : LoopSpace PUnit.{1} PUnit.unit) :
    intervalRoot.loopMap gamma =
      Path.id.symm.trans
        ((gamma.map intervalRoot.hom.continuous).trans Path.id) :=
  rfl

end Factorization

section BasepointChangeWeakEquivalence

variable {X : Type u} [TopologicalSpace X] {x y : X}

theorem basepointChange_symbolic (p : Path x y) :
    TopCat.weakHomotopyEquivalences.{u}
      (TopCat.ofHom (ContinuousMap.loopBasepointChange p)) :=
  ContinuousMap.loopBasepointChange_mem_weakHomotopyEquivalences p

theorem basepointChange_type_zero
    {X : Type 0} [TopologicalSpace X] {x y : X} (p : Path x y) :
    TopCat.weakHomotopyEquivalences.{0}
      (TopCat.ofHom (ContinuousMap.loopBasepointChange p)) :=
  ContinuousMap.loopBasepointChange_mem_weakHomotopyEquivalences p

theorem basepointChange_type_one
    {X : Type 1} [TopologicalSpace X] {x y : X} (p : Path x y) :
    TopCat.weakHomotopyEquivalences.{1}
      (TopCat.ofHom (ContinuousMap.loopBasepointChange p)) :=
  ContinuousMap.loopBasepointChange_mem_weakHomotopyEquivalences p

end BasepointChangeWeakEquivalence

section Negative

/-- error: Unknown constant `ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences` -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences

/-- error: Unknown constant `ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences` -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences

/-- error: Unknown constant `ContinuousMap.singularLoopIso` -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.singularLoopIso

end Negative

#print axioms ContinuousMap.loopBasepointChange_mem_weakHomotopyEquivalences
#print axioms ContinuousMap.WeaklyPointed.loopMap_eq_loopBasepointChange_comp_strictLoopMap
#print axioms factorization_mixed_universes
#print axioms basepointChange_symbolic
#print axioms basepointChange_type_zero
#print axioms basepointChange_type_one

end MathlibExtTest.AlgebraicTopology.ModelCategory.WeaklyPointedLoopMapFactorizationTests
