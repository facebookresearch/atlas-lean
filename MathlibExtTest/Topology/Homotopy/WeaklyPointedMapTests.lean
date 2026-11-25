/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.Topology.Homotopy.WeaklyPointedMap

/-!
# Tests for weakly pointed maps and product loop spaces

These tests pin mixed-universe elaboration, a genuinely non-reflexive root
path, the conjugation formula, identity/composition homotopies, and all public
product-loop formulas.  They also guard the deliberate absence of a weak-
equivalence theorem from this carrier-and-continuity layer.
-/

noncomputable section

open unitInterval

universe u v w u' v'

namespace MathlibExtTest.Topology.Homotopy.WeaklyPointedMapTests

section Generic

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

example (f : C(X, Y)) (p : Path (f x) y) :
    ContinuousMap.WeaklyPointed x y :=
  ⟨f, p⟩

example (f : ContinuousMap.WeaklyPointed x y) :
    C(LoopSpace X x, LoopSpace Y y) :=
  f.loopMap

example (f : ContinuousMap.WeaklyPointed x y) :
    Continuous f.loopMap :=
  f.loopMap.continuous

example (f : ContinuousMap.WeaklyPointed x y)
    (gamma : LoopSpace X x) :
    f.loopMap gamma =
      f.rootPath.symm.trans
        ((gamma.map f.hom.continuous).trans f.rootPath) :=
  f.loopMap_apply gamma

example (gamma : LoopSpace X x) :
    ((ContinuousMap.WeaklyPointed.id x).loopMap gamma).Homotopic gamma :=
  ContinuousMap.WeaklyPointed.loopMap_id_homotopic x gamma

example (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed y z)
    (gamma : LoopSpace X x) :
    ((f.comp g).loopMap gamma).Homotopic
      (g.loopMap (f.loopMap gamma)) :=
  ContinuousMap.WeaklyPointed.loopMap_comp_homotopic f g gamma

example (f : ContinuousMap.WeaklyPointed x y)
    (g : ContinuousMap.WeaklyPointed y z) :
    (f.comp g).rootPath =
      (f.rootPath.map g.hom.continuous).trans g.rootPath :=
  rfl

end Generic

section NontrivialRoot

/-- A weakly pointed constant map whose chosen root genuinely runs from zero
to one. -/
noncomputable def intervalRoot :
    ContinuousMap.WeaklyPointed (X := PUnit.{1}) (Y := unitInterval)
      (PUnit.unit : PUnit.{1}) (1 : unitInterval) where
  hom := ContinuousMap.const PUnit.{1} (0 : unitInterval)
  rootPath := Path.id

example : intervalRoot.rootPath 0 = (0 : unitInterval) :=
  Path.source intervalRoot.rootPath

example : intervalRoot.rootPath 1 = (1 : unitInterval) :=
  Path.target intervalRoot.rootPath

example (gamma : LoopSpace PUnit.{1} (PUnit.unit : PUnit.{1})) :
    intervalRoot.loopMap gamma =
      Path.id.symm.trans
        ((gamma.map intervalRoot.hom.continuous).trans Path.id) :=
  rfl

example (gamma : LoopSpace PUnit.{1} (PUnit.unit : PUnit.{1})) :
    intervalRoot.loopMap gamma 0 = (1 : unitInterval) :=
  Path.source (intervalRoot.loopMap gamma)

example (gamma : LoopSpace PUnit.{1} (PUnit.unit : PUnit.{1})) :
    intervalRoot.loopMap gamma 1 = (1 : unitInterval) :=
  Path.target (intervalRoot.loopMap gamma)

end NontrivialRoot

section Product

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (x : X) (y : Y)

example :
    LoopSpace (X × Y) (x, y) ≃ₜ
      LoopSpace X x × LoopSpace Y y :=
  loopSpaceProdHomeomorph x y

example (gamma : LoopSpace (X × Y) (x, y)) :
    (loopSpaceProdHomeomorph x y gamma).1 = gamma.map continuous_fst :=
  loopSpaceProdHomeomorph_apply_fst x y gamma

example (gamma : LoopSpace (X × Y) (x, y)) :
    (loopSpaceProdHomeomorph x y gamma).2 = gamma.map continuous_snd :=
  loopSpaceProdHomeomorph_apply_snd x y gamma

example (gamma : LoopSpace X x × LoopSpace Y y) :
    (loopSpaceProdHomeomorph x y).symm gamma =
      gamma.1.prod gamma.2 :=
  loopSpaceProdHomeomorph_symm_apply x y gamma

example :
    loopSpaceProdHomeomorph x y (Path.refl (x, y)) =
      (Path.refl x, Path.refl y) :=
  loopSpaceProdHomeomorph_refl x y

variable {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X'] [TopologicalSpace Y']

example (f : C(X, X')) (g : C(Y, Y'))
    (gamma : LoopSpace (X × Y) (x, y)) :
    loopSpaceProdHomeomorph (f x) (g y)
        (gamma.map (f.prodMap g).continuous) =
      ((loopSpaceProdHomeomorph x y gamma).1.map f.continuous,
        (loopSpaceProdHomeomorph x y gamma).2.map g.continuous) :=
  loopSpaceProdHomeomorph_naturality x y f g gamma

example (f : C(X, X')) (g : C(Y, Y'))
    (gamma : LoopSpace X x × LoopSpace Y y) :
    ((loopSpaceProdHomeomorph x y).symm gamma).map
        (f.prodMap g).continuous =
      (loopSpaceProdHomeomorph (f x) (g y)).symm
        (gamma.1.map f.continuous, gamma.2.map g.continuous) :=
  loopSpaceProdHomeomorph_symm_naturality x y f g gamma

end Product

section Negative

/-- error: Unknown constant `ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences` -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences

end Negative

#print axioms ContinuousMap.WeaklyPointed.loopMap
#print axioms ContinuousMap.WeaklyPointed.id
#print axioms ContinuousMap.WeaklyPointed.comp
#print axioms ContinuousMap.WeaklyPointed.loopMap_id_homotopic
#print axioms ContinuousMap.WeaklyPointed.loopMap_comp_homotopic
#print axioms loopSpaceProdHomeomorph
#print axioms loopSpaceProdHomeomorph_naturality
#print axioms loopSpaceProdHomeomorph_symm_naturality

end MathlibExtTest.Topology.Homotopy.WeaklyPointedMapTests
