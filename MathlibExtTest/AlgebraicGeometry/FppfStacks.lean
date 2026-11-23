/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.FppfStacks

/-! # Tests for fppf stacks in groupoids

Checks that the fibres of a stack in groupoids are groupoids by typeclass inference, and the
closure properties of fibrewise equivalences: identities, composites and two-out-of-three.
-/

namespace MathlibExtTest.AlgebraicGeometry.FppfStacks

open CategoryTheory Opposite _root_.AlgebraicGeometry _root_.AlgebraicGeometry.FppfStacks

universe u

example (X : StackInGroupoids.{u}) (T : Scheme.{u}) :
    IsGroupoid (X.toSchPseudofunctor.obj (.mk (op T))) := inferInstance

example (X : StackInGroupoids.{u}) : X.toSchPseudofunctor.IsStack Scheme.fppfTopology :=
  inferInstance

variable {X Y Z : StackInGroupoids.{u}} {f : StackInGroupoids.Hom X Y}
  {g : StackInGroupoids.Hom Y Z}

example : StackInGroupoids.Hom.IsFiberwiseEquiv
    (Pseudofunctor.StrongTrans.id X.toSchPseudofunctor) := by
  simp

example (hf : f.IsFiberwiseEquiv) (T : Scheme.{u}) :
    (f.app (.mk (op T))).toFunctor.IsEquivalence :=
  (StackInGroupoids.Hom.isFiberwiseEquiv_iff f).mp hf T

example (hf : f.IsFiberwiseEquiv) (hg : g.IsFiberwiseEquiv) :
    StackInGroupoids.Hom.IsFiberwiseEquiv (Pseudofunctor.StrongTrans.vcomp f g) :=
  hf.comp hg

example (hg : g.IsFiberwiseEquiv)
    (hfg : StackInGroupoids.Hom.IsFiberwiseEquiv (Pseudofunctor.StrongTrans.vcomp f g)) :
    f.IsFiberwiseEquiv :=
  hg.of_comp_right hfg

example (hf : f.IsFiberwiseEquiv)
    (hfg : StackInGroupoids.Hom.IsFiberwiseEquiv (Pseudofunctor.StrongTrans.vcomp f g)) :
    g.IsFiberwiseEquiv :=
  hf.of_comp_left hfg

end MathlibExtTest.AlgebraicGeometry.FppfStacks
