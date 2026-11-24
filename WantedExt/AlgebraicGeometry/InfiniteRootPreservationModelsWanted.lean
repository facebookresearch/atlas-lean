/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.InfiniteRootPreservationModels

/-!
# Native stack base-change and infinite-root preservation assembly

These are ordinary source integration for the fixed original relative
pseudofunctor and its cartesian modules. The actual preservation predicate
is defined independently; the log reconstruction theorem is separate.
Source: Stacks025Y; Talpo--Vistoli arXiv:1410.1164v2, Definition5.20.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.InfiniteRootPreservationModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry
open MathlibExt.AlgebraicGeometry.InfiniteRootSectionModels
open MathlibExt.AlgebraicGeometry.InfiniteRootPreservationModels

public theorem_wanted nativeRelativeStackBaseChanges (S : Scheme.{0}) (R : Stack S) :
  HasBaseChanges R

public def_wanted nativeBaseChangedArrow (S : Scheme.{0}) (X Y : Stack S)
    [HasBaseChanges X] [HasBaseChanges Y] (f : StackHom X Y)
    (T : Scheme.{0}) (b : T ⟶ S) : BaseChangedMap f b

public theorem_wanted nativeBaseChangedTensor (S : Scheme.{0}) (R : Stack S)
    [HasBaseChanges R] (T : Scheme.{0}) (b : T ⟶ S) :
    HasTensorLanding (baseChanged R b)

end WantedExt.AlgebraicGeometry.InfiniteRootPreservationModels
