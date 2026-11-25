/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeStackImageModels

/-!
# Native fibred-stack base composition

The target compares the entire original Grothendieck category and its
exact composed scheme-base functor. It supplies no independent root or
topos comparison. Source: Stacks025Y; Talpo--Vistoli1410.1164v2 Section6.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeStackImageModels

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open MathlibExt.AlgebraicGeometry.RelativeStackImageModels

public def_wanted nativeRelativeStackImage (X Y : Scheme.{0}) (f : Y ⟶ X) (R : Stack Y) :
  ImageModel f R

end WantedExt.AlgebraicGeometry.RelativeStackImageModels
