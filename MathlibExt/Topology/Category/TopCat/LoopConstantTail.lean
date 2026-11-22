/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import MathlibExt.Topology.Category.TopCat.LoopReparametrization

/-!
# Appending a constant path to the whole loop space

The original compact-open loop space admits the continuous constant-tail
map. Its entire path formula is the existing standard endpoint-preserving
reparametrization, whose affine interpolation gives a continuous homotopy
to the identity on the whole loop space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology

namespace TopCat

/-- The existing interval parameter for a path followed by its constant tail. -/
def loopConstantTailParameter : C(unitInterval, unitInterval) where
  toFun t := ⟨Path.Homotopy.transReflReparamAux t, Path.Homotopy.transReflReparamAux_mem_I t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Path.Homotopy.continuous_transReflReparamAux

/-- The constant-tail parameter preserves the original zero endpoint. -/
theorem loopConstantTailParameter_zero : loopConstantTailParameter 0 = 0 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_zero

/-- The constant-tail parameter preserves the original one endpoint. -/
theorem loopConstantTailParameter_one : loopConstantTailParameter 1 = 1 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_one

/-- Reparametrize every original loop to append the constant tail. -/
def loopConstantTailMap (B : TopCat.{u}) (b : B) :
    TopCat.of (LoopSpace B b) ⟶ TopCat.of (LoopSpace B b) :=
  loopReparamMap B b loopConstantTailParameter loopConstantTailParameter.continuous
    loopConstantTailParameter_zero loopConstantTailParameter_one

/-- The actual whole path is the original loop followed by the literal constant path. -/
theorem loopConstantTailMap_apply (B : TopCat.{u}) (b : B) (gamma : LoopSpace B b) :
    loopConstantTailMap B b gamma = gamma.trans (Path.refl b) := by
  apply Path.ext
  funext t
  have h := congrArg (fun q : Path b b => q t) (Path.Homotopy.trans_refl_reparam gamma)
  exact h.symm

/-- A continuous homotopy on the entire original loop space removes the constant tail. -/
def loopConstantTailHomotopy (B : TopCat.{u}) (b : B) :
    ContinuousMap.Homotopy (loopConstantTailMap B b).hom (ContinuousMap.id (LoopSpace B b)) :=
  loopReparamHomotopy B b loopConstantTailParameter loopConstantTailParameter.continuous
    loopConstantTailParameter_zero loopConstantTailParameter_one

end TopCat
