/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.LocallyConstant
public import Mathlib.Topology.Instances.ZMod

/-- Smoke test: the constant function on `Multiplicative (ZMod 2)` is invariant
under a neighborhood of `1`. -/
example : ∃ W : Set (Multiplicative (ZMod 2)), IsOpen W ∧ (1 : Multiplicative (ZMod 2)) ∈ W ∧
    ∀ g : Multiplicative (ZMod 2), ∀ w ∈ W, (fun _ => (1 : ℤ)) (g * w) = (fun _ => (1 : ℤ)) g ∧
      (fun _ => (1 : ℤ)) (w * g) = (fun _ => (1 : ℤ)) g :=
  IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport _
    (IsLocallyConstant.const _) (HasCompactSupport.of_compactSpace _)
