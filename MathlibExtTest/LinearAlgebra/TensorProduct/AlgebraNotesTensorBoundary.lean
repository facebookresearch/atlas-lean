/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

set_option autoImplicit false

/-!
# AlgebraNotes canonical API reuse tests

Canonical tensor balancing and generation, including the zero-length boundary.
These are algebraic tensor checks, not a geometric Dehn-invariant development.
-/

namespace AlgebraNotesApiProbe

private theorem torsion_annihilates_tensor (p : ℝ) (a : AddCircle p) (x : ℝ) (n : ℤ)
    (ha : n • a = 0) :
    TensorProduct.tmul ℤ (n • x) a = (0 : TensorProduct ℤ ℝ (AddCircle p)) := by
  calc
    TensorProduct.tmul ℤ (n • x) a = n • (TensorProduct.tmul ℤ x a) :=
      (TensorProduct.smul_tmul' n x a).symm
    _ = TensorProduct.tmul ℤ x (n • a) := (TensorProduct.tmul_smul n x a).symm
    _ = 0 := by rw [ha, TensorProduct.tmul_zero]

private theorem all_pure_tensors_generate (G H : Type*) [AddCommGroup G] [AddCommGroup H] :
    Submodule.map₂ (TensorProduct.mk ℤ G H) ⊤ ⊤ = ⊤ :=
  TensorProduct.map₂_mk_top_top_eq_top ℤ G H

-- Zero length refutes a universal nonzero-tensor claim without any geometric assumptions.
example (p : ℝ) (a : AddCircle p) :
    TensorProduct.tmul ℤ (0 : ℝ) a = (0 : TensorProduct ℤ ℝ (AddCircle p)) :=
  TensorProduct.zero_tmul ℝ a

#print axioms torsion_annihilates_tensor
#print axioms all_pure_tensors_generate

end AlgebraNotesApiProbe
