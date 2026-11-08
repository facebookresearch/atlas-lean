/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_length_quotient_le_of_ker_le.lean` and
`P2M/Sol/S_Module_length_quotient_le_of_ker_le.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Length of quotients factoring through a linear map

If the kernel of a linear map is contained in a submodule, the length of the
quotient by that submodule is bounded by the length of the target: factor
through the first isomorphism theorem and use monotonicity of length.
-/

@[expose] public section

/-- If `ker f ≤ K`, the length of `M ⧸ K` is at most the length of `N`. -/
theorem Module.length_quotient_le_of_ker_le {R : Type*} {M : Type*} {N : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (K : Submodule R M) (f : M →ₗ[R] N) (h : LinearMap.ker f ≤ K) :
    Module.length R (M ⧸ K) ≤ Module.length R N := by
  have h1 : Module.length R (M ⧸ K) ≤ Module.length R (M ⧸ LinearMap.ker f) :=
    Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)
  have h2 : Module.length R (M ⧸ LinearMap.ker f) = Module.length R (LinearMap.range f) :=
    (f.quotKerEquivRange).length_eq
  have h3 : Module.length R (LinearMap.range f) ≤ Module.length R N :=
    Module.length_le_of_injective (LinearMap.range f).subtype Subtype.val_injective
  exact h1.trans (h2.le.trans h3)
