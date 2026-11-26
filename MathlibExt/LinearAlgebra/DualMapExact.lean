/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LinearMap_exact_dualMap_of_exact.lean`
and
`P2M/Sol/S_LinearMap_exact_dualMap_of_exact.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

namespace LinearMap

/-- **Exactness of dual maps.** Dual maps reverse exactness over a field: if `f` followed by
`g` is exact, then the dual of `g` followed by the dual of `f` is exact. The spaces need not be
finite-dimensional. -/
public theorem exact_dualMap_of_exact {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup V₃] [Module K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, h]

end LinearMap
