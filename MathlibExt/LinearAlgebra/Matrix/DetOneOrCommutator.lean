/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one.lean`
and
`P2M/Sol/S_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one.lean`
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

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace Matrix

namespace GeneralLinearGroup

/-- Every determinant-one matrix in `GL (Fin 2) (ZMod 3)` is either the
identity or a commutator `x * y * x⁻¹ * y⁻¹`.

This is a finite check over the 48 elements of `GL (Fin 2) (ZMod 3)`:
the determinant-one subgroup has 24 elements, and each of them is
exhibited as a commutator or is the identity. -/
public theorem eq_one_or_eq_commutator_of_det_eq_one
    (g : GL (Fin 2) (ZMod 3))
    (hg : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
      ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3),
        g = x * y * x⁻¹ * y⁻¹ := by
  revert g
  decide +kernel

end GeneralLinearGroup

end Matrix
