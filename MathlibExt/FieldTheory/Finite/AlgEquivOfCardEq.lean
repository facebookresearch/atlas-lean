/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_FiniteField_nonempty_algEquiv_of_card_eq.lean`
and
`P2M/Sol/S_FiniteField_nonempty_algEquiv_of_card_eq.lean`
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
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

namespace FiniteField

/-- Two finite fields of the same cardinality are isomorphic over any
common subfield `K`.

Both fields are splitting fields over `K` of `X ^ card - X`, since every
element of a finite field satisfies that equation. This generalizes
`FiniteField.algEquivOfCardEq`, which fixes the base to `ZMod p`. -/
public theorem nonempty_algEquiv_of_card_eq (K : Type*) [Field K]
    (L₁ : Type*) [Field L₁] [Algebra K L₁] [Finite L₁]
    (L₂ : Type*) [Field L₂] [Algebra K L₂] [Finite L₂]
    (h : Nat.card L₁ = Nat.card L₂) : Nonempty (L₁ ≃ₐ[K] L₂) := by
  classical
  haveI := Fintype.ofFinite L₁
  haveI := Fintype.ofFinite L₂
  have h' : Fintype.card L₁ = Fintype.card L₂ := by
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  haveI : Polynomial.IsSplittingField K L₁
      (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) :=
    FiniteField.isSplittingField_sub L₁ K
  haveI : Polynomial.IsSplittingField K L₂
      (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) := by
    rw [h']; exact FiniteField.isSplittingField_sub L₂ K
  exact ⟨(Polynomial.IsSplittingField.algEquiv L₁
      (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).trans
    (Polynomial.IsSplittingField.algEquiv L₂
      (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).symm⟩

end FiniteField
