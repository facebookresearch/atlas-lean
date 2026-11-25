/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean`
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

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Global additive characters of the adele ring

A global additive character of the adele ring of a number field is a continuous, nontrivial
additive character with values in `ℂ` that is trivial on the diagonally embedded field. The
adelic character theory and the Whittaker coefficients both use these predicates.
-/

@[expose] public section

open NumberField

namespace AutomorphicForm

variable (F : Type*) [Field F] [NumberField F]

/-- An additive character of the adele ring is principal-invariant when it
is trivial on the diagonally embedded field. -/
public def IsPrincipalInvariantAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∀ α : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) α) = 1

/-- A global additive character of the adele ring: continuous, nontrivial,
and trivial on the diagonally embedded field. -/
public structure IsGlobalAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop where
  principalInvariant : IsPrincipalInvariantAddChar F ψ
  continuous : Continuous ψ
  nontrivial : ψ ≠ 1

public theorem isPrincipalInvariantAddChar_one :
    IsPrincipalInvariantAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun _ => rfl

public theorem not_isGlobalAddChar_one :
    ¬ IsGlobalAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun h => h.nontrivial rfl

end AutomorphicForm
