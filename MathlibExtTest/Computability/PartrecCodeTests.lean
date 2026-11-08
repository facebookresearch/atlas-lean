/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.PartrecCode

@[expose] public section

/-!
# Tests for computable families of codes
-/

set_option autoImplicit false

open MetaMathlibExt
open Nat.Partrec (Code)

namespace MathlibExtTest.Computability.PartrecCode

/-- The family of constant functions `x ↦ a` has a computable family of codes. -/
example : ∃ g : ℕ → Code, Computable g ∧ ∀ a x, (g a).eval x = Part.some a :=
  exists_computable_code (F := fun a _ ↦ Part.some a) (Computable.fst.partrec)

/-- A non-`ℕ` parameter type: the family `x ↦ p.1` indexed by pairs. -/
example : ∃ g : ℕ × ℕ → Code, Computable g ∧ ∀ p x, (g p).eval x = Part.some p.1 :=
  exists_computable_code (F := fun (p : ℕ × ℕ) (_ : ℕ) ↦ Part.some p.1)
    (Computable.fst.comp Computable.fst).partrec

end MathlibExtTest.Computability.PartrecCode
