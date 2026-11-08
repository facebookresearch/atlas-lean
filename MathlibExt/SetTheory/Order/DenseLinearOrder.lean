/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.Order.Defs.Unbundled

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 20

namespace MetaMathlibExt

-- Logic 20: Dense linear order without endpoints

/-- A relation R on a set S is a *dense linear order without endpoints* if it is irreflexive,
transitive, and trichotomous (a strict linear order), dense (R(a,b) ⇒ ∃ c, R(a,c) ∧ R(c,b)), and has
neither a least nor a greatest element (∀ a ∃ b, R(b,a) and ∀ a ∃ b, R(a,b)).
-/
def IsDenseLinearOrderWithoutEndpoints {α : Type*} (r : α → α → Prop) : Prop :=
   IsStrictTotalOrder α r ∧
   (∀ a b, r a b → ∃ c, r a c ∧ r c b) ∧
   (∀ a, ∃ b, r b a) ∧
   (∀ a, ∃ b, r a b)

end MetaMathlibExt

end
