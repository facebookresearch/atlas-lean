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

/-- **Dense linear order without endpoints.** A relation $R$ on a type $\alpha$ is a *dense linear
order without endpoints* if it is a strict total order (irreflexive, transitive, and
trichotomous: for all $a, b$, at least one of $R(a,b)$, $a = b$, $R(b,a)$ holds), it is dense
(whenever $R(a,b)$, there is $c$ with $R(a,c)$ and $R(c,b)$), and it has no endpoints (for every
$a$ there are $b$ and $b'$ with $R(b,a)$ and $R(a,b')$).
-/
def IsDenseLinearOrderWithoutEndpoints {α : Type*} (r : α → α → Prop) : Prop :=
   IsStrictTotalOrder α r ∧
   (∀ a b, r a b → ∃ c, r a c ∧ r c b) ∧
   (∀ a, ∃ b, r b a) ∧
   (∀ a, ∃ b, r a b)

end MetaMathlibExt

end
