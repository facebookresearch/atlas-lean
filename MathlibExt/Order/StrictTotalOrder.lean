/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Defs.Unbundled

/-! # Strict total orders

Shared bundle for strict preferences, used by matching and social-choice developments.
-/

@[expose] public section

namespace MathlibExt.Order

/-- **Strict total order.** A strict total order on a type $\alpha$ consists of a binary
relation $<$ on $\alpha$ that is irreflexive (no $a < a$), transitive ($a < b$ and $b < c$
imply $a < c$) and total on distinct elements (if $a \ne b$, then $a < b$ or $b < a$). It
models strict preference. -/
structure StrictTotalOrder (α : Type*) where
  lt : α → α → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ {a b c}, lt a b → lt b c → lt a c
  total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a

/-- The relation of a `StrictTotalOrder` is a strict total order in Mathlib's unbundled sense, so
generic strict-order lemmas apply to `T.lt`. -/
instance StrictTotalOrder.isStrictTotalOrder {α : Type*} (T : StrictTotalOrder α) :
    IsStrictTotalOrder α T.lt where
  irrefl := T.irrefl
  trans _ _ _ := T.trans
  trichotomous := fun _ _ hab hba =>
    Classical.byContradiction fun h => (T.total h).elim hab hba

/-- **Strict total orders are determined by their relation.** Two strict total orders on a
type $\alpha$ with the same relation are equal. -/
@[ext]
theorem StrictTotalOrder.ext {α : Type*} {T T' : StrictTotalOrder α} (h : T.lt = T'.lt) :
    T = T' := by
  cases T
  cases T'
  cases h
  rfl

end MathlibExt.Order
