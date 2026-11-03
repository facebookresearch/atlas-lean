/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications Copyright (c) 2026 Meta Platforms, Inc. and affiliates.
Modified for Atlas: generalized the arithmetic-formula leaf count to canonical first-order terms.
-/
module

public import Mathlib.ModelTheory.Syntax

/-! # Leaf counts for first-order terms

Adapted from `Formula.size` in `eth/proof/statements/NetworkStatements.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

open scoped BigOperators

namespace FirstOrder.Language.Term

universe u v w w'

/-- The number of leaves of a first-order term.

Variables and nullary function applications are leaves. A nonnullary function application has
the sum of the leaf counts of its arguments.
-/
def leafCount {L : FirstOrder.Language.{u, v}} {V : Type w} : L.Term V → Nat
  | .var _ => 1
  | .func (l := n) _ terms => if n = 0 then 1 else ∑ i, leafCount (terms i)

@[simp]
theorem leafCount_var {L : FirstOrder.Language.{u, v}} {V : Type w} (v : V) :
    (FirstOrder.Language.Term.var (L := L) v).leafCount = 1 := rfl

@[simp]
theorem leafCount_func {L : FirstOrder.Language.{u, v}} {V : Type w} {n : Nat}
    (f : L.Functions n) (terms : Fin n → L.Term V) :
    (FirstOrder.Language.Term.func f terms).leafCount =
      if n = 0 then 1 else ∑ i, (terms i).leafCount := rfl

/-- Relabeling variables does not change the number of leaves. -/
@[simp]
theorem leafCount_relabel {L : FirstOrder.Language.{u, v}} {V : Type w} {W : Type w'}
    (g : V → W)
    (t : L.Term V) : (t.relabel g).leafCount = t.leafCount := by
  induction t using FirstOrder.Language.Term.rec with
  | var => rfl
  | func _ _ ih => simp [FirstOrder.Language.Term.relabel, ih]

end FirstOrder.Language.Term
