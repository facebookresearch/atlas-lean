/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.MazurAdmissible

@[expose] public section

open MazurAdmissible

/-- Consumer with the original binders: an admissible chain for a prime
`q` in a finite additive commutative group has ambient cardinality
`q ^ filtLength`. -/
example {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : Nat.card M = q ^ filtLength c :=
  c.natCard_eq_pow_filtLength hq

/-- Higher-universe consumer: the same statement in `Type 1`. -/
example {M : Type 1} [AddCommGroup M] {q : ℕ} (hq : q.Prime)
    {Φ : OpenAction M} (c : AdmissibleChain q Φ) :
    Nat.card M = q ^ filtLength c :=
  c.natCard_eq_pow_filtLength hq

/-- `filtLength` is the indexed length `n` of the chain. -/
example {M : Type*} [AddCommGroup M] {q : ℕ} {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : filtLength c = c.n :=
  rfl
