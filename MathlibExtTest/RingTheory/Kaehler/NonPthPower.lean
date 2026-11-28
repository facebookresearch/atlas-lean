/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Kaehler.NonPthPower

@[expose] public section

-- `exactSource` consumer with the original binders.
example {k : Type*} [Field k] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    KaehlerDifferential.D (⊥ : Subfield k) k c ≠ 0 :=
  KaehlerDifferential.D_ne_zero_of_forall_pow_ne p hp c hc

-- Higher-universe consumer.
example {k : Type 1} [Field k] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    KaehlerDifferential.D (⊥ : Subfield k) k c ≠ 0 :=
  KaehlerDifferential.D_ne_zero_of_forall_pow_ne p hp c hc

-- The hypothesis cannot be dropped: a `p`-th power has zero differential
-- over the prime subfield in characteristic `p`, since `D (b ^ p)` is a
-- multiple of the characteristic.  Concretely, for `c = 0 = 0 ^ p` the
-- conclusion would assert `D 0 ≠ 0`, which is false.
example {k : Type*} [Field k] :
    ¬ (KaehlerDifferential.D (⊥ : Subfield k) k (0 : k) ≠ 0) := by
  simp
