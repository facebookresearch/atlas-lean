/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Fermat

/-!
# Fermat primes

This module formalizes the notion of a Fermat prime.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fermat prime.** A natural number $p$ is a Fermat prime if $p$ is prime and
$p = 2^{2^k} + 1$ for some natural number $k$, that is, $p$ is a prime Fermat number.

Source: concept `jis_sem_dc0cba6ecb4751a4e9031492` ("Fermat prime"), statements
`jis_0d9f8f95b9a74c9ccfec1e18` and `jis_a9e59051940d13024a23765b`. Formulated via
`Nat.fermatNumber`. -/
def IsFermatPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k : ℕ, p = Nat.fermatNumber k

end

end MetaMathlibExt
