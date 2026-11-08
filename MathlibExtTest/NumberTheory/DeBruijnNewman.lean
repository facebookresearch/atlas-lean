/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DeBruijnNewman

@[expose] public section

namespace MathlibExtTest.DeBruijnNewman

open MathlibExt.NumberTheory.DeBruijnNewman

/-- The kernel series converges absolutely at every real argument,
including the boundary values used by the integral. -/
example (u : ℝ) : Summable (phiTerm u) := summable_phiTerm u

example : Summable (phiTerm 0) := summable_phiTerm 0

/-- `phi` is the sum of its defining series by definition. -/
example (u : ℝ) : phi u = ∑' n : ℕ, phiTerm u n := rfl

/-- The zero-reality predicate unfolds to its defining condition. -/
example (lam : ℝ) :
    ZerosAllReal lam ↔ ∀ z : ℂ, H lam z = 0 → z.im = 0 :=
  Iff.rfl

end MathlibExtTest.DeBruijnNewman
