/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectKlNearPerfectWithPrimePowTwoIff
/-! # Tests for near-perfect prime powers

Concrete square witnesses and exclusions for cubes and `ell = 3` exercise the
classification of `[2,ell]`-near-perfect prime powers.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 2.
-/

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

example : KLNearPerfectWith 2 1 (2 ^ 2) 1 :=
  (klNearPerfectWith_prime_pow_two_iff 2 2 1 1 (by decide) (by decide)).mpr
    ⟨rfl, rfl, rfl⟩

example : KLNearPerfectWith 2 1 (3 ^ 2) 1 :=
  (klNearPerfectWith_prime_pow_two_iff 3 2 1 1 (by decide) (by decide)).mpr
    ⟨rfl, rfl, rfl⟩

example (p l d : ℕ) (hp : p.Prime) (hl : 1 ≤ l) :
    ¬ KLNearPerfectWith 2 l (p ^ 3) d := by
  intro h
  exact (by decide : (3 : ℕ) ≠ 2)
    ((klNearPerfectWith_prime_pow_two_iff p 3 l d hp hl).mp h).1

example (p a d : ℕ) (hp : p.Prime) : ¬ KLNearPerfectWith 2 3 (p ^ a) d := by
  intro h
  exact (by decide : (3 : ℕ) ≠ 1)
    ((klNearPerfectWith_prime_pow_two_iff p a 3 d hp (by decide)).mp h).2.1

end MathlibExtTest.NumberTheory.FkPerfect
