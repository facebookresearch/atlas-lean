/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Guy A7b: Shanks chains of length 7
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.GuyProblemA7bWanted

/-! Source record `GUY-A7b`. -/

namespace GPA7b

/-!
# Clause inventory for [GUY-A7b]

- Quantifier domain: `p : Fin 7 → ℕ`, exactly seven terms.
- Hypothesis: every term is prime.
- Hypothesis: recurrence `p_{i+1} = 4 * p_i^2 - 17` over `ℤ`.
- Question: existence of such a 7-tuple.
-/

/-- Shanks chain of length 7 with `p_{i+1} = 4 * p_i^2 - 17` [GUY-A7b]. -/
def IsShanksChainLength7 (p : Fin 7 → ℕ) : Prop :=
  (∀ i, Nat.Prime (p i)) ∧
    ∀ i : Fin 6, (p i.succ : ℤ) = 4 * (p (Fin.castSucc i) : ℤ) ^ 2 - 17

/-- Existence of a Shanks chain of length 7 [GUY-A7b]. -/
def ShanksChainLength7Exists : Prop :=
  ∃ p : Fin 7 → ℕ, IsShanksChainLength7 p

end GPA7b

/--
Resolved true: Resolved true: P. Leyland found a Shanks (4,17) chain of length 7 starting at
176996212597 (seventh term 758 digits) and proved all seven terms prime with Morain's ECPP
(NMBRTHRY list, 22 Nov 2000; recorded in MathWorld, Shanks Chain). Source: P. Leyland, A Shanks
(4,17) chain of length 7, NMBRTHRY mailing list, 22 Nov 2000,
https://listserv.nodak.edu/cgi-bin/wa.exe?A2=NMBRTHRY;696450a6.0011; E. W. Weisstein, Shanks
Chain, MathWorld, https://mathworld.wolfram.com/ShanksChain.html. Moved from
`OpenConjectures/NumberTheory/GuyProblemA7b`.
-/
public theorem_wanted ShanksChainLength7Exists_holds : GPA7b.ShanksChainLength7Exists

end MathlibExt.NumberTheory.GuyProblemA7bWanted
