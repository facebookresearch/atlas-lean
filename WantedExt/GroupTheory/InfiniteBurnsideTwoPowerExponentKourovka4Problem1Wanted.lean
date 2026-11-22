/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite finitely generated groups of exponent 2ⁿ (Kourovka Notebook Problem 4.1)

Kourovka Notebook, Archive of Solved Problems, Problem 4.1 (S. I. Adian): find an infinite finitely
generated group with an identical relation of the form `x^(2^n) = 1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

namespace MathlibExt.GroupTheory.InfiniteBurnsideTwoPowerExponentKourovka4Problem1Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.1 (S. I.
Adian). UnsolvedMath record UM-00700212 (`KOU-4.1`), dataset ulamai/UnsolvedMath v1.8.0.

"Find" is read as existence: some `n` and some infinite finitely generated group satisfying `g^(2^n)
= 1` for all `g`. The existing `BurnsideCounterexampleWanted` entry asserts an infinite finitely
generated group of some exponent, not necessarily a power of `2`.
-/

/-- Kourovka 4.1 (S. I. Adian): there is an infinite finitely generated group satisfying an
identity `x^(2^n) = 1` for some `n`. -/
def existsInfiniteFGGroupTwoPowerExponent : Prop :=
  ∃ (n : ℕ) (G : Type) (_ : Group G), Group.FG G ∧ Infinite G ∧ ∀ g : G, g ^ (2 ^ n) = 1

/--
Resolved true: Ivanov and Lysenok proved that the free Burnside groups `B(m, 2^k)`, `m ≥ 2`, are
infinite for large `k`; the Kourovka Archive answers 4.1 "It has been found". Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.1 (S. I. Adian); resolution: S. V.
Ivanov, The free Burnside groups of sufficiently large exponents, Int. J. Algebra Comput. 4 (1994),
no. 1-2, 1-308; I. G. Lysenok, Infinite Burnside groups of even exponent, Izv. Math. 60 (1996), no.
3, 453-654, Ivanov, abstract: construction of the free Burnside groups `B(m, n)`, `m > 1`, `n ≥
2^48` odd or divisible by `2^9`, solving the Burnside problem in the negative for these exponents
(so `B(2, 2^k)` is infinite for `k ≥ 48`); Lysenok, abstract: a negative solution to the Burnside
problem for exponents `n = 16k ≥ 8000`; Kourovka Archive of Solved Problems, Problem 4.1: It has
been found, https://doi.org/10.1142/S0218196794000026.
-/
public theorem_wanted existsInfiniteFGGroupTwoPowerExponent_holds :
    existsInfiniteFGGroupTwoPowerExponent

end MathlibExt.GroupTheory.InfiniteBurnsideTwoPowerExponentKourovka4Problem1Wanted
