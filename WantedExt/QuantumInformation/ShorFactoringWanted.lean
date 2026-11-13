/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shor's factoring theorem — wishlist
This file records Shor's factoring theorem as a `theorem_wanted` declaration.
-/
module

import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

open scoped BigOperators

namespace MathlibExt.QuantumInformation.ShorFactoringWanted

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-- The `M`-bit least-significant-bit-first expansion of `y`, as the bit
string a computational-basis measurement outcome decodes to. -/
def shorBits (M : ℕ) (y : Fin (2 ^ M)) : List Bool :=
  (List.finRange M).map (fun k => Nat.testBit y.val k)

/-- A successful Shor output for `N`: either a nontrivial factor `d` of
`N`, or `0` together with `N` prime. -/
def IsShorOutput (N d : ℕ) : Prop :=
  (1 < d ∧ d < N ∧ d ∣ N) ∨ (d = 0 ∧ Nat.Prime N)

/-- Decidability of `IsShorOutput`, for the measurement-outcome case split in
`shor_factoring` below. -/
noncomputable instance (N d : ℕ) : Decidable (IsShorOutput N d) :=
  Classical.propDecidable _

/--
Shor's factoring theorem: there is a polynomial-time quantum algorithm that
factors integers. Precisely: there are polynomials `a` and `s`, a
polynomial-time gate generator `gates`, and a polynomial-time classical
post-processing function `post` such that, for every `N > 1`, running the
circuit `gates (Nat.bits N)` (of at most `s` gates, all well formed on the
working qubits) on the input state for `N` and measuring in the
computational basis yields, with probability at least `2 / 3`, an outcome
whose post-processed decoding is either a nontrivial factor of `N` or `0`
with `N` prime.

The input is `Nat.bits N`, the least-significant-bit-first binary expansion.
The gate model is the repo's `BQP` model: 2-local unitary gates with rational
entries, generated in polynomial time (Kitaev–Shen–Vyalyi / Arora–Barak).
The `2 / 3` is the success probability of the whole procedure, including the
standard internal repetition of order-finding; the circuit may repeat the
order-finding subroutine, which keeps its size polynomial. The classical
post-processing is the order-finding pipeline: continued fractions to recover
the order, `gcd` extraction of a factor, and a primality test (AKS). Its
`gcd` step is proved in this repo as `Cslib.Shor.gcd_factor_of_order` in
`CSLibExt/Algorithms/Quantum/Shor/OrderToFactor.lean`. The prevalence of
units satisfying that step's hypotheses is proved here only for `N = p * q`
with `p` and `q` distinct odd primes: `shor_good_units` in
`MathlibExt/Quantum/ShorGoodUnits.lean` shows that at least half of the units
modulo such an `N` have even order `r` and `a ^ (r / 2) ≠ -1`. The matching
bound for the other odd `N` with at least two distinct prime factors (three or
more distinct primes, or a repeated prime factor) is not formalized in this
repo. Even `N` and odd prime powers, including odd primes, need no such bound
and may have no good units at all (for an odd prime power the unit group is
cyclic, so `a ^ (r / 2) = -1` whenever `r` is even); the standard algorithm
settles them classically before order finding, with a parity check, a
perfect-power test, and the primality test.

Source: P. W. Shor, Polynomial-time algorithms for prime factorization and
discrete logarithms on a quantum computer, SIAM J. Comput. 26 (1997),
1484–1509, Section 5; M. A. Nielsen and I. L. Chuang, Quantum Computation and
Quantum Information, Cambridge University Press, 2000, Section 5.3.
-/
public theorem_wanted shor_factoring :
    ∃ a s : Polynomial ℕ,
      ∃ gates : List Bool → List QGate,
        ∃ post : List Bool → List Bool,
          IsPolyTime gates ∧ IsPolyTime post ∧
          (∀ x, (gates x).length ≤ s.eval x.length) ∧
          (∀ x, ∀ g ∈ gates x, QGateWellFormed (x.length + a.eval x.length) g) ∧
          ∀ N : ℕ, 1 < N →
            let M := (Nat.bits N).length + a.eval (Nat.bits N).length
            let ψ := applyCircuit M (gates (Nat.bits N))
              (bqpInitState (Nat.bits N) (a.eval (Nat.bits N).length))
            (2 : ℝ) / 3 ≤ ∑ y : Fin (2 ^ M),
              if IsShorOutput N (qNumOf (post (shorBits M y)))
              then (starRingEnd ℂ (ψ y) * ψ y).re else 0

end MathlibExt.QuantumInformation.ShorFactoringWanted
