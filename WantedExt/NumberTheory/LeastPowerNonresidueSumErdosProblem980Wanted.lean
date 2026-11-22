/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The sum of least k-th power non-residues (Erdős Problem 980)

Erdős Problem 980: let `k ≥ 2` and `n_k(p)` denote the least `k`-th power nonresidue of `p`. Is it
true that `∑_{p < x} n_k(p) ∼ c_k x / log x` for some constant `c_k > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MathlibExt.NumberTheory.LeastPowerNonresidueSumErdosProblem980Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #980, https://www.erdosproblems.com/980 (status
PROVED). UnsolvedMath record UM-30007107 (`EP-980`), dataset ulamai/UnsolvedMath v1.8.0.

`n_k(p)` is the least positive integer that is not a `k`-th power in `ZMod p`. A `k`-th power
non-residue modulo `p` exists only when `gcd(k, p - 1) > 1`; as in Elliott's theorem as Martin and
Pollack state it (and in the formal-conjectures statement), the sum runs over the primes `p < x`
with `p ≡ 1 (mod k)`. For composite `k` this omits the primes `p ≢ 1 (mod k)` with `gcd(k, p - 1) >
1`, which have `k`-th power non-residues too (for `k = 4`, the primes `p ≡ 3 (mod 4)`); for prime
`k` the two ranges agree. `∼` is `Asymptotics.IsEquivalent` as `x → ∞` through `ℕ`. Compared with
the formal-conjectures statement `ErdosProblems/980.lean` (`erdos_980`, equivalent; no code
imported).
-/

open Asymptotics Filter

/-- `n_k(p)`: the least positive integer that is not a `k`-th power modulo `p` (`0` if every
residue is a `k`-th power, which does not happen for `p ≡ 1 (mod k)`, `k ≥ 2`). -/
noncomputable def leastPowerNonresidue (k p : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ x : ZMod p, x ^ k ≠ (m : ZMod p)}

/-- Erdős Problem 980: for every `k ≥ 2` there is `c_k > 0` with
`∑_{p < x, p ≡ 1 (mod k)} n_k(p) ~ c_k x / log x`, the sum over primes. -/
def leastPowerNonresidueSumAsymptotic : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
    (fun x : ℕ => ∑ p ∈ (Nat.primesBelow x).filter (fun p => p % k = 1),
        (leastPowerNonresidue k p : ℝ)) ~[atTop] fun x => c * x / Real.log x

/--
Resolved true: erdosproblems.com/980 records that Erdős proved the case `k = 2` and that the general
case was proved by Elliott. The sum runs over the primes `p ≡ 1 (mod k)`, the primes over which
Martin and Pollack state Elliott's theorem (a finite mean value of the least `k`-th power
non-residue, quoted below). Source: T. F. Bloom, Erdős Problems, Problem #980,
https://www.erdosproblems.com/980 (status PROVED); resolution: P. D. T. A. Elliott, A problem of
Erdős concerning power residue sums, Acta Arith. 13 (1967/68), 131-149, erdosproblems.com/980: Erdős
proved the case k = 2 and 'The general case was proved by Elliott'; K. Martin and P. Pollack, The
average least character non-residue and further variations on a theme of Erdős, arXiv:1112.1175,
Section 1: 'For a prime p ≡ 1 (mod 3), define n3(p) as the least cubic nonresidue modulo p. Elliott
[Ell68] showed that n3(p) possesses a finite mean-value. (In fact, he showed the analogous result
for kth power nonresidues, for all k.)', https://arxiv.org/abs/1112.1175.
-/
public theorem_wanted leastPowerNonresidueSumAsymptotic_holds : leastPowerNonresidueSumAsymptotic

end MathlibExt.NumberTheory.LeastPowerNonresidueSumErdosProblem980Wanted
