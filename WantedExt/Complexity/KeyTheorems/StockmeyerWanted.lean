/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Stockmeyer: approximate counting of #P functions in BPP^NP

Source:
L. J. Stockmeyer, "The complexity of approximate counting", Proceedings of the Fifteenth
Annual ACM Symposium on Theory of Computing (STOC 1983), 118-126 (journal version in
Information and Computation 1985).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Stockmeyer

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Stockmeyer: approximate counting of #P functions in BPP^NP

Every `#P` function can be approximated in `BPP^NP`: a single randomized polynomial-time
machine with an `NP` oracle takes the input, a random string, and the precision parameter
in unary (a bitstring `prec` of length `n`, so `|prec| = n`), and outputs an estimate `E`
with `f x / (1 + 1/n) ≤ E ≤ f x * (1 + 1/n)` with probability at least `2/3`. The oracle
machine is the shared `evalOracle` model with a Boolean `NP` oracle; the machine is the
`nextQ`/`final` pair, the random string has `pRand (|x| + n)` bits, and the numbers of
queries and the query cap are polynomial in `|x| + n` (the precision is unary, so
polynomial time in the input length is polynomial in `|x| + n`); a separate hard-coded
machine per precision would be nonuniform. In particular approximate counting lies in
`BPP^NP`, hence in the polynomial hierarchy.
-/

/-- **Stockmeyer: approximate counting of #P functions in BPP^NP.** For every function $f$ in
$\#P$ there are a decision problem $O$ in NP, polynomials $p_r$, $p$ and $q$ with
natural-number coefficients, and polynomial-time computable functions $\mathrm{nextQ}$ and
$\mathrm{final}$, each taking a bitstring and a list of query/answer pairs (bitstring, boolean),
with $\mathrm{nextQ}$ returning a bitstring and $\mathrm{final}$ returning a natural number,
such that the following holds. Let $x$ and $w$ be bitstrings with $n = |w| \ge 1$, where $|\cdot|$
denotes length, and put $m = |x| + n$. For a bitstring $r$ of length $p_r(m)$, let $E(r)$ be the
output of the oracle computation that chooses queries with $\mathrm{nextQ}$ and decides with
$\mathrm{final}$, run with oracle $O$, query-length cap $q(m)$ and $p(m)$ adaptive queries on
the bitstring encoding of the pair $(x, (r, w))$ from the empty history. Then
$f(x)/(1 + 1/n) \le E(r) \le f(x) \cdot (1 + 1/n)$, computed in the rationals, for at least two
thirds of the $2^{p_r(m)}$ bitstrings $r$ of length $p_r(m)$.

The bitstring $w$ gives the precision $n$ in unary; the number of random bits, the number of
queries and the query-length cap are all polynomial in $|x| + n$.

Source: L. J. Stockmeyer, "The complexity of approximate counting", Proceedings of the Fifteenth
Annual ACM Symposium on Theory of Computing (STOC 1983), 118-126 (journal version in
Information and Computation 1985). -/
public theorem_wanted stockmeyer_approximate_counting :
    ∀ f : List Bool → ℕ, f ∈ SharpP →
      ∃ O : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        O ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∃ pRand p q : Polynomial ℕ,
      ∃ nextQ : List Bool × List (List Bool × Bool) → List Bool,
      ∃ final : List Bool × List (List Bool × Bool) → ℕ,
      IsPolyTime nextQ ∧ IsPolyTime final ∧
      ∀ (x : List Bool) (prec : List Bool), 1 ≤ prec.length →
        3 * Set.ncard {r : Fin (pRand.eval (x.length + prec.length)) → Bool |
          let E := evalOracle (q.eval (x.length + prec.length)) nextQ final O
            (MetaMathlibExt.BitstringEncoding.bitEncode (x, List.ofFn r, prec))
            (p.eval (x.length + prec.length)) []
          (f x : ℚ) / (1 + 1 / (prec.length : ℚ)) ≤ (E : ℚ) ∧
            (E : ℚ) ≤ (f x : ℚ) * (1 + 1 / (prec.length : ℚ))} ≥
          2 * 2 ^ (pRand.eval (x.length + prec.length))

end MetaMathlibExt.Complexity.KeyTheorems.Stockmeyer
