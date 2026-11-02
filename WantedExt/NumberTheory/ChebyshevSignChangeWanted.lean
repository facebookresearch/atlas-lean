/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hardy–Littlewood sign-change for the prime race mod 4

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ChebyshevSignChange` — chebyshev_sign_change (manifest `manifests/problems/chebyshev_sign_change.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ChebyshevSignChangeWanted` namespace. Mathematical
statements are unchanged. Source: G.H. Hardy and J.E. Littlewood, 'Contributions to the theory of the Riemann zeta-function and the theory of the distribution of primes', Acta Math. 41 (1916) 119–196 (announced 1914). Chebyshev's original observation: P. Chebyshev, letter to M. Fuss, 1853, in *Œuvres de P.L. Tchebychef*, vol. I (Saint Petersburg, 1899). Listed as §106 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PrimeCounting.ResidueClass
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.ChebyshevSignChangeWanted
namespace NumberTheory
namespace ChebyshevSignChangeProblem

/-!
# Hardy–Littlewood sign-change for the prime race mod 4

The difference `π₃(n) − π₁(n)` between the number of primes `≤ n` in
residue class `3 mod 4` and in residue class `1 mod 4` changes sign
infinitely often: both `{n : π₃(n) > π₁(n)}` and
`{n : π₁(n) > π₃(n)}` are infinite. Hardy–Littlewood 1914
(unconditional). §106 in Knill's *Some Fundamental Theorems in
Mathematics* (boxed under "strong law of small numbers"; the named
unconditional content is this Hardy–Littlewood sign-change theorem).

Chebyshev observed (1853) that `π₃` is "usually" ahead of `π₁` — the
**Chebyshev bias** — but Hardy–Littlewood showed unconditionally that
`π₁` overtakes infinitely often.
-/

open Filter

/- The number of primes `p ≤ n` in the residue class `a mod 4`. -/

/-- **The set where primes $\equiv 3 \pmod 4$ lead.** This is the set of natural numbers $n$
for which the number of primes $p \le n$ with $p \equiv 3 \pmod 4$ is strictly greater than the
number of primes $p \le n$ with $p \equiv 1 \pmod 4$. -/
def chebyshevLead : Set ℕ :=
  {n : ℕ | Nat.primeCountingMod n 4 1 < Nat.primeCountingMod n 4 3}

/- **Hardy–Littlewood sign-change for the prime race mod 4**
(Hardy–Littlewood 1914, unconditional). The difference `π₃(n) − π₁(n)`
changes sign infinitely often: both
`{n : π₃(n) > π₁(n)}` and `{n : π₁(n) > π₃(n)}` are infinite. -/
/-- **Hardy–Littlewood sign changes in the prime race modulo 4.** There are infinitely many
natural numbers $n$ for which the primes $p \le n$ with $p \equiv 3 \pmod 4$ strictly outnumber
the primes $p \le n$ with $p \equiv 1 \pmod 4$, and infinitely many natural numbers $n$ for which
the primes $p \le n$ with $p \equiv 1 \pmod 4$ strictly outnumber the primes $p \le n$ with
$p \equiv 3 \pmod 4$.

Source: G.H. Hardy and J.E. Littlewood, 'Contributions to the theory of the Riemann zeta-function and the theory of the distribution of primes', Acta Math. 41 (1916) 119–196 (announced 1914). Chebyshev's original observation: P. Chebyshev, letter to M. Fuss, 1853, in *Œuvres de P.L. Tchebychef*, vol. I (Saint Petersburg, 1899). Listed as §106 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `chebyshev_sign_change`. -/
public theorem_wanted chebyshev_sign_change :
    chebyshevLead.Infinite ∧
    {n : ℕ | Nat.primeCountingMod n 4 3 < Nat.primeCountingMod n 4 1}.Infinite

end ChebyshevSignChangeProblem
end NumberTheory

end MathlibExt.NumberTheory.ChebyshevSignChangeWanted
