/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sturm's theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Algebra.Sturm` — sturm (manifest `manifests/problems/sturm.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Algebra.SturmWanted` namespace. Mathematical
statements are unchanged. Source: J. C. F. Sturm (1829). Listed as §97 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Formalized in Isabelle/HOL by Manuel Eberl (AFP entry Sturm_Sequences).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Algebra.SturmWanted
namespace Algebra

/-!
# Sturm's theorem

§97 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. For a
squarefree real polynomial `p` and an interval `(a, b)` whose endpoints are
not roots of `p`, the number of distinct roots of `p` in `(a, b)` equals the
drop in the number of sign variations of the Sturm chain across `[a, b]`.

mathlib has no Sturm chain, no sign-variation counter, and no Sturm's
theorem. The chain, the sign-change counter, and the variation function are
defined here. (Sturm's theorem is formalized in Isabelle/HOL — Manuel
Eberl's AFP entry `Sturm_Sequences` — for the same distinct-root form.)

The Sturm chain uses the negated-remainder convention `pₖ₊₁ = -(pₖ₋₁ mod pₖ)`,
for which the count is the difference `σ(a) − σ(b)`.
-/

open Polynomial
open scoped Classical

/-- **Negated-remainder sequence with fuel.** For real polynomials $a$, $b$ and a natural
number $n$, this is the list of polynomials defined recursively by: for $n = 0$ it is the
one-entry list $(a)$; for fuel $n + 1$ it is $(a)$ if $b = 0$, and otherwise it is $a$
followed by the list for the pair $b$, $-(a \bmod b)$ with fuel $n$, where $a \bmod b$ is the
remainder of $a$ on division by $b$. -/
noncomputable def sturmAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | a, _, 0       => [a]
  | a, b, (n + 1) =>
    if b = 0 then [a] else a :: sturmAux b (-(a % b)) n

/-- **Sturm chain.** The Sturm chain of a real polynomial $p$ is the list $p_0, p_1, \dots, p_m$
with $p_0 = p$, $p_1 = p'$ and $p_{k+1} = -(p_{k-1} \bmod p_k)$, the negated remainder of
$p_{k-1}$ on division by $p_k$, where the list stops at $p_m$ as soon as the next entry would
be $0$; thus $p_m$ is its last entry and, for $p \ne 0$, every entry is nonzero. For $p = 0$
the chain is the one-entry list $(0)$. -/
noncomputable def sturmChain (p : ℝ[X]) : List ℝ[X] :=
  sturmAux p (derivative p) (p.natDegree + 2)

/-- Number of sign changes in a list of real numbers, ignoring zeros: filter
the zeros out, then count adjacent pairs of opposite sign. -/
noncomputable def signChanges (xs : List ℝ) : ℕ :=
  let ys := xs.filter (· ≠ 0)
  ((ys.zip ys.tail).filter (fun q => q.1 * q.2 < 0)).length

/-- **Sturm sign-variation function.** For a real polynomial $p$ with Sturm chain
$p_0, p_1, \dots, p_m$ and a real number $x$, $\sigma_p(x)$ is the number of sign changes,
ignoring zeros, in the sequence of values $p_0(x), p_1(x), \dots, p_m(x)$. -/
noncomputable def sigma (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChanges ((sturmChain p).map fun q => q.eval x)

/- **Sturm's theorem.** For a squarefree real polynomial `p` and an interval
`(a, b)` with `a < b` whose endpoints are not roots of `p`, the number of
distinct roots of `p` in `(a, b)` equals `σ(a) − σ(b)`. -/
/-- **Sturm's theorem.** Let $p$ be a squarefree real polynomial and let $a < b$ be real numbers
with $p(a) \ne 0$ and $p(b) \ne 0$. Then the number of distinct real roots $x$ of $p$ with
$a < x < b$ equals $\sigma_p(a) - \sigma_p(b)$, where $\sigma_p$ is the Sturm sign-variation
function of $p$ and the subtraction is truncated subtraction of natural numbers.

Source: J. C. F. Sturm (1829). Listed as §97 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Formalized in Isabelle/HOL by Manuel Eberl (AFP entry Sturm_Sequences). Via leanprover/lean-eval@38361be, problem `sturm`. -/
public theorem_wanted sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b

end Algebra

end MathlibExt.Algebra.SturmWanted
