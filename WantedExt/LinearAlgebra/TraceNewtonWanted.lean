/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Trace Cayley-Hamilton / Newton identity

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.LinearAlgebra.TraceNewton` — trace_cayley_hamilton_newton (manifest `manifests/problems/trace_cayley_hamilton_newton.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.LinearAlgebra.TraceNewtonWanted` namespace. Mathematical
statements are unchanged. Source: Knill, *Some fundamental theorems in mathematics*, §220.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.LinearAlgebra.TraceNewtonWanted
namespace LinearAlgebra.TraceNewton

/-!
# Trace Cayley-Hamilton / Newton identity

`trace_cayley_hamilton_newton`: the Newton trace recurrence for the
coefficients of the characteristic polynomial,
`k cₖ + ∑_{j=1}^k tr(Aʲ) c_{k-j} = 0`, where `χ_A(X) = Xᴺ + c₁ Xᴺ⁻¹ + ⋯ + c_N`.
Trusted helper `charpolyDescendingCoeff` (non-hole). Category-(b) candidate from
§220 of the Knill survey.
-/

open Matrix Polynomial
open scoped BigOperators Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Characteristic-polynomial coefficients in descending order.** Let $A$ be a square matrix
over a commutative ring $R$ whose rows and columns are indexed by a finite set of size $N$, and
write its characteristic polynomial as $\chi_A(X) = \det(X I - A) = X^N + c_1 X^{N-1} + \dots +
c_N$. For a natural number $k$, the descending coefficient $c_k$ of $A$ is the coefficient of
$X^{N-k}$ in $\chi_A$ when $k \le N$, and $0$ when $k > N$.

Setting $c_k = 0$ for $k > N$ lets the trace recurrence be stated uniformly for all positive $k$. -/
noncomputable def charpolyDescendingCoeff {R : Type*} [CommRing R]
    (A : Matrix n n R) (k : ℕ) : R :=
  if k ≤ Fintype.card n then
    Polynomial.coeff A.charpoly (Fintype.card n - k)
  else
    0

/- The trace Cayley-Hamilton / Newton identity:
`k c_k + ∑_{j=1}^k tr(A^j) c_{k-j} = 0`, where
`χ_A(X) = X^N + c₁ X^(N-1) + ... + c_N`.

For `k > N`, `c_k = 0`, and the remaining relation is the trace of
Cayley-Hamilton multiplied by a power of `A`. -/
/-- **Newton's trace identities for the characteristic polynomial.** Let $A$ be a square matrix
over a commutative ring $R$ whose rows and columns are indexed by a finite set of size $N$. For
each natural number $k$, let $c_k$ be the coefficient of $X^{N-k}$ in the characteristic
polynomial $\chi_A(X) = \det(X I - A)$ when $k \le N$, and $c_k = 0$ when $k > N$, so that
$\chi_A(X) = X^N + c_1 X^{N-1} + \dots + c_N$. Then for every natural number $k \ge 1$,
$$k \, c_k + \sum_{j=1}^{k} \operatorname{tr}(A^j) \, c_{k-j} = 0,$$
where $k$ is read as an element of $R$.

Source: Knill, *Some fundamental theorems in mathematics*, §220. Via leanprover/lean-eval@38361be, problem `trace_cayley_hamilton_newton`. -/
public theorem_wanted trace_cayley_hamilton_newton {R : Type*} [CommRing R]
    (A : Matrix n n R) {k : ℕ} (hk : 1 ≤ k) :
    (k : R) * charpolyDescendingCoeff A k +
        ∑ j ∈ Finset.Icc 1 k,
          trace (A ^ j) * charpolyDescendingCoeff A (k - j) = 0

end LinearAlgebra.TraceNewton

end MathlibExt.LinearAlgebra.TraceNewtonWanted
