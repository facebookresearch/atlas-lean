/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The alternating sign matrix theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.AlternatingSignMatrix` — alternating_sign_matrix_count (manifest `manifests/problems/alternating_sign_matrix_count.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.AlternatingSignMatrixWanted` namespace. Mathematical
statements are unchanged. Source: D. Zeilberger (1996); G. Kuperberg (1996). Knill, §168.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.AlternatingSignMatrixWanted
namespace Combinatorics.AlternatingSignMatrix

/-!
# The alternating sign matrix theorem

`alternating_sign_matrix_count` (Zeilberger 1994 / Kuperberg 1996): the number
of `n × n` alternating sign matrices is the Robbins product
`∏_{k<n} (3k+1)! / (n+k)!`. Trusted helpers (`IsAlternatingSignMatrix`,
`AlternatingSignMatrix`, `robbinsProduct`, …) are non-holes. Mathlib has no ASM
enumeration.
Category-(b) candidate from §168 of the Knill survey.
-/

open Matrix
open scoped BigOperators

/-- **Row partial sums of a matrix.** For an $n \times n$ integer matrix $A$ and indices
$i, k \in \{0, \dots, n-1\}$, the row partial sum of $A$ at $(i, k)$ is the sum of the entries of
row $i$ in columns $0$ through $k$, that is, $\sum_{j \le k} A_{ij}$. -/
def rowPartialSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i k : Fin n) : ℤ :=
  Finset.sum (Finset.univ.filter (fun j : Fin n => j ≤ k)) (fun j => A i j)

/-- **Column partial sums of a matrix.** For an $n \times n$ integer matrix $A$ and indices
$j, k \in \{0, \dots, n-1\}$, the column partial sum of $A$ at $(j, k)$ is the sum of the entries
of column $j$ in rows $0$ through $k$, that is, $\sum_{i \le k} A_{ij}$. -/
def colPartialSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j k : Fin n) : ℤ :=
  Finset.sum (Finset.univ.filter (fun i : Fin n => i ≤ k)) (fun i => A i j)

/-- **Integers equal to zero or one.** An integer $a$ is zero or one when $a = 0$ or $a = 1$. These
are the values allowed for the partial sums of an alternating sign matrix. -/
def IsZeroOrOne (a : ℤ) : Prop := a = 0 ∨ a = 1

/-- **Alternating sign matrices.** An $n \times n$ integer matrix $A$ is an alternating sign matrix
when every entry of $A$ is $-1$, $0$ or $1$; for all indices $i, k$ the row partial sum
$\sum_{j \le k} A_{ij}$ is $0$ or $1$; for all indices $j, k$ the column partial sum
$\sum_{i \le k} A_{ij}$ is $0$ or $1$; every row of $A$ sums to $1$; and every column of $A$
sums to $1$. -/
def IsAlternatingSignMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) ∧
  (∀ i k, IsZeroOrOne (rowPartialSum A i k)) ∧
  (∀ j k, IsZeroOrOne (colPartialSum A j k)) ∧
  (∀ i, ∑ j, A i j = 1) ∧
  (∀ j, ∑ i, A i j = 1)

/-- **Alternating sign matrices of size $n$.** For a natural number $n$, this is the collection of
all $n \times n$ integer matrices that are alternating sign matrices. -/
abbrev ASMatrix (n : ℕ) :=
  { A : Matrix (Fin n) (Fin n) ℤ // IsAlternatingSignMatrix A }

/-- **The Robbins product.** For a natural number $n$, the Robbins product is the rational number
$$\prod_{k=0}^{n-1} \frac{(3k+1)!}{(n+k)!},$$
an empty product, equal to $1$, when $n = 0$. -/
def robbinsProduct (n : ℕ) : ℚ :=
  Finset.prod (Finset.range n)
    (fun k => (Nat.factorial (3 * k + 1) : ℚ) / (Nat.factorial (n + k) : ℚ))

/- **Alternating sign matrix theorem.** The number of `n × n` ASMs equals the
Robbins product. -/
/-- **Alternating sign matrix theorem.** For every natural number $n$, the number of
$n \times n$ alternating sign matrices equals the Robbins product
$\prod_{k=0}^{n-1} \frac{(3k+1)!}{(n+k)!}$.

Source: D. Zeilberger (1996); G. Kuperberg (1996). Knill, §168. Via leanprover/lean-eval@38361be, problem `alternating_sign_matrix_count`. -/
public theorem_wanted alternating_sign_matrix_count (n : ℕ) :
    (Nat.card (ASMatrix n) : ℚ) = robbinsProduct n

end Combinatorics.AlternatingSignMatrix

end MathlibExt.Combinatorics.AlternatingSignMatrixWanted
