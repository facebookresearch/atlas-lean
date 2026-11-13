/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The 290 theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.TwoNinetyTheorem` — two_ninety_theorem (manifest `manifests/problems/two_ninety_theorem.toml`, rev 1, submitter Bolton Bailey/Project Numina, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.TwoNinetyTheoremWanted` namespace. Mathematical
statements are unchanged. Source: M. Bhargava, J. Hanke, Universal quadratic forms and the 290-theorem, preprint (2011). See also https://en.wikipedia.org/wiki/15_and_290_theorems
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.TwoNinetyTheoremWanted
namespace NumberTheory.TwoNinety

/-!
# The 290 theorem

A positive-definite integral quadratic form represents every positive integer
as soon as it represents the 29 critical numbers
`1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31, 34, 35,
37, 42, 58, 93, 110, 145, 203, 290`.

See <https://en.wikipedia.org/wiki/15_and_290_theorems>.
-/

open Matrix

variable {R : Type*} [Ring R] {n : ℕ}

/-- **Quadratic form of a matrix.** For a ring $R$ and an $n \times n$ matrix $M$ with entries
in $R$, the value of the quadratic form of $M$ at a vector $x \in R^n$ is
$x \cdot (M x) = \sum_{i,j} x_i M_{ij} x_j$, where $i$ and $j$ range over $\{0, \dots, n-1\}$.

No symmetry of $M$ is assumed, and $R$ need not be commutative. -/
def evalQ (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : R := v ⬝ᵥ M *ᵥ v

/-- **Natural numbers represented by a quadratic form.** For a ring $R$, an $n \times n$ matrix
$M$ with entries in $R$ represents a natural number $m$ if there is an integer vector
$x \in \mathbb{Z}^n$ with $\sum_{i,j} x_i M_{ij} x_j = m$, where the entries of $x$ and the
number $m$ are viewed as elements of $R$. -/
def Represents (M : Matrix (Fin n) (Fin n) R) (m : ℕ) : Prop :=
  ∃ v : Fin n → ℤ, evalQ M (v · : _ → R) = m

/-- **Universal quadratic forms over a ring.** For a ring $R$, an $n \times n$ matrix $M$ with
entries in $R$ is universal if it represents every positive integer: for every positive
integer $m$ there is $x \in \mathbb{Z}^n$ with $\sum_{i,j} x_i M_{ij} x_j = m$ in $R$. -/
def IsUniversal (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ m : ℕ, 0 < m → Represents M m

/-- **Integer-valued quadratic forms.** For a ring $R$, an $n \times n$ matrix $M$ with entries
in $R$ is integral if its quadratic form takes integer values at integer vectors: for every
$x \in \mathbb{Z}^n$, the value $\sum_{i,j} x_i M_{ij} x_j$ computed in $R$ lies in the image
of $\mathbb{Z}$ in $R$. -/
def Integral (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ v : Fin n → ℤ, evalQ M (v · : _ → R) ∈ Set.range ((↑) : ℤ → R)

/-- **Critical numbers of the 290 theorem.** The critical numbers of the 290 theorem form the
set of the 29 natural numbers $1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29,
30, 31, 34, 35, 37, 42, 58, 93, 110, 145, 203, 290$. -/
def criticalNumbers : Finset ℕ :=
  {1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31,
   34, 35, 37, 42, 58, 93, 110, 145, 203, 290}

/-- **The 290 theorem.** Let $n$ be a natural number and let $M$ be a real $n \times n$ matrix
that is positive definite (symmetric, with $x^{\top} M x > 0$ for every nonzero
$x \in \mathbb{R}^n$) and integral (for every $x \in \mathbb{Z}^n$, the value $x^{\top} M x$ is
an integer). If $M$ represents each of the 29 critical numbers of the 290 theorem, that is,
for each critical number $m$ there is $x \in \mathbb{Z}^n$ with $x^{\top} M x = m$, then $M$
is universal: for every positive integer $m$ there is $x \in \mathbb{Z}^n$ with
$x^{\top} M x = m$.

Source: M. Bhargava, J. Hanke, Universal quadratic forms and the 290-theorem, preprint (2011). See also https://en.wikipedia.org/wiki/15_and_290_theorems Via leanprover/lean-eval@38361be, problem `two_ninety_theorem`. -/
public theorem_wanted two_ninety_theorem {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hpos : M.PosDef)
    (hIntegral : Integral M)
    (hrep : ∀ m ∈ criticalNumbers, Represents M m) :
    IsUniversal M

end NumberTheory.TwoNinety

end MathlibExt.NumberTheory.TwoNinetyTheoremWanted
