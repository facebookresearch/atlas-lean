/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conway–Schneeberger fifteen theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ConwaySchneebergerFifteen` — conway_schneeberger_fifteen (manifest `manifests/problems/conway_schneeberger_fifteen.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ConwaySchneebergerFifteenWanted` namespace. Mathematical
statements are unchanged. Source: Conway–Schneeberger 1993 (unpublished, communicated by Conway in lectures); full proof M. Bhargava, 'On the Conway–Schneeberger fifteen theorem', in *Quadratic Forms and their Applications* (Contemp. Math. 272, AMS 2000). Listed as §95 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.ConwaySchneebergerFifteenWanted
namespace NumberTheory
namespace ConwaySchneebergerFifteenProblem

/-!
# Conway–Schneeberger fifteen theorem

A positive-definite integer-matrix quadratic form `Q : ℤⁿ → ℤ` is
**universal** (represents every positive integer) iff it represents
every integer in `{1, 2, …, 15}`. Conway–Schneeberger 1993; full
published proof Bhargava 2000 (*New Directions in Quadratic Forms*,
Contemp. Math. **272**). §95 in Knill's *Some Fundamental Theorems in
Mathematics*.

Definitions are kept matrix-explicit (rather than going through
mathlib's bundled `QuadraticMap`) because Knill's statement makes the
integer entries of `Q` central — the integer-matrix versus
integer-valued distinction is precisely the difference between the 15
theorem here and Bhargava–Hanke's 290 theorem.
-/

/-- **Quadratic form of an integer matrix.** For an $n \times n$ matrix $Q$ with integer
entries, the quadratic form of $Q$ is the map $\mathbb{Z}^n \to \mathbb{Z}$ sending $x$ to
$Q(x) = \sum_{i,j} Q_{ij} x_i x_j$, where $i$ and $j$ range over $\{0, \dots, n-1\}$. No
symmetry of $Q$ is assumed. -/
def evalQ {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ :=
  ∑ i, ∑ j, Q i j * x i * x j

/-- **Integers represented by an integer-matrix quadratic form.** An $n \times n$ matrix $Q$
with integer entries represents an integer $m$ if $Q(x) = m$ for some $x \in \mathbb{Z}^n$,
where $Q(x) = \sum_{i,j} Q_{ij} x_i x_j$. -/
def Represents {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℤ) (m : ℤ) : Prop :=
  ∃ x : Fin n → ℤ, evalQ Q x = m

/-- **Universal integer-matrix quadratic forms.** An $n \times n$ matrix $Q$ with integer
entries is universal if its quadratic form $Q(x) = \sum_{i,j} Q_{ij} x_i x_j$ represents every
positive integer, that is, for every positive integer $m$ there is $x \in \mathbb{Z}^n$ with
$Q(x) = m$. -/
def IsUniversal {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → Represents Q (m : ℤ)

/- **Conway–Schneeberger fifteen theorem** (Conway–Schneeberger 1993,
proof Bhargava 2000). A positive-definite integer-matrix quadratic form
is universal iff it represents every integer in `{1, 2, …, 15}`.

The forward direction is immediate; the content is the converse — 15 is
the smallest `N` such that representing `{1, …, N}` implies representing
every positive integer. Bhargava's refinement reduces the critical set
to `{1, 2, 3, 5, 6, 7, 10, 14, 15}` (9 elements). -/
/-- **Conway–Schneeberger fifteen theorem.** Let $Q$ be a positive definite symmetric
$n \times n$ matrix with integer entries, with quadratic form $Q(x) = \sum_{i,j} Q_{ij} x_i x_j$
on $\mathbb{Z}^n$. Then $Q$ is universal, that is, it represents every positive integer, if and
only if it represents every integer $k$ with $1 \le k \le 15$.

The forward direction is immediate; the content is the converse. Bhargava's refinement reduces
the critical set to $\{1, 2, 3, 5, 6, 7, 10, 14, 15\}$.

Source: Conway–Schneeberger 1993 (unpublished, communicated by Conway in lectures); full proof M. Bhargava, 'On the Conway–Schneeberger fifteen theorem', in *Quadratic Forms and their Applications* (Contemp. Math. 272, AMS 2000). Listed as §95 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `conway_schneeberger_fifteen`. -/
public theorem_wanted conway_schneeberger_fifteen {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℤ)
    (_hpos : Q.PosDef) :
    IsUniversal Q ↔ ∀ k ∈ Finset.Icc (1 : ℤ) 15, Represents Q k

end ConwaySchneebergerFifteenProblem
end NumberTheory

end MathlibExt.NumberTheory.ConwaySchneebergerFifteenWanted
