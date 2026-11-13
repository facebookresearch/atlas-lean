/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abel–Ruffini theorem

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
the `abel_ruffini` statement below is taken verbatim from
leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e,
module `LeanEval.Algebra.AbelRuffini` (manifest
`manifests/problems/abel_ruffini.toml`, statement revision 1, submitter
Kim Morrison), which is distributed under the Apache License, Version 2.0.
The original statement had no per-file copyright header and lean-eval
ships no `NOTICE` file. Changes made in this file: converted the original
`@[eval_problem] theorem … := by sorry` into a Batteries
`theorem_wanted`, replaced `import Mathlib` and `EvalTools.Markers` with
minimal imports, placed the declaration in the
`MathlibExt.Algebra.AbelRuffiniWanted` namespace, and corrected the
source docstring's reversed forward/reverse direction descriptions. The
mathematical statement itself is unchanged.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.AbelRuffini

@[expose] public section

namespace MathlibExt.Algebra.AbelRuffiniWanted

open Polynomial

/--
**Abel–Ruffini theorem.** Let $n \ge 1$ be a natural number. Every complex root of every
polynomial with rational coefficients of degree exactly $n$ is expressible by radicals over
$\mathbb{Q}$ if and only if $n \le 4$. Here a complex number is expressible by radicals over
$\mathbb{Q}$ when it lies in the smallest subfield $S$ of $\mathbb{C}$ such that $z \in S$
whenever $z \in \mathbb{C}$ and $z^k \in S$ for some integer $k \ge 1$.

The direction from radical solvability to $n \le 4$ is the classical insolvability of the
general quintic, extended to higher degrees; the converse follows from the explicit formulas
of Cardano and Ferrari for degrees at most four.

Source: P. Ruffini (1799), N. H. Abel (1824), É. Galois (1832). Listed as §57
in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf);
the general-quintic insolvability is #16 on Freek Wiedijk's *Formalizing 100
Theorems* list (https://www.cs.ru.nl/~freek/100/). Taken verbatim, with no
Lean variant, from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, manifest
`manifests/problems/abel_ruffini.toml` (statement revision 1), module
`LeanEval.Algebra.AbelRuffini`, hole `abel_ruffini`.
-/
public theorem_wanted abel_ruffini (n : ℕ) (_hn : 1 ≤ n) :
    (∀ p : ℚ[X], p.natDegree = n → ∀ x : ℂ, aeval x p = 0 →
        x ∈ solvableByRad ℚ ℂ) ↔ n ≤ 4

end MathlibExt.Algebra.AbelRuffiniWanted
