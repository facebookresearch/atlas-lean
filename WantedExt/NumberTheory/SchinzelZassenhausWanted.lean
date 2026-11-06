/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dimitrov's lower bound for the house of a nonzero algebraic integer that is not a root of unity

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.SchinzelZassenhaus` — dimitrov (manifest `manifests/problems/dimitrov.toml`, rev 1, submitter Zou Jinping, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.SchinzelZassenhausWanted` namespace. Mathematical
statements are unchanged. Source: James McKee and Chris Smyth, Around the Unit Circle, Chapter 4, Theorem 4.1; Vesselin Dimitrov (2019).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.House

@[expose] public section

namespace MathlibExt.NumberTheory.SchinzelZassenhausWanted
/-!
# The Schinzel–Zassenhaus Conjecture

This file records a Lean statement of Dimitrov's theorem as it appears in
Chapter 4 of McKee and Smyth, *Around the Unit Circle*.

Let `α₁, ..., αₙ` denote the conjugates of a nonzero algebraic
integer `α` which is not a root of unity.  The Schinzel–Zassenhaus
conjecture asserts that there is an absolute constant `c > 0` such that

`max_{1 ≤ j ≤ n} |αⱼ| > 1 + c / d`.

The quantity `maxⱼ |αⱼ|` is called the house of `α`; in Mathlib this
is `NumberField.house`.

## Reference

The formalization is based on Chapter 4 ("The Schinzel–Zassenhaus Conjecture") of the book:
* **James McKee, Chris Smyth**, *Around the Unit Circle: Mahler Measure, Integer Matrices and Roots of Unity*, Springer, Universitext, 2021.
（https://link.springer.com/chapter/10.1007/978-3-030-80031-4_4）
-/

namespace NumberTheory

/- **Dimitrov's theorem**, McKee–Smyth Theorem 4.1.

Let `α` be a nonzero algebraic integer, not a root of unity.  Then the
house of `α` is at least `2 ^ (1 / (4 * d'))`, where `d'` is the number of
different phases among its conjugates.

The condition "not a root of unity" is expressed as `¬ IsOfFinOrder α`,
Mathlib's standard predicate for an element having no positive power equal to 1.
Source: James McKee and Chris Smyth, Around the Unit Circle, Chapter 4, Theorem 4.1; Vesselin Dimitrov (2019). Via leanprover/lean-eval@38361be, problem `dimitrov`.
-/

/-- **Dimitrov's lower bound for the house of an algebraic integer.** Let $K$ be a number field
and let $\alpha \in K$ be a nonzero algebraic integer that is not a root of unity. Let $d'$ be
the number of distinct values of the argument $\arg \sigma(\alpha)$ as $\sigma$ ranges over the
ring homomorphisms $K \to \mathbb{C}$. Then the house of $\alpha$, the maximum of
$|\sigma(\alpha)|$ over these $\sigma$, is at least $2^{1/(4d')}$.

Source: James McKee and Chris Smyth, Around the Unit Circle, Chapter 4, Theorem 4.1; Vesselin Dimitrov (2019). Via leanprover/lean-eval@38361be, problem `dimitrov`. -/
public theorem_wanted dimitrov {K : Type*} [Field K] [NumberField K]
    (α : K)
    (α_int : IsIntegral ℤ α)
    (α_ne_zero : α ≠ 0)
    (α_not_rootOfUnity : ¬ IsOfFinOrder α) :
    (2 : ℝ) ^ (1 / (4 * (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card) : ℝ) ≤
      NumberField.house α

end NumberTheory

end MathlibExt.NumberTheory.SchinzelZassenhausWanted
