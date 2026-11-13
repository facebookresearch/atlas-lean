/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On Zagier-Hoffman's conjectures in positive characteristic

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ZagierHoffmanPositiveChar` — annals_zagier_hoffman_positive_char (manifest `manifests/problems/annals_zagier_hoffman_positive_char.toml`, rev 1, submitter Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ZagierHoffmanPositiveCharWanted` namespace. Mathematical
statements are unchanged. Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ZagierHoffmanPositiveCharWanted
/-!
# Main Statements from On Zagier-Hoffman's conjectures in positive characteristic

We formalise the statements of the main results from T. N. Dac,
`On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021.

## Implementation Details

Throughout the definitions and statements, we reindex the `i`'s so that they run from `0`
to `r - 1` rather than from `1` to `r`.
-/

set_option autoImplicit false

namespace ZagierHoffmanPositiveChar

open NNReal Polynomial RatFunc

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- **Tuples of monic polynomials with strictly decreasing degrees.** Let $F$ be a finite field
and $r$ a natural number. This is the set of $r$-tuples $(a_1, \dots, a_r)$ of monic polynomials
in $F[t]$ such that $\deg a_1 > \deg a_2 > \dots > \deg a_r$. -/
abbrev monicStrictAntiNatDegree (r : ℕ) :=
  {a : Fin r → Polynomial F // StrictAnti (Polynomial.natDegree ∘ a) ∧ ∀ i, (a i).Monic}

/-- **Multiple zeta values in positive characteristic.** Let $F$ be a finite field, $A = F[t]$,
and $K_\infty = F((1/t))$ the completion of the rational function field $F(t)$ at the place
at infinity. For a natural number $r$ and positive integers $s_1, \dots, s_r$, the multiple
zeta value is

$$\zeta_A(s_1, \dots, s_r) = \sum \frac{1}{a_1^{s_1} \cdots a_r^{s_r}} \in K_\infty,$$

where the sum runs over all $r$-tuples $(a_1, \dots, a_r)$ of monic polynomials in $A$ with
$\deg a_1 > \deg a_2 > \dots > \deg a_r$. -/
noncomputable def ζ_A {r : ℕ} (𝔰 : Fin r → ℕ+) : CompletionAtInfty F :=
  ∑' a : monicStrictAntiNatDegree F r, (∏ i, a.val i ^ (𝔰 i : ℕ))⁻¹

/-- **Compositions of $w$ into $r$ parts.** For natural numbers $w$ and $r$, $\mathfrak{S}_w$
is the set of $r$-tuples $(s_1, \dots, s_r)$ of positive integers with $s_1 + \dots + s_r = w$. -/
def 𝔖_w (w : ℕ) (r : ℕ) : Set (Fin r → ℕ+) := {𝔰 : Fin r → ℕ+ | ∑ i : Fin r, (𝔰 i : ℕ) = w}

/-- **Multiple zeta values of given depth and weight.** Let $F$ be a finite field and let $w$
and $r$ be natural numbers. The weight of a multiple zeta value $\zeta_A(s_1, \dots, s_r)$ over
$F$, with $s_1, \dots, s_r$ positive integers, is $s_1 + \dots + s_r$. This is the set of multiple
zeta values $\zeta_A(s_1, \dots, s_r)$ over $F$ of weight $w$, that is, with $s_1, \dots, s_r$
positive integers and $s_1 + \dots + s_r = w$. -/
def ζ_A_weight (w : ℕ) (r : ℕ) : Set (CompletionAtInfty F) := {ζ_A F 𝔰 | 𝔰 ∈ 𝔖_w w r}

/-- **The space $\mathcal{Z}_w$ of multiple zeta values of weight $w$.** Let $K$ be the field of
rational functions in one variable over the finite field $F$, and $K_\infty$ its completion at
infinity. For $w \in \mathbb{N}$, $\mathcal{Z}_w$ is the $K$-linear subspace of $K_\infty$ spanned
by the multiple zeta values $\zeta_A(s_1, \dots, s_r)$ for all $r \ge 0$ and all positive integers
$s_1, \dots, s_r$ with $s_1 + \dots + s_r = w$. -/
noncomputable def 𝒵 (w : ℕ) : Submodule (RatFunc F) (CompletionAtInfty F) :=
  Submodule.span (RatFunc F) (⋃ r, ζ_A_weight F w r)

/-- **Restricted multiple zeta values of given depth.** Let $F$ be a finite field with $q$
elements, $w$ a natural number and $r$ a positive integer. This is the set of multiple zeta
values $\zeta_A(s_1, \dots, s_r)$ over $F$ with positive integers $s_1, \dots, s_r$ such that
$s_1 + \dots + s_r = w$, $s_i \le q$ for $1 \le i \le r - 1$, and $s_r < q$. -/
def 𝒯_aux (w : ℕ) (r : ℕ+) : Set (CompletionAtInfty F) :=
  let q := Nat.card F
  let 𝔖'_w := {𝔰 ∈ 𝔖_w w r | (∀ i : Fin r, i < (r - 1 : ℕ) → 𝔰 i ≤ q) ∧ 𝔰 ⟨r - 1, by simp⟩ < q}
  {ζ_A F s | s ∈ 𝔖'_w}

/-- **The set $\mathcal{T}_w$ of restricted multiple zeta values.** Let $q$ be the number of
elements of the finite field $F$. For $w \in \mathbb{N}$, $\mathcal{T}_w$ is the set of multiple
zeta values $\zeta_A(s_1, \dots, s_r)$, over all $r \ge 1$ and all positive integers
$s_1, \dots, s_r$ with $s_1 + \dots + s_r = w$, $s_i \le q$ for $1 \le i \le r - 1$,
and $s_r < q$. -/
def 𝒯 (w : ℕ) : Set (CompletionAtInfty F) := ⋃ r : ℕ+, 𝒯_aux F w r

/-- **Multiple zeta values of given depth with small entries.** Let $F$ be a finite field with
$q$ elements, $w$ a natural number and $r$ a positive integer. This is the set of multiple
zeta values $\zeta_A(s_1, \dots, s_r)$ over $F$ with positive integers $s_1, \dots, s_r$ such
that $s_1 + \dots + s_r = w$ and $s_i < q$ for all $i$. -/
def 𝒯0_aux (w : ℕ) (r : ℕ+) : Set (CompletionAtInfty F) :=
  let q := Nat.card F
  let 𝔖'_w := {𝔰 ∈ 𝔖_w w r | ∀ i, 𝔰 i < q}
  {ζ_A F s | s ∈ 𝔖'_w}

/-- **Multiple zeta values with small entries.** Let $F$ be a finite field with $q$ elements and
$w$ a natural number. The set $\mathcal{T}^0_w$ consists of the multiple zeta values
$\zeta_A(s_1, \dots, s_r)$ over $F$, for all positive integers $r$ and $s_1, \dots, s_r$ such
that $s_1 + \dots + s_r = w$ and $s_i < q$ for all $i$. -/
def 𝒯0 (w : ℕ) : Set (CompletionAtInfty F) := ⋃ r : ℕ+, 𝒯0_aux F w r

/-- **Dimension sequence for multiple zeta values.** Let $F$ be a finite field with $q$ elements.
The sequence $d(w)$, for natural numbers $w$, is defined by $d(0) = 1$, $d(w) = 2^{w-1}$ for
$1 \le w \le q - 1$, $d(q) = 2^{q-1} - 1$, and
$d(w) = d(w - 1) + d(w - 2) + \dots + d(w - q)$ for $w > q$.

This is the sequence of Conjecture 1.5 and Theorems A and D of T. N. Dac, On Zagier-Hoffman's
conjectures in positive characteristic. -/
noncomputable def d (w : ℕ) : ℕ :=
  let q := Nat.card F
  if w = 0 then 1
  else if w ≤ q - 1 then 2 ^ (w - 1)
  else if w = q then 2 ^ (w - 1) - 1
  else ∑ i ∈ Finset.range q, d (w - (i + 1))

/--
**Brown's theorem in positive characteristic.** Let $F$ be a finite field with $q$ elements,
$K = F(t)$, and $w$ a positive integer. Let $\mathcal{Z}_w$ be the $K$-vector space spanned by
the multiple zeta values over $F$ of weight $w$, and let $\mathcal{T}_w$ be the set of multiple
zeta values $\zeta_A(s_1, \dots, s_r)$ with $r \ge 1$, positive integers $s_1, \dots, s_r$ with
sum $w$, $s_i \le q$ for $1 \le i \le r - 1$, and $s_r < q$. Then $\mathcal{Z}_w$ is the
$K$-linear span of $\mathcal{T}_w$, so every multiple zeta value of weight $w$ is a $K$-linear
combination of elements of $\mathcal{T}_w$, and $\dim_K \mathcal{Z}_w \le d(w)$, where $d$ is
the dimension sequence for multiple zeta values.

Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
-/
public theorem_wanted theorem_A (w : ℕ+) :
    𝒵 F w = Submodule.span (RatFunc F) (𝒯 F w) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≤ d F w

/--
**Linear independence of multiple zeta values with small entries.** Let $F$ be a finite field
with $q$ elements, $K = F(t)$, and $w$ a positive integer. Let $\mathcal{T}^0_w$ be the set of
multiple zeta values $\zeta_A(s_1, \dots, s_r)$ over $F$ with $r \ge 1$, positive integers
$s_1, \dots, s_r$ with sum $w$, and $s_i < q$ for all $i$, and let $\mathcal{Z}_w$ be the
$K$-vector space spanned by all multiple zeta values of weight $w$. Then the elements of
$\mathcal{T}^0_w$ are linearly independent over $K$, and
$\dim_K \mathcal{Z}_w \ge |\mathcal{T}^0_w|$.

Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
-/
public theorem_wanted theorem_B (w : ℕ+) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F w → CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≥ Set.ncard (𝒯0 F w)

/--
**Dimension of multiple zeta values in low weight.** Let $F$ be a finite field with $q$
elements, $K = F(t)$, and $w$ a positive integer with $w \le 2q - 2$. Let $\mathcal{T}_w$ be the
set of multiple zeta values $\zeta_A(s_1, \dots, s_r)$ over $F$ with $r \ge 1$, positive integers
$s_1, \dots, s_r$ with sum $w$, $s_i \le q$ for $1 \le i \le r - 1$, and $s_r < q$, and let
$\mathcal{Z}_w$ be the $K$-vector space spanned by all multiple zeta values of weight $w$. Then
the elements of $\mathcal{T}_w$ are linearly independent over $K$, and
$\dim_K \mathcal{Z}_w = d(w)$, where $d$ is the dimension sequence for multiple zeta values.

Together with Brown's theorem in positive characteristic (Theorem A of the source), which says
that $\mathcal{T}_w$ spans $\mathcal{Z}_w$, this means that $\mathcal{T}_w$ is a $K$-basis of
$\mathcal{Z}_w$.

Source: T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
-/
public theorem_wanted theorem_D (w : ℕ+) (hw : w ≤ 2 * Nat.card F - 2) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F w → CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) = d F w

end ZagierHoffmanPositiveChar

end MathlibExt.NumberTheory.ZagierHoffmanPositiveCharWanted
