/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A conjecture of Erdős, supersingular primes and short character sums

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ErdosSupersingularPrimes` — annals_erdos_supersingular_primes (manifest `manifests/problems/annals_erdos_supersingular_primes.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ErdosSupersingularPrimesWanted` namespace. Mathematical
statements are unchanged. Source: M. Bennett and S. Siksek, `A conjecture of Erdős, supersingular primes and short character sums`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-ErdosSupersingularPrimes.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosSupersingularPrimesWanted
/-!
# Main Statement from A conjecture of Erdős, supersingular primes and short character sums

We formalise the statement of the main result from M. Bennett and S. Siksek,
`A conjecture of Erdős, supersingular primes and short character sums`,
Annals of Math, 191 (2) 2020.
-/

set_option autoImplicit false

namespace ErdosSupersingularPrimes

open Int Real

/-- A solution to the Diophantine equation `n (n + d) (n + 2d) ··· (n + (k − 1)d) = y ^ l`,
where `gcd(n, d) = 1`. -/
structure Solution (k : ℕ) where
  /-- The exponent `l` in the solution. -/
  l : ℕ
  /-- The value of `n` in the solution. -/
  n : ℤ
  /-- The value of `d` in the solution. -/
  d : ℤ
  /-- The value of `y` in the solution. -/
  y : ℤ
  gcd : gcd n d = 1
  eq : ∏ i ∈ Finset.range k, (n + i * d) = y ^ l

/- The absolute constant such that for all `k ≥ k₀`, the theorem holds.

Part of the theorem statement is that `k₀` should be "effectively computable".
In principle, this means that the definition of `k₀` should avoid `Classical.choice`.
Unfortunately, this is not currently enforceable in Comparator.
Note that prohibiting `noncomputable` is not sufficient:
https://leanprover.zulipchat.com/#narrow/channel/583341-Model-comparisons-for-Lean/topic/LeanEval/near/598595369 -/
/-- Source: M. Bennett and S. Siksek, `A conjecture of Erdős, supersingular primes and short character sums`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-ErdosSupersingularPrimes.lean Via leanprover/lean-eval@38361be, problem `annals_erdos_supersingular_primes`. -/
public def_wanted k₀ : ℕ

/--
Statement of Theorem 2:

There is an effectively computable absolute constant `k₀` such
that if `k ≥ k₀` is a positive integer, then any `Solution` with prime exponent `l` satisfies
either `y = 0` or `d = 0` or `l ≤ exp(10 ^ k)`.
Source: M. Bennett and S. Siksek, `A conjecture of Erdős, supersingular primes and short character sums`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-ErdosSupersingularPrimes.lean Via leanprover/lean-eval@38361be, problem `annals_erdos_supersingular_primes`.
-/
public theorem_wanted theorem_2 (k : ℕ) (s : Solution k) (hs : s.l.Prime) :
    k ≥ ❰k₀❱ → s.y = 0 ∨ s.d = 0 ∨ s.l ≤ exp (10 ^ k)

end ErdosSupersingularPrimes

end MathlibExt.NumberTheory.ErdosSupersingularPrimesWanted
