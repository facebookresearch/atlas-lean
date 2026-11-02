/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Friedlander–Iwaniec theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.FriedlanderIwaniec` — friedlander_iwaniec (manifest `manifests/problems/friedlander_iwaniec.toml`, rev 1, submitter Bolton Bailey/Project Numina, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.FriedlanderIwaniecWanted` namespace. Mathematical
statements are unchanged. Source: Friedlander, John, and Henryk Iwaniec. “The Polynomial X² + Y⁴ Captures Its Primes.” Annals of Mathematics, vol. 148, no. 3, 1998, pp. 945–1040. JSTOR, https://doi.org/10.2307/121034.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.FriedlanderIwaniecWanted
namespace NumberTheory.FriedlanderIwaniec

/-!
# Friedlander–Iwaniec theorem

There are infinitely many primes of the form `a² + b⁴`.

See <https://en.wikipedia.org/wiki/Friedlander%E2%80%93Iwaniec_theorem>.
-/
/-- **Friedlander–Iwaniec theorem.** There are infinitely many primes $p$ of the form
$p = a^2 + b^4$ with $a$ and $b$ natural numbers.

Source: Friedlander, John, and Henryk Iwaniec. “The Polynomial X² + Y⁴ Captures Its Primes.” Annals of Mathematics, vol. 148, no. 3, 1998, pp. 945–1040. JSTOR, https://doi.org/10.2307/121034. Via leanprover/lean-eval@38361be, problem `friedlander_iwaniec`. -/
public theorem_wanted friedlander_iwaniec : {p : ℕ | p.Prime ∧ ∃ a b, p = a ^ 2 + b ^ 4}.Infinite

end NumberTheory.FriedlanderIwaniec

end MathlibExt.NumberTheory.FriedlanderIwaniecWanted
