/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Martinet's asymptotically-good totally real towers

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.MartinetTotallyRealTowers` — martinet_totally_real_towers (manifest `manifests/problems/martinet_totally_real_towers.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.MartinetTotallyRealTowersWanted` namespace. Mathematical
statements are unchanged. Source: Theorem 3.2 of T. F. Bloom, W. Sawin, C. Schildkraut, D. Zhelezov, *The sum-product conjecture is false for real numbers*, arXiv:2605.28781. Lean axiom: https://github.com/mathlib-initiative/sum_product (SumProduct.exists_totallyReal_discr_le). Underlying result: J. Martinet, *Tours de corps de classes et estimations de discriminants*, Invent. Math. 44 (1978), 65–73.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.MartinetTotallyRealTowersWanted
namespace NumberTheory

/-!
# Martinet's asymptotically-good totally real towers

`exists_totallyReal_discr_le` is Theorem 3.2 of

> T. F. Bloom, W. Sawin, C. Schildkraut, D. Zhelezov,
> *The sum-product conjecture is false for real numbers*, `arXiv:2605.28781`,

which is the sole classical input their formalization takes as an axiom (see
`SumProduct.exists_totallyReal_discr_le` in
<https://github.com/mathlib-initiative/sum_product>). The underlying result is
Martinet's construction (1978) of asymptotically-good totally real towers — a
family of totally real number fields of growing degree with bounded root
discriminant — obtained from class field theory (Golod–Shafarevich towers).
It is not currently available in Mathlib.

A bounded root discriminant `rd_K = |Δ_K|^{1/d} ≤ C` is exactly the statement
that `|Δ_K| ≤ C ^ d`, so the bound below captures Martinet's theorem in the
form used by the sum-product argument. "Infinitely many degrees `d`" is the
cofinal form `∀ N, ∃ d ≥ N`.
-/

open NumberField

/- **Theorem 3.2 (Martinet).**

There is an absolute constant `C > 0` such that for infinitely many degrees `d`
there is a totally real number field `K` of degree `d` over `ℚ` whose
discriminant satisfies `|Δ_K| ≤ C ^ d`.

"Infinitely many `d`" is expressed as: for every `N` there is a degree `d ≥ N`
that works. -/
/-- **Martinet's totally real towers.** There is a real constant $C > 0$ such that for every
$N \in \mathbb{N}$ there exist a natural number $d \ge N$ and a totally real number field $K$ of
degree $[K : \mathbb{Q}] = d$ whose discriminant $\Delta_K$ satisfies $|\Delta_K| \le C^d$.

Source: Theorem 3.2 of T. F. Bloom, W. Sawin, C. Schildkraut, D. Zhelezov, *The sum-product conjecture is false for real numbers*, arXiv:2605.28781. Lean axiom: https://github.com/mathlib-initiative/sum_product (SumProduct.exists_totallyReal_discr_le). Underlying result: J. Martinet, *Tours de corps de classes et estimations de discriminants*, Invent. Math. 44 (1978), 65–73. Via leanprover/lean-eval@38361be, problem `martinet_totally_real_towers`. -/
public theorem_wanted exists_totallyReal_discr_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d

end NumberTheory

end MathlibExt.NumberTheory.MartinetTotallyRealTowersWanted
