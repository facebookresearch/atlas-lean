/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lidskii's inequality

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.LinearAlgebra.LidskiiInequality` — lidskii_inequality (manifest `manifests/problems/lidskii_inequality.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.LinearAlgebra.LidskiiInequalityWanted` namespace. Mathematical
statements are unchanged. Source: V. B. Lidskii, On the proper values of a sum and product of symmetric matrices, Dokl. Akad. Nauk SSSR 75 (1950), 769-772. Listed as an additional statement of §99 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.LinearAlgebra.LidskiiInequalityWanted
namespace LinearAlgebra

/-!
# Lidskii's inequality

§99 of Oliver Knill's *Some Fundamental Theorems in Mathematics* (an
additional statement of the section on spectral perturbation; the boxed
main theorem `lidskii_last` follows as the `p = 1` case combined with an
entrywise bound).

For two self-adjoint complex `n × n` matrices `A, B` with eigenvalues
sorted in the same order, the `ℓ^p` displacement of the eigenvalues is
bounded by the `ℓ^p` norm of the eigenvalues of `C := B − A`, for every
real `p ≥ 1`:

  `∑ⱼ |αⱼ − βⱼ|^p ≤ ∑ⱼ |γⱼ|^p`.

mathlib has `Matrix.IsHermitian.eigenvalues₀` (the spectral-theorem
eigenvalues) but none of the classical eigenvalue-perturbation bounds
(Lidskii, Ky Fan, Hoffman–Wielandt). No formalization of Lidskii's
inequality was found in any other proof assistant.
-/

open Matrix

/- **Lidskii's inequality.** For two self-adjoint complex `n × n` matrices
`A, B`, with eigenvalues sorted in the same order and `p ≥ 1`,
`∑ⱼ |αⱼ − βⱼ|^p ≤ ∑ⱼ |γⱼ|^p` where `γⱼ` are the eigenvalues of `B − A`. -/
/-- Source: V. B. Lidskii, On the proper values of a sum and product of symmetric matrices, Dokl. Akad. Nauk SSSR 75 (1950), 769-772. Listed as an additional statement of §99 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `lidskii_inequality`. -/
public theorem_wanted lidskii_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {p : ℝ} (_hp : 1 ≤ p) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ^ p ≤
      ∑ j, |(hB.sub hA).eigenvalues₀ j| ^ p

end LinearAlgebra

end MathlibExt.LinearAlgebra.LidskiiInequalityWanted
