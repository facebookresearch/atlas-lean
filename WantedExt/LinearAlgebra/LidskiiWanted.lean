/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lidskii–Last eigenvalue-perturbation theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.LinearAlgebra.Lidskii` — lidskii_last (manifest `manifests/problems/lidskii_last.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.LinearAlgebra.LidskiiWanted` namespace. Mathematical
statements are unchanged. Source: V. B. Lidskii (1950); the entrywise ℓ¹ form is due to Y. Last (around 1993). Listed as §99 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.LinearAlgebra.LidskiiWanted
namespace LinearAlgebra

/-!
# Lidskii–Last eigenvalue-perturbation theorem

§99 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. For two
self-adjoint complex `n × n` matrices `A, B` with eigenvalues sorted in the
same order, the total eigenvalue displacement is bounded by the entrywise
`ℓ¹` distance:

  `∑ⱼ |αⱼ − βⱼ| ≤ ∑ᵢⱼ |Aᵢⱼ − Bᵢⱼ|`.

This is Last's theorem (≈ 1993), a consequence of Lidskii's inequality
(1950). mathlib has `Matrix.IsHermitian.eigenvalues₀` (the spectral-theorem
eigenvalues) but none of the classical eigenvalue-perturbation bounds
(Lidskii, Ky Fan, Hoffman–Wielandt). The statement needs no auxiliary
definitions.
-/

open Matrix

/- **Lidskii–Last theorem.** For two self-adjoint complex `n × n` matrices
`A, B`, with eigenvalues sorted in the same order,
`∑ⱼ |αⱼ − βⱼ| ≤ ∑ᵢⱼ |Aᵢⱼ − Bᵢⱼ|`. -/
/-- **Lidskii–Last theorem.** Let $A$ and $B$ be Hermitian complex square matrices indexed by a
finite set with $N$ elements, and list the eigenvalues of $A$ and of $B$, each with multiplicity
and in decreasing order, as $\alpha_1 \ge \dots \ge \alpha_N$ and $\beta_1 \ge \dots \ge \beta_N$.
Then
$$\sum_{j=1}^N |\alpha_j - \beta_j| \le \sum_{i,j} |A_{ij} - B_{ij}|.$$

Source: V. B. Lidskii (1950); the entrywise ℓ¹ form is due to Y. Last (around 1993). Listed as §99 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `lidskii_last`. -/
public theorem_wanted lidskii_last {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
      ∑ i, ∑ j, ‖A i j - B i j‖

end LinearAlgebra

end MathlibExt.LinearAlgebra.LidskiiWanted
