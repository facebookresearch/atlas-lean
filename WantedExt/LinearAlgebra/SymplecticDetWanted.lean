/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Symplectic matrices have determinant 1

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.LinearAlgebra.SymplecticDet` — symplectic_matrix_det (manifest `manifests/problems/symplectic_matrix_det.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.LinearAlgebra.SymplecticDetWanted` namespace. Mathematical
statements are unchanged. Source: Folklore (Pfaffian computation). Listed as §39 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Marked as an open TODO at the head of Mathlib/LinearAlgebra/SymplecticGroup.lean (rev 5450b53e5ddc).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.LinearAlgebra.SymplecticDetWanted
namespace LinearAlgebra

/-!
# Symplectic matrices have determinant 1

§39 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. For any
commutative ring `R` and `2n × 2n` symplectic matrix `A` over `R` (i.e.
`A * J * Aᵀ = J` with `J = [[0, -I], [I, 0]]`), one has `det A = 1`.

Taking determinants of `Aᵀ J A = J` only forces `(det A)² = 1`; the sign
requires the Pfaffian argument (`det A = Pf(Aᵀ J A) / Pf(J) = 1`).

mathlib has `Matrix.symplecticGroup l R` and proves `symplectic_det`
(`IsUnit (det A)`) but the determinant-equals-one claim is an open TODO in
`Mathlib/LinearAlgebra/SymplecticGroup.lean`. No formalization of the
identity was found in any other proof assistant.
-/

open Matrix

/- **Symplectic matrices have determinant 1.** For any commutative ring `R`
and `2n × 2n` symplectic matrix `A` over `R`, `A.det = 1`. -/
/-- Source: Folklore (Pfaffian computation). Listed as §39 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Marked as an open TODO at the head of Mathlib/LinearAlgebra/SymplecticGroup.lean (rev 5450b53e5ddc). Via leanprover/lean-eval@38361be, problem `symplectic_matrix_det`. -/
public theorem_wanted symplectic_matrix_det
    {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {A : Matrix (l ⊕ l) (l ⊕ l) R} (_hA : A ∈ Matrix.symplecticGroup l R) :
    A.det = 1

end LinearAlgebra

end MathlibExt.LinearAlgebra.SymplecticDetWanted
