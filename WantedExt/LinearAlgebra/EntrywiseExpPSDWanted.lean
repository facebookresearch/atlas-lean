/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Entrywise exponential of a PSD matrix is PSD

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.LinearAlgebra.EntrywiseExpPSD` — posSemidef_map_exp (manifest `manifests/problems/posSemidef_map_exp.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.LinearAlgebra.EntrywiseExpPSDWanted` namespace. Mathematical
statements are unchanged. Source: I.J. Schoenberg, Positive definite functions on spheres, 1942.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace MathlibExt.LinearAlgebra.EntrywiseExpPSDWanted
namespace LinearAlgebra

open scoped MatrixOrder Matrix

/-!
The entrywise exponential of a positive semidefinite matrix is positive semidefinite.

This is a consequence of the Schur product theorem (Schur 1911) and the Taylor expansion
of the exponential function. The key idea is that `exp_⊙(A)_{ij} = exp(a_{ij})` can be
written as the convergent series `∑ₖ (1/k!) A^{⊙k}`, where `A^{⊙k}` denotes the k-fold
Hadamard product. Each `A^{⊙k}` is positive semidefinite by iterated application of the
Schur product theorem, and a convergent nonnegative combination of PSD matrices is PSD.

This result is part of the Schur–Pólya–Loewner theory of entrywise functions preserving
positive semidefiniteness, with applications in statistics (correlation matrices) and
quantum information theory (density matrices).
-/

public theorem_wanted posSemidef_map_exp
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef

end LinearAlgebra

end MathlibExt.LinearAlgebra.EntrywiseExpPSDWanted
