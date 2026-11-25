/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Solvable extensions ↔ solvable groups (the missing converse in Abel–Ruffini)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Algebra.SolvableByRadicals` — solvable_by_radicals_converse (manifest `manifests/problems/solvable_by_radicals_converse.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Algebra.SolvableByRadicalsWanted` namespace. Mathematical
statements are unchanged. Source: É. Galois (1832); the iff appears in standard texts such as Stewart, *Galois Theory* (Theorem 18.10); Lang, *Algebra* (VI §7); Rotman, *Galois Theory* (Theorem 73). Listed as §58 (additional statement 2) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Algebra.SolvableByRadicalsWanted
namespace Algebra

/-!
# Solvable extensions ↔ solvable groups

For a characteristic-zero field `F` and a nonzero polynomial `p ∈ F[X]`,
every root of `p` in `AlgebraicClosure F` lies in
`solvableByRad F (AlgebraicClosure F)` if and only if its Galois group
`p.Gal` is solvable. §58 of Knill's *Some Fundamental Theorems in
Mathematics* (additional statement). The left-hand side quantifies over
the actual roots of `p`, so the statement does not depend on choosing a
sufficiently large ambient extension.

Mathlib has the `→` direction in `Mathlib/FieldTheory/AbelRuffini.lean`
via `isSolvable_gal_of_irreducible` / `isSolvable_gal_minpoly`: a root
in `solvableByRad F E` has solvable minimal-polynomial Galois group.
The header docstring of that file states it proves "one direction" of
Abel–Ruffini. The `←` direction is the Kummer-theory content (solvable
Galois group implies roots in `solvableByRad`) and is the missing piece.

This is the polynomial-level statement, not the irreducible/minpoly
form already in mathlib.
-/

open Polynomial IntermediateField

/-- **Solvable extensions ↔ solvable groups.** Let $F$ be a field of characteristic zero and let
$p \in F[X]$ be a nonzero polynomial. Every root of $p$ in an algebraic closure $\overline{F}$ of
$F$ is solvable by radicals over $F$ (obtainable from $F$ by field operations and $n$-th roots
inside $\overline{F}$) if and only if the Galois group of $p$ over $F$ is solvable.

Source: É. Galois (1832); the iff appears in standard texts such as Stewart, *Galois Theory* (Theorem 18.10); Lang, *Algebra* (VI §7); Rotman, *Galois Theory* (Theorem 73). Listed as §58 (additional statement 2) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `solvable_by_radicals_converse`. -/
public theorem_wanted solvable_iff_solvableByRad (F : Type*) [Field F] [CharZero F]
    (p : F[X]) (_hp : p ≠ 0) :
    (∀ x : AlgebraicClosure F, aeval x p = 0 →
        x ∈ solvableByRad F (AlgebraicClosure F)) ↔ Group.IsSolvable p.Gal

end Algebra

end MathlibExt.Algebra.SolvableByRadicalsWanted
