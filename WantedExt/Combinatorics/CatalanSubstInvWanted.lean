/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Catalan generating function via compositional inversion

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.CatalanSubstInv` — substInv_X_sub_X_sq_eq_catalan (manifest `manifests/problems/substInv_X_sub_X_sq_eq_catalan.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.CatalanSubstInvWanted` namespace. Mathematical
statements are unchanged. Source: E. Catalan, Note sur une équation aux différences finies, 1838; J.-L. Lagrange, Nouvelle méthode pour résoudre les équations littérales, 1770.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Data.Nat.Choose.Central

@[expose] public section

namespace MathlibExt.Combinatorics.CatalanSubstInvWanted
namespace Combinatorics

open PowerSeries

/-!
The Catalan generating function via compositional inversion.

The Catalan numbers `C_n = (2n choose n) / (n + 1)` arise as the coefficients of the
compositional inverse of the power series `X - X²`. This is one of the most classical
applications of Lagrange inversion in enumerative combinatorics: the generating function
`C(x) = ∑ C_n x^{n+1}` satisfies `C(x) - C(x)² = x`, so `C` is the compositional inverse
of the polynomial `P(x) = x - x²`.

Equivalently, `C(x) = (1 - √(1 - 4x)) / 2`.

This identity connects formal power series inversion (`substInv`) to the enumeration of
Dyck paths, binary trees, triangulations of polygons, and many other combinatorial structures.
-/

public theorem_wanted substInv_X_sub_X_sq_eq_catalan (n : ℕ) :
    haveI : Invertible (coeff 1 ((X : ℚ⟦X⟧) - X ^ 2)) := by
      simp [coeff_X, coeff_X_pow]; exact invertibleOne
    coeff (n + 1) (substInv ((X : ℚ⟦X⟧) - X ^ 2)) =
      (Nat.choose (2 * n) n : ℚ) / (↑n + 1)

end Combinatorics

end MathlibExt.Combinatorics.CatalanSubstInvWanted
