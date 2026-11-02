/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Weyl bound for Dirichlet L-functions of cube-free conductor

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.DirichletWeylBound` — annals_dirichlet_weyl_bound (manifest `manifests/problems/annals_dirichlet_weyl_bound.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.DirichletWeylBoundWanted` namespace. Mathematical
statements are unchanged. Source: I. Petrow and M. P. Young, `The Weyl bound for Dirichlet L-functions of cube-free conductor`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-DirichletWeylBound.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import MathlibExt.NumberTheory.PowerFree

@[expose] public section

namespace MathlibExt.NumberTheory.DirichletWeylBoundWanted
/-!
# Main Statement from The Weyl bound for Dirichlet L-functions of cube-free conductor

We formalise the statement of the main result from I. Petrow and M. P. Young,
`The Weyl bound for Dirichlet L-functions of cube-free conductor`, Annals of Math, 192 (2) 2020.
-/

set_option autoImplicit false

/- A natural number `n` is cubefree if it is not divisible by `k ^ 3` for `k ≠ 1`;
below this is `Nat.IsPowerFree n 3` (no prime cube divides `n`). -/
namespace DirichletWeylBound

open Complex

/--
**Petrow–Young Weyl bound on the critical line.** For every real $\varepsilon > 0$ there is a
real number $C$ such that for every cube-free natural number $q$ (that is, $q > 0$ and $p^3$ does
not divide $q$ for any prime $p$), every primitive Dirichlet character $\chi$ modulo $q$ and
every real $t$, the analytically continued Dirichlet $L$-function satisfies
$$|L(1/2 + it, \chi)| \le C \, q^{1/6 + \varepsilon} (1 + |t|)^{1/6 + \varepsilon}.$$

This is Corollary 1.3 of the source.

Source: I. Petrow and M. P. Young, `The Weyl bound for Dirichlet L-functions of cube-free conductor`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-DirichletWeylBound.lean Via leanprover/lean-eval@38361be, problem `annals_dirichlet_weyl_bound`.
-/
public theorem_wanted corollary_1_3 (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ,
    ∀ q (_hq : q.IsPowerFree 3) [NeZero q] (χ : DirichletCharacter ℂ q) (_hχ : χ.IsPrimitive) (t : ℝ),
      ‖χ.LFunction (1 / 2 + I * t)‖ ≤ C * q ^ (1 / 6 + ε) * (1 + |t|) ^ (1 / 6 + ε)

end DirichletWeylBound

end MathlibExt.NumberTheory.DirichletWeylBoundWanted
