/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear independence results of Calegari–Dimitrov–Tang

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.CalegariDimitrovTangLinearIndependent` — cdt_linearIndependent (manifest `manifests/problems/cdt_linearIndependent.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.CalegariDimitrovTangLinearIndependentWanted` namespace. Mathematical
statements are unchanged. Source: https://arxiv.org/abs/2408.15403
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.CalegariDimitrovTangLinearIndependentWanted
/-!
# Linear independence results of Calegari–Dimitrov–Tang

Theorem A in the 218-page paper "The linear independence of 1, ζ(2), and L(2,χ₋₃)"
(https://arxiv.org/abs/2408.15403) by Frank Calegari, Vesselin Dimitrov, and Yunqing Tang
states that 1, ζ(2), and L(2,χ₋₃) are linear independent over ℚ.

Theorem C states that if m, n ∈ ℤ \ {-1, 0} and |m/n - 1| < 10⁻⁶, then
log(1 + 1/m) * log(1 + 1/n) is irrational, and 1, log(1 + 1/m), log(1 + 1/n) and
log(1 + 1/m) * log(1 + 1/n) are linearly independent over ℚ if m ≠ n.
-/

namespace NumberTheory.CalegariDimitrovTangLinearIndependent

/--
**Calegari–Dimitrov–Tang linear independence theorems.** Let
$\chi : \mathbb{Z}/3\mathbb{Z} \to \mathbb{C}$ be given by $\chi(0) = 0$, $\chi(1) = 1$ and
$\chi(2) = -1$ (the nontrivial Dirichlet character modulo $3$), let $\zeta$ be the Riemann zeta
function and let $L(s, \chi)$ be the Dirichlet $L$-function of $\chi$. Then the complex numbers
$1$, $\zeta(2)$ and $L(2, \chi)$ are linearly independent over $\mathbb{Q}$. Moreover, let $m$
and $n$ be integers, neither of them equal to $-1$ or $0$, with $10^6 |m - n| < |n|$, and put
$\ell_m = \log(1 + 1/m)$ and $\ell_n = \log(1 + 1/n)$. Then $\ell_m \ell_n$ is irrational, and if
$m \ne n$, the real numbers $1$, $\ell_m$, $\ell_n$ and $\ell_m \ell_n$ are linearly independent
over $\mathbb{Q}$.

Source: https://arxiv.org/abs/2408.15403 Via leanprover/lean-eval@38361be, problem `cdt_linearIndependent`.
-/
public theorem_wanted cdt_linearIndependent :
    letI χ : ZMod 3 → ℂ := ![0, 1, -1]
    LinearIndependent ℚ ![1, riemannZeta 2, ZMod.LFunction χ 2] ∧
    ∀ m n : ℤ, m ≠ -1 → m ≠ 0 → n ≠ -1 → n ≠ 0 → 10 ^ 6 * |m - n| < |n| →
      letI lm := Real.log (1 + 1 / m)
      letI ln := Real.log (1 + 1 / n)
      Irrational (lm * ln) ∧
      (m ≠ n → LinearIndependent ℚ ![1, lm, ln, lm * ln])

end NumberTheory.CalegariDimitrovTangLinearIndependent

end MathlibExt.NumberTheory.CalegariDimitrovTangLinearIndependentWanted
