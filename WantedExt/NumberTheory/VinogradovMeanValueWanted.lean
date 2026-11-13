/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Vinogradov mean value theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.VinogradovMeanValue` — vinogradov_mean_value (manifest `manifests/problems/vinogradov_mean_value.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.VinogradovMeanValueWanted` namespace. Mathematical
statements are unchanged. Source: J. Bourgain, C. Demeter, and L. Guth, `Proof of the main conjecture in Vinogradov's Mean Value Theorem for degrees higher than three`, Ann. of Math. 184 (2) 2016, 633–682; T. D. Wooley, `Nested efficient congruencing and relatives of Vinogradov's mean value theorem`, Proc. London Math. Soc. 118 (4) 2019, 942–1016.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.VinogradovMeanValueWanted
/-!
# Vinogradov mean value theorem

https://en.wikipedia.org/wiki/Vinogradov%27s_mean-value_theorem

Given integers `s, k ≥ 1`, let J_{s,k}(X) denote the number of integral solutions to the system of
`k` equations `x₁ʲ + … + xₛʲ = y₁ʲ + … + yₛʲ` with `1 ≤ xᵢ, yᵢ ≤ X` for `i = 1, …, s`.
Then J_{s,k}(X) ≪ X^ε(X^s + X^{2s-k(k+1)/2}) for every ε > 0.

This was proved by Jean Bourgain, Ciprian Demeter, and Larry Guth and by a different method
by Trevor Wooley.

## References

Lillian B. Pierce. The Vinogradov Mean Value Theorem [after Wooley, and Bourgain, Demeter and Guth].
https://arxiv.org/abs/1707.00119

Bourgain, Jean; Demeter, Ciprian; Guth, Larry (2016).
"Proof of the main conjecture in Vinogradov's Mean Value Theorem for degrees higher than three".
Ann. of Math. 184 (2): 633–682. arXiv:1512.01565. doi:10.4007/annals.2016.184.2.7.

Wooley, Trevor D. (2019). "Nested efficient congruencing and relatives of Vinogradov's mean value theorem".
Proceedings of the London Mathematical Society. 118 (4): 942–1016. arXiv:1708.01220. doi:10.1112/plms.12204.
-/

namespace NumberTheory.VinogradovMeanValue

/-- **The Vinogradov mean value count.** For natural numbers $s$, $k$ and $X$, $J_{s,k}(X)$ is the
number of pairs of tuples $(x_1, \dots, x_s)$ and $(y_1, \dots, y_s)$ of integers in
$\{1, \dots, X\}$ such that $x_1^j + \dots + x_s^j = y_1^j + \dots + y_s^j$ for every natural
number $j \le k$, regarded as a real number. -/
def J (s k X : ℕ) : ℝ :=
  Finset.card {(x, y) : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X) |
    ∀ j ≤ k, ∑ i, (x i).1 ^ j = ∑ i, (y i).1 ^ j}

/-- **Vinogradov's mean value theorem.** For all natural numbers $s$ and $k$ and every real
$\varepsilon > 0$ there is a constant $C$ such that
$J_{s,k}(X) \le C (X^{s + \varepsilon} + X^{2s - k(k+1)/2 + \varepsilon})$ for all sufficiently
large natural numbers $X$, where $J_{s,k}(X)$ is the number of pairs of tuples
$(x_1, \dots, x_s)$ and $(y_1, \dots, y_s)$ of integers in $\{1, \dots, X\}$ with
$x_1^j + \dots + x_s^j = y_1^j + \dots + y_s^j$ for every natural number $j \le k$.

Source: J. Bourgain, C. Demeter, and L. Guth, `Proof of the main conjecture in Vinogradov's Mean Value Theorem for degrees higher than three`, Ann. of Math. 184 (2) 2016, 633–682; T. D. Wooley, `Nested efficient congruencing and relatives of Vinogradov's mean value theorem`, Proc. London Math. Soc. 118 (4) 2019, 942–1016. Via leanprover/lean-eval@38361be, problem `vinogradov_mean_value`. -/
public theorem_wanted vinogradov_mean_value (s k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    J s k =O[Filter.atTop]
      fun X ↦ (X ^ (s + ε) + X ^ ((2 * s : ℝ) - k * (k + 1) / 2 + ε) : ℝ)

end NumberTheory.VinogradovMeanValue

end MathlibExt.NumberTheory.VinogradovMeanValueWanted
