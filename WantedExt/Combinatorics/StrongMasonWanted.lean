/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strong Mason conjecture for matroid independent sets

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.StrongMason` — strong_mason_conjecture (manifest `manifests/problems/strong_mason_conjecture.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.StrongMasonWanted` namespace. Mathematical
statements are unchanged. Source: P. Branden and J. Huh, 'Lorentzian polynomials', Ann. of Math. 192 (2020), 821-891, Theorem 4.14, https://doi.org/10.4007/annals.2020.192.3.4; independently N. Anari, K. Liu, S. Oveis Gharan, and C. Vinzant, 'Log-concave polynomials III: Mason's ultra-log-concavity conjecture for independent sets of matroids', https://arxiv.org/abs/1811.01600.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.StrongMasonWanted
namespace Combinatorics.StrongMason

/-!
# The strong Mason conjecture

For a finite matroid, let `I k` be the number of independent sets of
cardinality `k`. Mason's strongest conjecture says that the normalized
sequence `I k / (n.choose k)` is log-concave, where `n` is the cardinality
of the ground set. Branden and Huh proved this using Lorentzian polynomials;
Anari, Liu, Oveis Gharan, and Vinzant obtained the result independently.

Mathlib supplies the matroid axioms and their independent-set API. The
inequality below clears the binomial denominators, so it can be stated
entirely in `Nat`.
-/

/-- **Number of independent sets of a given size.** For a finite matroid $M$ and a natural
number $k$, this is the number of independent sets of $M$ with exactly $k$ elements. -/
noncomputable def independentSetCount {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) : ℕ :=
  {I ∈ Set.powersetCard α k | M.Indep I}.ncard

/- **The strong Mason conjecture** (Branden-Huh; independently
Anari-Liu-Oveis Gharan-Vinzant). If `I k` counts the independent sets of
size `k` in a finite matroid on `n` elements, then

`I k ^ 2 * k * (n - k) >= I (k - 1) * I (k + 1) * (k + 1) * (n - k + 1)`.

Equivalently, `I k / n.choose k` is a log-concave sequence. -/
/-- **The strong Mason conjecture.** Let $M$ be a finite matroid whose ground set has $n$
elements, and for each $j$ let $I_j$ be the number of independent sets of $M$ with $j$ elements.
Then for every natural number $k$ with $0 < k < n$,
$$I_{k-1} \, I_{k+1} \, (k+1) \, (n-k+1) \le I_k^2 \, k \, (n-k).$$

Equivalently, the sequence $I_k / \binom{n}{k}$ is log-concave for $0 \le k \le n$.

Source: P. Branden and J. Huh, 'Lorentzian polynomials', Ann. of Math. 192 (2020), 821-891, Theorem 4.14, https://doi.org/10.4007/annals.2020.192.3.4; independently N. Anari, K. Liu, S. Oveis Gharan, and C. Vinzant, 'Log-concave polynomials III: Mason's ultra-log-concavity conjecture for independent sets of matroids', https://arxiv.org/abs/1811.01600. Via leanprover/lean-eval@38361be, problem `strong_mason_conjecture`. -/
public theorem_wanted strong_mason_conjecture {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) *
          (k + 1) * (M.E.ncard - k + 1) ≤
      independentSetCount M k ^ 2 * k * (M.E.ncard - k)

end Combinatorics.StrongMason

end MathlibExt.Combinatorics.StrongMasonWanted
