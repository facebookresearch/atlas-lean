/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ramanujan–Petersson conjecture for the τ-function (Deligne's theorem)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.RamanujanTau` — ramanujan_petersson (manifest `manifests/problems/ramanujan_petersson.toml`, rev 1, submitter Seewoo Lee, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.RamanujanTauWanted` namespace. Mathematical
statements are unchanged. Source: S. Ramanujan, 'On certain arithmetical functions', Trans. Cambridge Philos. Soc. 22 (1916) 159–184. H. Petersson, 'Theorie der automorphen Formen beliebiger reeller Dimension und ihre Darstellung durch eine neue Art Poincaréscher Reihen', Math. Ann. 103 (1930) 369–436. P. Deligne, 'Formes modulaires et représentations ℓ-adiques', Séminaire Bourbaki 1968/69: Exposés 347–363, Lecture Notes in Math. 179, Springer (1971). P. Deligne, 'La conjecture de Weil. I', Publ. Math. IHÉS 43 (1974) 273–307. Background: https://en.wikipedia.org/wiki/Ramanujan%E2%80%93Petersson_conjecture
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.RamanujanTauWanted
namespace NumberTheory
namespace RamanujanTauProblem

/-!
# The Ramanujan–Petersson conjecture for the τ-function (Deligne's theorem)

The Ramanujan τ-function is defined by the Fourier expansion
`Δ = ∑_{n ≥ 1} τ(n) qⁿ` of the modular discriminant
`Δ(z) = η(z)²⁴ = q ∏_{n ≥ 1} (1 - qⁿ)²⁴`, the normalised cusp form of weight
`12` and level `1`. Ramanujan (1916) conjectured that `|τ(p)| ≤ 2 p^(11/2)`
for every prime `p`; Petersson generalised the conjecture to all cusp forms,
and Deligne proved it in 1974 as a consequence of the Weil conjectures.

Here `τ n` is the `n`-th `q`-expansion coefficient of mathlib's
`ModularForm.discriminant`. The coefficients are a priori complex, so the
bound is on the complex norm `‖τ p‖`.
-/

open ModularForm UpperHalfPlane

/-- **Ramanujan τ-function.** For a natural number $n$, $\tau(n)$ is the complex number given by
the coefficient of $q^n$ in the $q$-expansion of the modular discriminant $\Delta = \eta^{24}$,
where $\eta$ is the Dedekind eta function and $q = e^{2\pi i z}$. -/
noncomputable def τ (n : ℕ) : ℂ := (qExpansion 1 discriminant).coeff n

/-- **Normalisation of the Ramanujan τ-function.** The Ramanujan τ-function satisfies
$\tau(1) = 1$: the coefficient of $q$ in the $q$-expansion of the modular discriminant $\Delta$
is $1$. -/
theorem τ_one : τ 1 = 1 := discriminant_qExpansion_coeff_one

/- **The Ramanujan–Petersson conjecture for `τ`** (Ramanujan 1916; proved by
Deligne in 1974). For every prime `p`, `|τ(p)| ≤ 2 p^(11/2)`. -/
/-- **Ramanujan–Petersson conjecture for τ (Deligne's theorem).** For every prime $p$, the
Ramanujan τ-function satisfies $|\tau(p)| \le 2p^{11/2}$, where $|\cdot|$ is the absolute value
of a complex number.

Source: S. Ramanujan, 'On certain arithmetical functions', Trans. Cambridge Philos. Soc. 22 (1916) 159–184. H. Petersson, 'Theorie der automorphen Formen beliebiger reeller Dimension und ihre Darstellung durch eine neue Art Poincaréscher Reihen', Math. Ann. 103 (1930) 369–436. P. Deligne, 'Formes modulaires et représentations ℓ-adiques', Séminaire Bourbaki 1968/69: Exposés 347–363, Lecture Notes in Math. 179, Springer (1971). P. Deligne, 'La conjecture de Weil. I', Publ. Math. IHÉS 43 (1974) 273–307. Background: https://en.wikipedia.org/wiki/Ramanujan%E2%80%93Petersson_conjecture Via leanprover/lean-eval@38361be, problem `ramanujan_petersson`. -/
public theorem_wanted ramanujan_petersson :
    ∀ p : ℕ, Prime p → ‖τ p‖ ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)

end RamanujanTauProblem
end NumberTheory

end MathlibExt.NumberTheory.RamanujanTauWanted
