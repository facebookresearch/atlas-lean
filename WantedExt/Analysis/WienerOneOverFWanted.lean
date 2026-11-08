/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wiener's 1/f theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.WienerOneOverF` — wiener_inverse_closed (manifest `manifests/problems/wiener_inverse_closed.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.WienerOneOverFWanted` namespace. Mathematical
statements are unchanged. Source: N. Wiener, Tauberian theorems, Ann. of Math. 33 (1932), 1-100. Listed as §226 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §226.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.WienerOneOverFWanted
namespace Analysis.WienerOneOverF

/-!
# Wiener's `1/f` theorem

§226 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Wiener's
lemma for the circle algebra: if a continuous function on the circle has
absolutely summable Fourier coefficients and is nowhere zero, then its
pointwise inverse again has absolutely summable Fourier coefficients.

mathlib has the additive circle, the Fourier characters `fourier`, Fourier
coefficients `fourierCoeff`, and `hasSum_fourier_series_of_summable`, but not
the Wiener algebra or the spectral-invariance theorem.
-/

open Set
open scoped ComplexConjugate Real

noncomputable section

variable {T : ℝ} [Fact (0 < T)]

/-- The Wiener-algebra predicate on the additive circle: a continuous
complex-valued function whose Fourier coefficients are absolutely summable.
For complex series, `Summable` is equivalent to absolute summability of the
norms. -/
def InWienerAlgebra (f : C(AddCircle T, ℂ)) : Prop :=
  Summable (fourierCoeff f)

/- **Wiener's `1/f` theorem.** If a function on the circle belongs to the
Wiener algebra and has no zero on the circle, then its pointwise reciprocal
again belongs to the Wiener algebra. -/
/-- Source: N. Wiener, Tauberian theorems, Ann. of Math. 33 (1932), 1-100. Listed as §226 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §226. Via leanprover/lean-eval@38361be, problem `wiener_inverse_closed`. -/
public theorem_wanted wiener_inverse_closed (f : C(AddCircle T, ℂ))
    (hf : InWienerAlgebra f) (hzero : ∀ x, f x ≠ 0) :
    ∃ g : C(AddCircle T, ℂ),
      (∀ x, g x = (f x)⁻¹) ∧ InWienerAlgebra g

end

end Analysis.WienerOneOverF

end MathlibExt.Analysis.WienerOneOverFWanted
