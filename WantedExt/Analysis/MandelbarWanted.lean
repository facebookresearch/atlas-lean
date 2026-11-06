/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mandelbar (tricorn) is not path-connected (Hubbard–Schleicher)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ComplexAnalysis.Mandelbar` — mandelbar_not_path_connected (manifest `manifests/problems/mandelbar_not_path_connected.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.MandelbarWanted` namespace. Mathematical
statements are unchanged. Source: John H. Hubbard and Dierk Schleicher, *Multicorns are not Path Connected*, arXiv:1209.1753 (2012); published in *Frontiers in Complex Dynamics* (Princeton University Press, 2014), pp. 73-102. Listed as §62 (additional statement 2) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.MandelbarWanted
namespace ComplexAnalysis

/-!
# Mandelbar (tricorn) is not path-connected

The `d = 2` case of Hubbard–Schleicher's theorem that multicorns — the
connectedness loci of unicritical antiholomorphic polynomials
`z ↦ z̄^d + c` — are not path-connected for `d ≥ 2`. For `d = 2` the
multicorn is the mandelbar / tricorn, the connectedness locus of
`z ↦ z̄² + c`.

Knill lists this as §62 additional statement 2 but writes the iterator
as `z ↦ z̄ + c` (degree 1). That literal map has bounded critical orbit
iff `Re c = 0`, so its connectedness locus is the imaginary axis —
path-connected, contradicting the claim. The formal statement here
uses the standard quadratic antiholomorphic family `z ↦ z̄² + c`.
-/

open Function

/-- **The antiholomorphic quadratic map.** For $c \in \mathbb{C}$, the map
$T_c : \mathbb{C} \to \mathbb{C}$ is $T_c(z) = \bar z^2 + c$, where $\bar z$ is the complex
conjugate of $z$. -/
def Tantibar (c : ℂ) (z : ℂ) : ℂ := (starRingEnd ℂ z) ^ 2 + c

/-- **The Mandelbar set (tricorn).** The Mandelbar set is the set of $c \in \mathbb{C}$ for which
the orbit of $0$ under the map $T_c(z) = \bar z^2 + c$ is bounded: there is a real number $M$
with $|T_c^n(0)| \le M$ for all $n \ge 0$, where $T_c^n$ is the $n$-th iterate of $T_c$ and
$T_c^0$ is the identity.

This set is the connectedness locus of the family $z \mapsto \bar z^2 + c$. -/
def Mandelbar : Set ℂ :=
  { c : ℂ | ∃ M : ℝ, ∀ n : ℕ, ‖(Tantibar c)^[n] 0‖ ≤ M }

/- **The mandelbar (tricorn) is not path-connected** (Hubbard–Schleicher). -/
/-- **The Mandelbar set is not path-connected.** The Mandelbar set (tricorn), the set of
$c \in \mathbb{C}$ for which the orbit of $0$ under $z \mapsto \bar z^2 + c$ is bounded, is not
path-connected.

This is the degree-2 case of the Hubbard–Schleicher theorem that multicorns are not
path-connected.

Source: John H. Hubbard and Dierk Schleicher, *Multicorns are not Path Connected*, arXiv:1209.1753 (2012); published in *Frontiers in Complex Dynamics* (Princeton University Press, 2014), pp. 73-102. Listed as §62 (additional statement 2) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `mandelbar_not_path_connected`. -/
public theorem_wanted mandelbar_not_path_connected : ¬ IsPathConnected Mandelbar

end ComplexAnalysis

end MathlibExt.Analysis.MandelbarWanted
