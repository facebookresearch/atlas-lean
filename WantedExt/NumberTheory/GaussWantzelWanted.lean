/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gauss-Wantzel constructible regular polygon theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.GaussWantzel` — gauss_wantzel_constructible_polygon (manifest `manifests/problems/gauss_wantzel_constructible_polygon.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.GaussWantzelWanted` namespace. Mathematical
statements are unchanged. Source: C. F. Gauss, Disquisitiones Arithmeticae (1801), §365-366; P. L. Wantzel, Recherches sur les moyens de reconnaître si un problème de géométrie peut se résoudre avec la règle et le compas, J. Math. Pures Appl. 1 (1837). Listed as §174 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §174.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.FermatPrime
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.GaussWantzelWanted
namespace NumberTheory.GaussWantzel

/-!
# Gauss-Wantzel constructible polygon theorem

`gauss_wantzel_constructible_polygon`: a regular `n`-gon is
straightedge-and-compass constructible exactly when `n` is a Gauss-Wantzel
integer. Constructibility is encoded by `IsConstructible`, the smallest
subfield of `ℝ` closed under square roots, applied to `cos (2π/n)`; the
arithmetic side `GaussWantzelNumber` requires every odd prime factor to be a
distinct Fermat prime. Mathlib has the algebraic ingredients but no
constructibility theory and no Gauss-Wantzel theorem. Category-(b) candidate
from §174 of the Knill survey.
-/

/-- The real values constructible from rational data by straightedge and
compass: the smallest subfield of `ℝ` closed under square roots. -/
inductive IsConstructible : ℝ → Prop
  | base (q : ℚ) : IsConstructible (q : ℝ)
  | add {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x + y)
  | neg {x : ℝ} : IsConstructible x → IsConstructible (-x)
  | mul {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x * y)
  | inv {x : ℝ} : IsConstructible x → IsConstructible x⁻¹
  | sqrt {x : ℝ} : IsConstructible x → IsConstructible (Real.sqrt x)


/-- The number-theoretic side of the Gauss-Wantzel regular-polygon theorem:
only a power of two may occur with repeated exponent; every odd prime factor
must be a distinct Fermat prime. -/
def GaussWantzelNumber (n : ℕ) : Prop :=
  0 < n ∧
    ∀ p : ℕ, p.Prime → p ∣ n →
      (p = 2 ∨ MetaMathlibExt.IsFermatPrime p) ∧ (p ≠ 2 → ¬ p ^ 2 ∣ n)

/- **Gauss-Wantzel constructible polygon theorem** (§174): a regular `n`-gon
is straightedge-and-compass constructible exactly for the Gauss-Wantzel
integers. -/
/-- Source: C. F. Gauss, Disquisitiones Arithmeticae (1801), §365-366; P. L. Wantzel, Recherches sur les moyens de reconnaître si un problème de géométrie peut se résoudre avec la règle et le compas, J. Math. Pures Appl. 1 (1837). Listed as §174 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §174. Via leanprover/lean-eval@38361be, problem `gauss_wantzel_constructible_polygon`. -/
public theorem_wanted gauss_wantzel_constructible_polygon (n : ℕ) (hn : 3 ≤ n) :
    IsConstructible (Real.cos (2 * Real.pi / n)) ↔ GaussWantzelNumber n

end NumberTheory.GaussWantzel

end MathlibExt.NumberTheory.GaussWantzelWanted
