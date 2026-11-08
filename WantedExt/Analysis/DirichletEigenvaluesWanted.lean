/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dirichlet eigenvalues of -y'' = lambda y on [0,pi] are n^2

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.ODE.DirichletEigenvalues` — dirichlet_eigenvalues_eq_nat_sq (manifest `manifests/problems/dirichlet_eigenvalues_eq_nat_sq.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.DirichletEigenvaluesWanted` namespace. Mathematical
statements are unchanged. Source: Classical Sturm-Liouville theory.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

namespace MathlibExt.Analysis.DirichletEigenvaluesWanted
namespace Analysis
namespace ODE

open scoped Real

/-!
Dirichlet eigenvalues of `-y'' = λ y` on `[0, π]`.

A nontrivial `C²` solution `y` (defined on some open interval `J` containing `[0, π]`)
of `-y''(x) = λ y(x)` with `y 0 = y π = 0` exists **iff** `λ = n²` for some positive
natural number `n`.

The "if" direction is straightforward (`sin (n · x)` works). The "only if" direction is
the substantive content: it requires casing on the sign of `λ` and ruling out `λ < 0`
(only the zero solution; uses `sinh`/`cosh` linear independence) and `λ = 0` (only the
zero solution), and for `λ > 0` showing that `√λ` must be a positive integer.
-/

/- **Dirichlet eigenvalue characterization.** A real `λ` is a Dirichlet eigenvalue of
`-y'' = λ y` on `[0, π]` (i.e. there is a nontrivial `C²` solution on some open interval
containing `[0, π]`, vanishing at both endpoints) iff `λ = n²` for some positive natural
number `n`. -/
/-- Source: Classical Sturm-Liouville theory. Via leanprover/lean-eval@38361be, problem `dirichlet_eigenvalues_eq_nat_sq`. -/
public theorem_wanted dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2

end ODE
end Analysis

end MathlibExt.Analysis.DirichletEigenvaluesWanted
