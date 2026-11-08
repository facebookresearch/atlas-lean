/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Symplectic monodromy at radius zero and equimultiplicity of μ-constant families

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.SymplecticMonodromy` — annals_symplectic_monodromy (manifest `manifests/problems/annals_symplectic_monodromy.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.SymplecticMonodromyWanted` namespace. Mathematical
statements are unchanged. Source: J. Fernández de Bobadilla and T. Pełka, `Symplectic monodromy at radius zero and equimultiplicity of μ-constant families`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-SymplecticMonodromy.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.Topology.UnitInterval

@[expose] public section

namespace MathlibExt.Geometry.SymplecticMonodromyWanted
/-!
# Main Statement from Symplectic monodromy at radius zero and equimultiplicity of
# μ-constant families

We formalise the statement of the main result from J. Fernández de Bobadilla and T. Pełka,
`Symplectic monodromy at radius zero and equimultiplicity of μ-constant families`,
Annals of Math, 200 (1) 2024.
-/

set_option autoImplicit false

namespace SymplecticMonodromy

open MvPowerSeries

/-- The Milnor number of `f` is `dim_ℂ ℂ⟦z₁, ⋯, zₙ⟧ / ⟨∂f/∂z₁, ⋯, ∂f/∂zₙ⟩`. -/
noncomputable def milnorNumber {σ R : Type*} [CommRing R] (f : MvPowerSeries σ R) : ℕ∞ :=
  (Module.rank R (MvPowerSeries σ R ⧸ Ideal.span (Set.range (pderiv · f)))).toENat

/--
Statement of Theorem 1.1:

Let `(fₜ)` be a continuous family of power series. If the Milnor number `μ(fₜ)` is independent
of `t` and finite, then the multiplicity `ν(fₜ)` is also independent of `t`.

Note that what the paper calls "multiplicity" is exactly `MvPowerSeries.order`; see
for instance `MvPowerSeries.order_eq_nat`.

Even though not explicitly mentioned by the paper, we need to require the constant coefficients
to vanish. This is equivalent to saying that `fₜ` is a germ `(ℂⁿ, 0) → (ℂ, 0)`, i.e. that it's
a family of isolated hypersurface singularities through the origin, which is mentioned both in the
abstract and in Corollary 1.3, but not explicitly in Theorem 1.1. For an example showing that we
need this assumption, consider `fₜ = z + t`: The Milnor number is `0` for all `t` (the Jacobian quotient is the zero module since the derivative ideal contains `1`), but
`order(f₀) = 1` while `order(f₁) = 0`.
Source: J. Fernández de Bobadilla and T. Pełka, `Symplectic monodromy at radius zero and equimultiplicity of μ-constant families`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-SymplecticMonodromy.lean Via leanprover/lean-eval@38361be, problem `annals_symplectic_monodromy`.
-/
public theorem_wanted theorem_1_1 (n : ℕ) (f : unitInterval → MvPowerSeries (Fin n) ℂ)
    (cont : ∀ d, Continuous fun t ↦ coeff d (f t)) (h_const : ∀ t, constantCoeff (f t) = 0)
    (h : ∃ μ : ℕ, ∀ t, milnorNumber (f t) = μ) : ∀ t₁ t₂, (f t₁).order = (f t₂).order

end SymplecticMonodromy

end MathlibExt.Geometry.SymplecticMonodromyWanted
