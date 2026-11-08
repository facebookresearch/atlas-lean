/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fourier interpolation in dimensions 8 and 24

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.CKMRVInterpolation` — ckmrv_fourier_interpolation (manifest `manifests/problems/ckmrv_fourier_interpolation.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.CKMRVInterpolationWanted` namespace. Mathematical
statements are unchanged. Source: H. Cohn, A. Kumar, S. D. Miller, D. Radchenko, and M. Viazovska, 'Universal optimality of the E8 and Leech lattices and interpolation formulas', Ann. of Math. 196 (2022), 983-1082, Theorem 1.9, https://doi.org/10.4007/annals.2022.196.3.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.CKMRVInterpolationWanted
namespace Analysis.CKMRVInterpolation

/-!
# Fourier interpolation in dimensions 8 and 24

Cohn, Kumar, Miller, Radchenko, and Viazovska proved that a radial Schwartz
function on `R^8` or `R^24` is determined by the values and radial derivatives
of the function and its Fourier transform at the nonzero vector lengths of
the `E8` or Leech lattice. More strongly, every four rapidly decreasing
sequences occur uniquely as these samples.

The equivalence in `CKMRV` is pinned to the sampling map itself, so the
statement does not hide interpolation basis functions in trusted definitions.
-/

open Filter Topology
open scoped FourierTransform SchwartzMap

/-- A function is radial if it takes the same value at points with the same norm. -/
def Radial {E F : Type*} [Norm E] (f : E → F) : Prop :=
  ∀ e e' : E, ‖e‖ = ‖e'‖ → f e = f e'

/-- Inclusion of a coordinate axis into Euclidean space. -/
abbrev realIncl {n : ℕ} [NeZero n] (r : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (if · = 0 then r else 0)

/-- The four sample sequences: values of `f` and its Fourier transform,
followed by their radial derivatives, at radii `sqrt (2 * k)`. -/
noncomputable def coeffs (n k₀ : ℕ) [NeZero n]
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (Set.Ici k₀ × Fin 4) → ℂ :=
  Function.uncurry fun k ↦
    let r := Real.sqrt (2 * k)
    let fhat :=
      FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f
    ![f (realIncl r), fhat (realIncl r),
      deriv (f ∘ realIncl) r, deriv (fhat ∘ realIncl) r]

/-- A complex sequence indexed by integers at least `k₀` is rapidly decreasing
if multiplication by every natural power of the index still tends to zero. -/
def RapidlyDecreasing {k₀ : ℕ} (a : Set.Ici k₀ → ℂ) : Prop :=
  ∀ m : ℕ,
    Tendsto (fun k ↦ (k.1 : ℝ) ^ m * ‖a k‖) atTop (𝓝 0)

/-- Four rapidly decreasing sample sequences. -/
def RapidlyDecreasingSamples {k₀ : ℕ}
    (a : (Set.Ici k₀ × Fin 4) → ℂ) : Prop :=
  ∀ j, RapidlyDecreasing fun k ↦ a (k, j)

/-- Radial complex-valued Schwartz functions on `R^n`. -/
abbrev RadialSchwartz (n : ℕ) :=
  {f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) // Radial f}

/-- Four rapidly decreasing complex sample sequences indexed from `k₀`. -/
abbrev RapidSampleData (k₀ : ℕ) :=
  {a : (Set.Ici k₀ × Fin 4) → ℂ // RapidlyDecreasingSamples a}

/-- The full Fourier sampling isomorphism with dimension and starting index
as parameters. The equivalence is required to be the sampling map `coeffs`. -/
def CKMRV (n k₀ : ℕ) [NeZero n] : Prop :=
  ∃ e : RadialSchwartz n ≃ RapidSampleData k₀,
    ∀ f, (e f).1 = coeffs n k₀ f.1

/- **Cohn-Kumar-Miller-Radchenko-Viazovska Fourier interpolation theorem.**
In dimension 8 sampling starts at `sqrt 2`, while in dimension 24 it starts
at radius `2`. In both cases the four sample sequences give a bijection
between radial Schwartz functions and rapidly decreasing data. -/
/-- Source: H. Cohn, A. Kumar, S. D. Miller, D. Radchenko, and M. Viazovska, 'Universal optimality of the E8 and Leech lattices and interpolation formulas', Ann. of Math. 196 (2022), 983-1082, Theorem 1.9, https://doi.org/10.4007/annals.2022.196.3.3. Via leanprover/lean-eval@38361be, problem `ckmrv_fourier_interpolation`. -/
public theorem_wanted ckmrv_fourier_interpolation :
    CKMRV 8 1 ∧ CKMRV 24 2

end Analysis.CKMRVInterpolation

end MathlibExt.Analysis.CKMRVInterpolationWanted
