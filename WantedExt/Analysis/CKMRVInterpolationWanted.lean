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

/-- **Embedding of the first coordinate axis.** For a positive integer $n$, this is the map
$\mathbb{R} \to \mathbb{R}^n$ sending $r$ to $(r, 0, \dots, 0)$, whose image is the first
coordinate axis. -/
abbrev realIncl {n : ℕ} [NeZero n] (r : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (if · = 0 then r else 0)

/-- **Fourier sample sequences.** Let $n \ge 1$ and $k_0 \ge 0$ be integers, let $f$ be a
complex-valued Schwartz function on $\mathbb{R}^n$ with Fourier transform
$\hat f(\xi) = \int f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$, let $e_1$ be the first
standard basis vector and let $r_k = \sqrt{2k}$. The samples of $f$ are the four complex
sequences indexed by the integers $k \ge k_0$ whose $k$-th terms are, in this order,
$f(r_k e_1)$, $\hat f(r_k e_1)$, the derivative at $r = r_k$ of $r \mapsto f(r e_1)$, and the
derivative at $r = r_k$ of $r \mapsto \hat f(r e_1)$. -/
noncomputable def coeffs (n k₀ : ℕ) [NeZero n]
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (Set.Ici k₀ × Fin 4) → ℂ :=
  Function.uncurry fun k ↦
    let r := Real.sqrt (2 * k)
    let fhat :=
      FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f
    ![f (realIncl r), fhat (realIncl r),
      deriv (f ∘ realIncl) r, deriv (fhat ∘ realIncl) r]

/-- **Rapidly decreasing sequences.** For a natural number $k_0$, a complex sequence
$(a_k)_{k \ge k_0}$ indexed by the integers $k \ge k_0$ is rapidly decreasing if
$k^m |a_k| \to 0$ as $k \to \infty$ for every natural number $m$. -/
def RapidlyDecreasing {k₀ : ℕ} (a : Set.Ici k₀ → ℂ) : Prop :=
  ∀ m : ℕ,
    Tendsto (fun k ↦ (k.1 : ℝ) ^ m * ‖a k‖) atTop (𝓝 0)

/-- **Rapidly decreasing sample quadruples.** For a natural number $k_0$, a family $(a_{k,j})$
of complex numbers indexed by the integers $k \ge k_0$ and $j \in \{0, 1, 2, 3\}$ is a rapidly
decreasing quadruple if each of its four sequences $(a_{k,j})_{k \ge k_0}$ is rapidly
decreasing, that is, $k^m |a_{k,j}| \to 0$ as $k \to \infty$ for every $j$ and every natural
number $m$. -/
def RapidlyDecreasingSamples {k₀ : ℕ}
    (a : (Set.Ici k₀ × Fin 4) → ℂ) : Prop :=
  ∀ j, RapidlyDecreasing fun k ↦ a (k, j)

/-- **Radial Schwartz functions.** For a natural number $n$, this is the set of complex-valued
Schwartz functions $f$ on $\mathbb{R}^n$ that are radial: $f(x) = f(y)$ whenever $|x| = |y|$. -/
abbrev RadialSchwartz (n : ℕ) :=
  {f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) // Radial f}

/-- **Rapidly decreasing sample data.** For a natural number $k_0$, this is the set of families
$(a_{k,j})$ of complex numbers indexed by the integers $k \ge k_0$ and $j \in \{0, 1, 2, 3\}$
whose four sequences $(a_{k,j})_{k \ge k_0}$ are all rapidly decreasing: $k^m |a_{k,j}| \to 0$
as $k \to \infty$ for every $j$ and every natural number $m$. -/
abbrev RapidSampleData (k₀ : ℕ) :=
  {a : (Set.Ici k₀ × Fin 4) → ℂ // RapidlyDecreasingSamples a}

/-- **Radial Fourier interpolation property.** Let $n \ge 1$ and $k_0 \ge 0$ be integers. For a
complex-valued Schwartz function $f$ on $\mathbb{R}^n$, let
$\hat f(\xi) = \int f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$ be its Fourier transform, let
$e_1$ be the first standard basis vector and let $r_k = \sqrt{2k}$. The sampling map from index
$k_0$ sends $f$ to the four complex sequences indexed by the integers $k \ge k_0$ whose $k$-th
terms are $f(r_k e_1)$, $\hat f(r_k e_1)$ and the derivatives at $r = r_k$ of
$r \mapsto f(r e_1)$ and of $r \mapsto \hat f(r e_1)$. Call $f$ radial if $f(x) = f(y)$ whenever
$|x| = |y|$, and call a sequence $(a_k)_{k \ge k_0}$ rapidly decreasing if $k^m |a_k| \to 0$ as
$k \to \infty$ for every natural number $m$. The property $\mathrm{CKMRV}(n, k_0)$ holds when
the sampling map from index $k_0$ is a bijection from the radial Schwartz functions on
$\mathbb{R}^n$ onto the quadruples of rapidly decreasing sequences indexed by $k \ge k_0$.

The bijection is required to be the sampling map itself, so no interpolation basis is hidden
in the definition. -/
def CKMRV (n k₀ : ℕ) [NeZero n] : Prop :=
  ∃ e : RadialSchwartz n ≃ RapidSampleData k₀,
    ∀ f, (e f).1 = coeffs n k₀ f.1

/- **Cohn-Kumar-Miller-Radchenko-Viazovska Fourier interpolation theorem.**
In dimension 8 sampling starts at `sqrt 2`, while in dimension 24 it starts
at radius `2`. In both cases the four sample sequences give a bijection
between radial Schwartz functions and rapidly decreasing data. -/
/-- **Cohn–Kumar–Miller–Radchenko–Viazovska Fourier interpolation theorem.** Let
$(n, k_0)$ be $(8, 1)$ or $(24, 2)$. For a complex-valued Schwartz function $f$ on
$\mathbb{R}^n$, let $\hat f(\xi) = \int f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$ be its
Fourier transform, let $e_1$ be the first standard basis vector and let $r_k = \sqrt{2k}$.
The sampling map sends $f$ to the four complex sequences indexed by the integers $k \ge k_0$
whose $k$-th terms are $f(r_k e_1)$, $\hat f(r_k e_1)$ and the derivatives at $r = r_k$ of
$r \mapsto f(r e_1)$ and of $r \mapsto \hat f(r e_1)$. Call $f$ radial if $f(x) = f(y)$
whenever $|x| = |y|$, and call a sequence $(a_k)_{k \ge k_0}$ rapidly decreasing if
$k^m |a_k| \to 0$ as $k \to \infty$ for every natural number $m$. Then the sampling map is a
bijection from the radial Schwartz functions on $\mathbb{R}^n$ onto the quadruples of rapidly
decreasing sequences indexed by $k \ge k_0$. So sampling starts at radius $\sqrt 2$ in
dimension $8$ and at radius $2$ in dimension $24$.

Source: H. Cohn, A. Kumar, S. D. Miller, D. Radchenko, and M. Viazovska, 'Universal optimality of the E8 and Leech lattices and interpolation formulas', Ann. of Math. 196 (2022), 983-1082, Theorem 1.9, https://doi.org/10.4007/annals.2022.196.3.3. Via leanprover/lean-eval@38361be, problem `ckmrv_fourier_interpolation`. -/
public theorem_wanted ckmrv_fourier_interpolation :
    CKMRV 8 1 ∧ CKMRV 24 2

end Analysis.CKMRVInterpolation

end MathlibExt.Analysis.CKMRVInterpolationWanted
