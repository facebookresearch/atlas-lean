/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pointwise and Cesàro convergence of Fourier series (Dirichlet, Fejér)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.FourierConvergence` — fourier_dirichlet_fejer (manifest `manifests/problems/fourier_dirichlet_fejer.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.FourierConvergenceWanted` namespace. Mathematical
statements are unchanged. Source: P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.FourierConvergenceWanted
namespace Analysis

/-!
# Pointwise and Cesàro convergence of Fourier series

§46 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Dirichlet's pointwise convergence theorem** (main): for a `C¹` 2π-periodic
  complex function `f`, the symmetric Fourier partial sums
  `S_N(f)(x) = ∑_{n = -N}^{N} f̂_n e^{inx}` converge to `f(x)` at every `x ∈ ℝ`.
* **Fejér's theorem** (additional): for a merely *continuous* 2π-periodic `f`,
  the Cesàro means `σ_N(f) = (S_0 + ⋯ + S_N)/(N+1)` of the partial sums converge
  to `f` uniformly on `ℝ`.

mathlib has the circle, the Fourier characters, `fourierCoeffOn`, the `L²`
Fourier series, and uniform convergence under `ℓ¹`-summability
(`hasSum_fourier_series_of_summable`). It has neither the Dirichlet kernel nor
the statement that `C¹` forces pointwise convergence of the symmetric partial
sums — the `C¹` bound `|f̂_n| ≤ C/n` is not `ℓ¹`-summable, so the summable case
does not apply. The
symmetric partial-sum order `Finset.Icc (-N) N` is essential, since the Fourier
series of a `C¹` function need not converge absolutely.

`MathlibExt/Analysis/Fourier/AddCircle/FejerTheorem.lean` supplies the Fejér
kernel, Cesàro–Fourier means, and uniform convergence on `AddCircle T`.
The circle and real-line Fourier-coefficient interfaces use the same symmetric
partial-sum order and `N + 1` normalization. Transport from the circle interface
requires descending a continuous periodic function to `AddCircle (2 * Real.pi)`,
identifying `fourierCoeffOn` and the exponential modes with the circle coefficients
and modes, and pulling uniform convergence back to `ℝ`. This catalogue does not
supply those interface bridges.
-/

open Filter Topology

/-- **Symmetric Fourier partial sums.** For $f \colon \mathbb{R} \to \mathbb{C}$, a natural number
$N$ and $x \in \mathbb{R}$, the $N$-th symmetric Fourier partial sum of $f$ at $x$ is
$S_N(f)(x) = \sum_{n=-N}^{N} \hat f_n e^{inx}$, where
$\hat f_n = \frac{1}{2\pi} \int_0^{2\pi} e^{-int} f(t)\,dt$ is the $n$-th Fourier coefficient of $f$
on the interval $[0, 2\pi]$. -/
noncomputable def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))

/-- **Cesàro means of Fourier series.** For $f \colon \mathbb{R} \to \mathbb{C}$, a natural number
$N$ and $x \in \mathbb{R}$, the $N$-th Cesàro mean of the Fourier series of $f$ at $x$ is the
average of the first $N + 1$ symmetric Fourier partial sums,
$\sigma_N(f)(x) = \frac{1}{N+1} \sum_{k=0}^{N} S_k(f)(x)$, where
$S_k(f)(x) = \sum_{n=-k}^{k} \hat f_n e^{inx}$ and
$\hat f_n = \frac{1}{2\pi} \int_0^{2\pi} e^{-int} f(t)\,dt$ is the $n$-th Fourier coefficient of
$f$ on the interval $[0, 2\pi]$. -/
noncomputable def fourierCesaroMean (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ k ∈ Finset.range (N + 1), fourierPartialSum f k x) / (N + 1 : ℂ)

/- **Dirichlet's pointwise convergence theorem** (§46). For every `C¹`
2π-periodic complex function `f`, the symmetric Fourier partial sums `S_N(f)(x)`
converge to `f(x)` at every point `x ∈ ℝ`. -/
/-- **Dirichlet's theorem on pointwise convergence of Fourier series.** Let
$f \colon \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and continuously differentiable, and for
$n \in \mathbb{Z}$ let $\hat f_n = \frac{1}{2\pi} \int_0^{2\pi} e^{-int} f(t)\,dt$ be the $n$-th
Fourier coefficient of $f$ on $[0, 2\pi]$. Then for every $x \in \mathbb{R}$ the symmetric Fourier
partial sums $S_N(f)(x) = \sum_{n=-N}^{N} \hat f_n e^{inx}$ converge to $f(x)$ as $N \to \infty$.

Source: P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `fourier_dirichlet_fejer`. -/
public theorem_wanted dirichlet_pointwise
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hC1 : ContDiff ℝ 1 f)
    (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x))

/- **Fejér's theorem** (§46). For every *continuous* 2π-periodic complex
function `f` — without the `C¹` hypothesis of Dirichlet's theorem — the Cesàro
means `σ_N(f)` of the symmetric Fourier partial sums converge to `f` uniformly
on `ℝ`. -/
/-- **Fejér's theorem.** Let $f \colon \mathbb{R} \to \mathbb{C}$ be continuous and
$2\pi$-periodic, and write $S_k(f)$ for the $k$-th symmetric Fourier partial sum of $f$. Then the
Cesàro means $\sigma_N(f) = (S_0(f) + S_1(f) + \dots + S_N(f)) / (N + 1)$ converge to $f$
uniformly on $\mathbb{R}$ as $N \to \infty$.

Source: P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `fourier_dirichlet_fejer`. -/
public theorem_wanted fejer
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean f N) f atTop

end Analysis

end MathlibExt.Analysis.FourierConvergenceWanted
