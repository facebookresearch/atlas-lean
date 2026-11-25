/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Fourier series coefficient

Retained definition for concept `Fourier series coefficient`
(`jis_sem_e469cc9709bc61c7d3368fdf`), required clause from statement
`jis_730fbe152ebd86322427d06f`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fourier coefficients of the Mathieu–Fibonacci periodic function.** Let
$\varphi = (1 + \sqrt{5}) / 2$ be the golden ratio. For each natural number $n \ge 1$, the $n$-th
coefficient is the real number
$c_n = (2 / \log \varphi) \, |\Gamma(1 + 2 n \pi i / \log \varphi)|^2$, where $\Gamma$ is the
complex Gamma function.

In the source, these are the coefficients of the cosine series
$H(x) = 1 + \sum_{n \ge 1} c_n \cos(4 n \pi x / \log \varphi)$ of a periodic function $H$.

Source: concept `Fourier series coefficient` (`jis_sem_e469cc9709bc61c7d3368fdf`);
required clause from statement `jis_730fbe152ebd86322427d06f`. -/
public noncomputable def mathieuFibonacciFourierCoefficient (n : {n : ℕ // 1 ≤ n}) : ℝ :=
  (2 / Real.log ((1 + Real.sqrt 5) / 2)) *
    ‖Complex.Gamma (1 + 2 * (n.val : ℂ) * (Real.pi : ℂ) * Complex.I /
      (Real.log ((1 + Real.sqrt 5) / 2) : ℂ))‖ ^ 2

end

end MetaMathlibExt
