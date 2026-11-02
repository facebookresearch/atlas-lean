/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Avila-Jitomirskaya Ten Martini Problem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.TenMartini` — ten_martini_problem (manifest `manifests/problems/ten_martini_problem.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.TenMartiniWanted` namespace. Mathematical
statements are unchanged. Source: A. Avila and S. Jitomirskaya, 'The Ten Martini Problem', Ann. of Math. 170 (2009), 303-342, https://doi.org/10.4007/annals.2009.170.303.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.TenMartiniWanted
namespace Analysis.TenMartini

/-!
# The Ten Martini Problem

Avila and Jitomirskaya proved that the spectrum of the almost Mathieu
operator is a Cantor set for every irrational frequency and every nonzero
coupling constant.

The operator acts on `l^2(Z)` by

`(H u)(n) = u(n+1) + u(n-1) + 2 lambda cos(2 pi (theta + n alpha)) u(n)`.

We specify this coordinate formula transparently and ask for construction of
the bounded operator as part of the theorem, so the spectral conclusion does
not rest on an existence hypothesis.
-/

open Set

/-- **The sequence space $\ell^2(\mathbb{Z})$.** We write $\ell^2(\mathbb{Z})$ for the Hilbert
space of square-summable sequences $(u_n)_{n \in \mathbb{Z}}$ of complex numbers. -/
abbrev EllTwo : Type := lp (fun _ : ℤ => ℂ) 2

/-- **Almost Mathieu operator.** Let $\alpha$, $\lambda$ and $\theta$ be real numbers. A bounded
complex-linear operator $H$ on $\ell^2(\mathbb{Z})$ is an almost Mathieu operator with frequency
$\alpha$, coupling $\lambda$ and phase $\theta$ when, for every $u \in \ell^2(\mathbb{Z})$ and
every $n \in \mathbb{Z}$,

$$(Hu)(n) = u(n+1) + u(n-1) + 2\lambda \cos(2\pi(\theta + n\alpha))\, u(n).$$
-/
def IsAlmostMathieuOperator (α coupling θ : ℝ) (H : EllTwo →L[ℂ] EllTwo) : Prop :=
  ∀ (u : EllTwo) (n : ℤ),
    H u n =
      u (n + 1) + u (n - 1) +
        ((2 * coupling * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α) : ℝ) : ℂ) * u n)

/- **Avila-Jitomirskaya Ten Martini theorem.** For irrational frequency
and nonzero coupling, the spectrum of the almost Mathieu operator is a
Cantor set. Here this means nonempty, compact, perfect, and totally
disconnected. -/
/-- **Ten Martini theorem (Avila–Jitomirskaya).** Let $\alpha$, $\lambda$ and $\theta$ be real
numbers with $\alpha$ irrational and $\lambda \neq 0$. Then there is an almost Mathieu operator $H$
on $\ell^2(\mathbb{Z})$ with frequency $\alpha$, coupling $\lambda$ and phase $\theta$, and the
spectrum of $H$ is nonempty, compact, perfect and totally disconnected, that is, a Cantor set.

Source: A. Avila and S. Jitomirskaya, 'The Ten Martini Problem', Ann. of Math. 170 (2009), 303-342, https://doi.org/10.4007/annals.2009.170.303. Via leanprover/lean-eval@38361be, problem `ten_martini_problem`. -/
public theorem_wanted ten_martini_problem (α coupling θ : ℝ)
    (hα : Irrational α) (hcoupling : coupling ≠ 0) :
    ∃ H : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α coupling θ H ∧
        (spectrum ℂ H).Nonempty ∧
        IsCompact (spectrum ℂ H) ∧
        Perfect (spectrum ℂ H) ∧
        IsTotallyDisconnected (spectrum ℂ H)

end Analysis.TenMartini

end MathlibExt.Analysis.TenMartiniWanted
