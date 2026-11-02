/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Baker-Wüstholz theorem on linear forms in logarithms

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.BakerWustholz` — bakerWustholz_linearForms_logs (manifest `manifests/problems/bakerWustholz_linearForms_logs.toml`, rev 1, submitter Ralf Stephan, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.BakerWustholzWanted` namespace. Mathematical
statements are unchanged. Source: A. Baker, G. Wüstholz, Logarithmic forms and group varieties, J. reine angew. Math. 442 (1993), 19-62.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

namespace MathlibExt.NumberTheory.BakerWustholzWanted
/-!
# The Baker–Wüstholz theorem on linear forms in logarithms

Reference: A. Baker and G. Wüstholz, *Logarithmic forms and group varieties*,
J. reine angew. Math. **442** (1993), 19–62. In particular, their "main theorem"
is a refinement of the 1966-68 Baker bound, with the outer exponent on `log B`
essentially `1` rather than `(2n+1)²`.

## Statement conventions

* `α₁, …, αₙ` are nonzero elements of a number field `K`. We work through a
  ring-hom embedding `φ : K →+* ℂ`, and use `Complex.log` (principal branch)
  for the logs of the images.
* `d := Module.finrank ℚ K` is the field degree.
* `h(α) := Height.logHeight₁ α / d` is the **normalized** logarithmic Weil
  height. (Mathlib's `logHeight₁` is the unnormalized product-over-places
  sum; dividing by `d` gives the classical absolute height.)
* `h'(α) := max(h(α), |log φ(α)| / d, 1 / d)` is the **modified height** used
  by Baker–Wüstholz. The extra terms handle the case where `α` is very close
  to 1 (so `h(α)` is small) or where the chosen log determination is large.
* `B := max(|b₁|, …, |bₙ|, 2)` is the maximum coefficient (clamped to 2 so
  `log B > 0`).
* `C(n, d) := 18 · (n + 1)! · n^(n+1) · (32d)^(n+2) · log(2nd)` is the
  Baker–Wüstholz constant.
-/

open Complex

namespace BakerWustholz

/-- **The Baker–Wüstholz constant.** For natural numbers $n$ and $d$, the Baker–Wüstholz constant
is the real number
$C(n, d) = 18 \cdot (n + 1)! \cdot n^{n+1} \cdot (32 d)^{n+2} \cdot \log(2nd)$. -/
noncomputable def C (n d : ℕ) : ℝ :=
  18 * (n + 1).factorial * (n : ℝ) ^ (n + 1) *
    (32 * (d : ℝ)) ^ (n + 2) * Real.log (2 * n * d)

/-- **Modified height.** Let $K$ be a number field of degree $d = [K : \mathbb{Q}]$ and let
$\varphi : K \to \mathbb{C}$ be a ring homomorphism. For $\alpha \in K$, the modified height of
$\alpha$ with respect to $\varphi$ is
$$h'(\alpha) = \max\left(h(\alpha), \frac{|\log \varphi(\alpha)|}{d}, \frac{1}{d}\right),$$
where $\log$ is the principal branch of the complex logarithm (with $\log 0 = 0$) and $h(\alpha)$
is the absolute logarithmic Weil height of $\alpha$: $\frac{1}{d}$ times the sum of
$\log \max(1, |\alpha|_v)$ over the places $v$ of $K$, with the absolute values normalized so that
the product formula holds and each complex place counted twice. -/
noncomputable def modifiedHeight
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (α : K) : ℝ :=
  let d : ℝ := Module.finrank ℚ K
  max (Height.logHeight₁ α / d) (max (‖Complex.log (φ α)‖ / d) (1 / d))

end BakerWustholz

/- **Baker–Wüstholz theorem on linear forms in logarithms**, effective form.

Reference: A. Baker, G. Wüstholz, *Logarithmic forms and group varieties*,
J. reine angew. Math. **442** (1993), 19–62.

Let `α₁, …, αₙ` (with `1 ≤ n`) be nonzero elements of a number field `K` of
degree `d := Module.finrank ℚ K`, embedded in `ℂ` via `φ`. Let `b₁, …, bₙ`
be rational integers with `|bᵢ| ≤ B` and `B ≥ 2`. If the linear form
`Λ := ∑ᵢ bᵢ · log (φ (αᵢ))` (complex log, principal branch) is nonzero,
then
`log |Λ| ≥ -C(n, d) · max(log B, 1/d) · ∏ᵢ h'(αᵢ)`

where `C(n, d)` is `BakerWustholz.C n d` and `h'(α)` is
`BakerWustholz.modifiedHeight φ α`. The `max(log B, 1/d)` factor (rather
than bare `log B`) is the standard Baker–Wüstholz formulation; it avoids
spuriously sharpening the bound at `d = 1`, `B = 2`. -/
/-- **Baker–Wüstholz theorem on linear forms in logarithms.** Let $n \ge 1$, let $K$ be a number
field of degree $d = [K : \mathbb{Q}]$, let $\varphi : K \to \mathbb{C}$ be a ring homomorphism,
and let $\alpha_1, \dots, \alpha_n$ be nonzero elements of $K$. Let $b_1, \dots, b_n$ be integers
and let $B \ge 2$ be a natural number with $|b_i| \le B$ for every $i$. With $\log$ the principal
branch of the complex logarithm, suppose that $\Lambda = \sum_{i=1}^n b_i \log \varphi(\alpha_i)$
is nonzero. Then
$$\log |\Lambda| \ge -C(n, d) \max\left(\log B, \frac{1}{d}\right) \prod_{i=1}^n h'(\alpha_i),$$
where $C(n, d)$ is the Baker–Wüstholz constant and $h'$ is the modified height with respect to
$\varphi$.

Source: A. Baker, G. Wüstholz, Logarithmic forms and group varieties, J. reine angew. Math. 442 (1993), 19-62. Via leanprover/lean-eval@38361be, problem `bakerWustholz_linearForms_logs`. -/
public theorem_wanted bakerWustholz_linearForms_logs
    {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (α : Fin n → K) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ) {B : ℕ} (hB : 2 ≤ B) (hbB : ∀ i, (b i).natAbs ≤ B)
    (hΛ_ne_zero : (∑ i, (b i : ℂ) * Complex.log (φ (α i))) ≠ 0) :
    Real.log ‖∑ i, (b i : ℂ) * Complex.log (φ (α i))‖
      ≥ -(BakerWustholz.C n (Module.finrank ℚ K)
          * max (Real.log B) (1 / (Module.finrank ℚ K : ℝ))
          * ∏ i, BakerWustholz.modifiedHeight φ (α i))

end MathlibExt.NumberTheory.BakerWustholzWanted
