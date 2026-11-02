/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sobolev embedding theorem (Morrey regime)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.SobolevMorrey` — sobolev_embedding_morrey (manifest `manifests/problems/sobolev_embedding_morrey.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.SobolevMorreyWanted` namespace. Mathematical
statements are unchanged. Source: C.B. Morrey, 'Functions of several variables and absolute continuity, II', Duke Math. J. 6 (1940) 187–215; full Sobolev-embedding development in *Multiple Integrals in the Calculus of Variations*, Springer 1966. Listed as §111 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.SobolevMorreyWanted
namespace Analysis
namespace SobolevMorreyProblem

/-!
# Sobolev embedding theorem (Morrey regime)

When `n < p` and `r + α < k − n/p`, every `W^{k,p}(ℝⁿ)` function has a
`C^{r,α}` representative — the Sobolev embedding into Hölder spaces.
Charles Morrey, *Functions of several variables and absolute
continuity, II*, Duke Math. J. **6** (1940). The theorem is listed as
§111 in Knill's *Some Fundamental Theorems in Mathematics*.

The `LocallyIntegrable f` conjunct in `MemSobolevWk` is essential to
faithfulness: without it, a non-a.e.-measurable `f` would make every
distributional pairing `∫ f · D^m φ` collapse to the default value
that Lean's Bochner integral assigns outside integrability hypotheses,
so `IsWeakDeriv f 0 m` would hold vacuously and `f` would spuriously
satisfy `W^{k,p}` membership while having no a.e.-equal continuous
representative.

Mathlib has the subcritical Gagliardo–Nirenberg–Sobolev inequality
(`eLpNorm_le_eLpNorm_fderiv_*`) and the Bessel-potential / `H^{s,p}`
spaces (`TemperedDistribution.MemSobolev`), but no
weak-derivative Sobolev space `W^{k,p}` and no Morrey-regime embedding.
-/

open MeasureTheory
open scoped ENNReal NNReal

/-- **Euclidean space $\mathbb{R}^n$.** For a natural number $n$, $\mathbb{R}^n$ denotes the real
Euclidean space of dimension $n$: real vectors with coordinates indexed by $0, \dots, n-1$, with
the Euclidean inner product and norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- **Partial derivative.** For a coordinate index $i \in \{0, \dots, n-1\}$ and a function
$\varphi : \mathbb{R}^n \to \mathbb{R}$, the partial derivative $\partial_i \varphi$ is the
function $\mathbb{R}^n \to \mathbb{R}$ sending $x$ to $D\varphi(x)(e_i)$, the Fréchet derivative
of $\varphi$ at $x$ applied to the $i$-th standard basis vector $e_i$. At points where $\varphi$
is not differentiable its value is $0$. -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (φ : E n → ℝ) : E n → ℝ :=
  fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))

/-- **Mixed partial derivative.** For a multi-index $m = (m_0, \dots, m_{n-1})$ of natural numbers
and a function $\varphi : \mathbb{R}^n \to \mathbb{R}$, the mixed partial derivative is
$D^m \varphi = \partial_0^{m_0} \partial_1^{m_1} \cdots \partial_{n-1}^{m_{n-1}} \varphi$, where
$\partial_i^{j}$ is the $j$-fold iterate of the partial derivative $\partial_i$; thus
$\partial_{n-1}$ is applied first and $\partial_0$ last. -/
noncomputable def mixedDeriv {n : ℕ} (m : Fin n → ℕ) (φ : E n → ℝ) : E n → ℝ :=
  (List.finRange n).foldr (fun i ψ => (partialDeriv i)^[m i] ψ) φ

/-- **Weak derivative.** Let $f, g : \mathbb{R}^n \to \mathbb{R}$ and let
$m = (m_0, \dots, m_{n-1})$ be a multi-index of order $|m| = m_0 + \cdots + m_{n-1}$. Then $g$ is
a weak derivative $D^m f$ of $f$ when every smooth ($C^\infty$) compactly supported function
$\varphi : \mathbb{R}^n \to \mathbb{R}$ satisfies
$$\int_{\mathbb{R}^n} f \, D^m \varphi \, dx = (-1)^{|m|} \int_{\mathbb{R}^n} g \, \varphi \, dx,$$
where $D^m \varphi$ is the classical mixed partial derivative and each integral is the Lebesgue
integral, taken to be $0$ when the integrand is not integrable. -/
def IsWeakDeriv {n : ℕ} (f g : E n → ℝ) (m : Fin n → ℕ) : Prop :=
  ∀ φ : E n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, f x * mixedDeriv m φ x = (-1) ^ (∑ i, m i) * ∫ x, g x * φ x

/-- **Sobolev space $W^{k,p}(\mathbb{R}^n)$.** For a natural number $k$ and $p \in [0, \infty]$, a
function $f : \mathbb{R}^n \to \mathbb{R}$ belongs to $W^{k,p}(\mathbb{R}^n)$ when $f$ is locally
integrable and, for every multi-index $m = (m_0, \dots, m_{n-1})$ of natural numbers with
$m_0 + \cdots + m_{n-1} \le k$, $f$ has a weak derivative $D^m f$ that lies in
$L^p(\mathbb{R}^n)$. Local integrability and $L^p$ are with respect to Lebesgue measure. -/
def MemSobolevWk {n : ℕ} (k : ℕ) (p : ℝ≥0∞) (f : E n → ℝ) : Prop :=
  LocallyIntegrable f volume ∧
  ∀ m : Fin n → ℕ, (∑ i, m i) ≤ k →
    ∃ g : E n → ℝ, IsWeakDeriv f g m ∧ MemLp g p volume

/-- **Hölder space $C^{r,\alpha}(\mathbb{R}^n)$.** For a natural number $r$ and a real number
$\alpha$, a function $g : \mathbb{R}^n \to \mathbb{R}$ belongs to $C^{r,\alpha}(\mathbb{R}^n)$ when
$g$ is $r$ times continuously differentiable, its iterated derivatives $D^j g$ for $j \le r$ are
bounded on $\mathbb{R}^n$, and its $r$-th derivative is $\alpha$-Hölder: there is $C \ge 0$ with
$\|D^r g(x) - D^r g(y)\| \le C \|x - y\|^{\alpha}$ for all $x, y \in \mathbb{R}^n$. Here
$D^j g(x)$ is the $j$-th Fréchet derivative of $g$ at $x$, a $j$-linear map measured in the
operator norm, and a negative $\alpha$ is replaced by $0$. -/
def MemHolder {n : ℕ} (r : ℕ) (α : ℝ) (g : E n → ℝ) : Prop :=
  ContDiff ℝ (r : ℕ∞) g ∧
  (∃ C : NNReal, HolderWith C α.toNNReal (iteratedFDeriv ℝ r g)) ∧
  (∀ j ≤ r, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ M)

/- **Sobolev embedding theorem (Morrey regime).** If `n < p`,
`0 < α ≤ 1` and `r + α < k − n/p`, then every `W^{k,p}(ℝⁿ)` function
has a `C^{r,α}` representative. -/
/-- **Sobolev embedding theorem (Morrey regime).** Let $n, k, r$ be natural numbers and
$\alpha, p$ real numbers with $n < p$, $0 < \alpha \le 1$ and $r + \alpha < k - n/p$. Then every
function $f : \mathbb{R}^n \to \mathbb{R}$ in the Sobolev space $W^{k,p}(\mathbb{R}^n)$ is equal
almost everywhere, for Lebesgue measure, to some function $g$ in the Hölder space
$C^{r,\alpha}(\mathbb{R}^n)$.

Source: C.B. Morrey, 'Functions of several variables and absolute continuity, II', Duke Math. J. 6 (1940) 187–215; full Sobolev-embedding development in *Multiple Integrals in the Calculus of Variations*, Springer 1966. Listed as §111 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `sobolev_embedding_morrey`. -/
public theorem_wanted sobolev_embedding {n k r : ℕ} {α p : ℝ}
    (_hp : (n : ℝ) < p) (_hα : 0 < α) (_hα1 : α ≤ 1)
    (_hgap : (r : ℝ) + α < (k : ℝ) - n / p)
    (f : E n → ℝ) (_hf : MemSobolevWk k (ENNReal.ofReal p) f) :
    ∃ g : E n → ℝ, f =ᵐ[volume] g ∧ MemHolder r α g

end SobolevMorreyProblem
end Analysis

end MathlibExt.Analysis.SobolevMorreyWanted
