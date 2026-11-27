/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pointwise ergodic theorems for non-conventional bilinear polynomial averages

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.PointwiseErgodicTheorems` — annals_pointwise_ergodic_theorems (manifest `manifests/problems/annals_pointwise_ergodic_theorems.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.PointwiseErgodicTheoremsWanted` namespace. Mathematical
statements are unchanged. Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

namespace MathlibExt.Dynamics.PointwiseErgodicTheoremsWanted
/-!
# Main Statements from Pointwise ergodic theorems for non-conventional bilinear polynomial averages

We formalise the statements of the main results from B. Krause, M. Mirek, and T. Tao,
`Pointwise ergodic theorems for non-conventional bilinear polynomial averages`,
Annals of Math, 195 (3) 2022.
-/

set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology

open scoped ENNReal NNReal PNat

/-- **Lacunary sequence.** For a real number $\Lambda \ge 0$, a sequence
$(a_n)_{n \in \mathbb{N}}$ of nonnegative real numbers is $\Lambda$-lacunary if
$a_{n+1} / a_n > \Lambda$ for every $n \in \mathbb{N}$, where division by $0$ gives $0$; in
particular every term of a $\Lambda$-lacunary sequence is positive. -/
def Lacunary (Λ : ℝ≥0) (a : ℕ → ℝ≥0) : Prop := ∀ n, a (n + 1) / a n > Λ

/-- **Variational norm.** For a real number $r \ge 0$ and a sequence
$a = (a_n)_{n \in \mathbb{N}}$ of complex numbers, the $r$-variational norm of $a$ is the
element of $[0, \infty]$

$$\|a\|_{\mathbb{V}^r} = \sup_{n \in \mathbb{N}} |a_n| +
\sup_{J \in \mathbb{N}} \sup_{N_0 \le N_1 \le \dots \le N_J}
\Big( \sum_{j=0}^{J-1} |a_{N_{j+1}} - a_{N_j}|^r \Big)^{1/r},$$

where the inner supremum runs over nondecreasing finite sequences of natural numbers
$N_0 \le N_1 \le \dots \le N_J$ and the empty sum ($J = 0$) is $0$. For $r = 0$ the whole term
$\big( \sum_{j=0}^{J-1} |a_{N_{j+1}} - a_{N_j}|^r \big)^{1/r}$ is replaced by the number of
indices $j < J$ with $a_{N_{j+1}} \ne a_{N_j}$.
-/
noncomputable def variationalNorm (r : ℝ≥0) (a : ℕ → ℂ) : ℝ≥0∞ :=
  (⨆ n, ‖a n‖ₑ) + ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
    ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))‖

/- We assume that `(X, μ, T)` is a Measure-preserving system. That is `(X, μ)` is a
`σ`-finite measure space, and `T : X → X` is an invertible bimeasurable map that is
measure preserving in the sense that `μ(T(E)) = μ(E)` for all measurable `E`.-/
variable {𝓧 : Type*} [σX : MeasurableSpace 𝓧] {μ : Measure 𝓧} [SigmaFinite μ]
  {T : 𝓧 ≃ᵐ 𝓧} (hT : MeasurePreserving T μ μ)

include hT

/-- **Bilinear polynomial ergodic averages.** Let $X$ be a measurable space and let
$T : X \to X$ be a measurable bijection with measurable inverse. For a real number $N \ge 0$,
polynomials $P_1, P_2 \in \mathbb{Z}[t]$, functions $f, g : X \to \mathbb{C}$ and a point
$x \in X$, the bilinear average is the complex number

$$A_N^{P_1, P_2}(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^{P_1(n)} x)\, g(T^{P_2(n)} x),$$

where $T^k$ for $k \in \mathbb{Z}$ is the $k$-th power of $T$ in the group of bijections of $X$
(so negative powers are iterates of $T^{-1}$), and $A_N^{P_1, P_2}(f, g)(x) = 0$ when
$\lfloor N \rfloor = 0$. -/
noncomputable def A (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ : ℤ[X]) (P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) : ℂ :=
  (Nat.floor N : ℝ)⁻¹ * ∑ n ∈ Icc 1 (Nat.floor N),
    f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)

/- Let `P : ℤ[X]` be a polynomial with degree at least `2`. -/
variable {P : ℤ[X]} (hP : P.degree ≥ 2)

include hP

/- Let `p₁, p₂, p` be real numbers such that `1 < p₁, p₂ < ∞` and `p₁⁻¹ + p₂⁻¹ = p⁻¹ ≤ 1`. -/
variable {p₁ p₂ p : ℝ≥0∞} (h₁p₁ : 1 < p₁) (h₁p₂ : 1 < p₂) (h₂p₁ : p₁ < ∞) (h₂p₂ : p₂ < ∞)
  (hp₁p₂p : p₁⁻¹ + p₂⁻¹ = p⁻¹) (hp : p⁻¹ ≤ 1)

include h₁p₁ h₁p₂ h₂p₁ h₁p₂ h₂p₂ hp₁p₂p hp

/--
**Mean ergodic theorem for bilinear polynomial averages.** Let $(X, \mu)$ be a $\sigma$-finite
measure space and let $T : X \to X$ be a measurable bijection with measurable inverse that
preserves $\mu$. Let $P \in \mathbb{Z}[t]$ have degree at least $2$, and let
$p_1, p_2 \in (1, \infty)$ and $p \in [0, \infty]$ satisfy $p_1^{-1} + p_2^{-1} = p^{-1}$ and
$p^{-1} \le 1$. For a real number $N \ge 0$, functions $f, g : X \to \mathbb{C}$ and $x \in X$ let

$$A_N(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^n x)\, g(T^{P(n)} x),$$

with $A_N(f, g)(x) = 0$ when $\lfloor N \rfloor = 0$, where $T^k$ for $k \in \mathbb{Z}$ is the
$k$-th power of $T$ in the group of bijections of $X$. Then for all
$f \in L^{p_1}(\mu)$ and $g \in L^{p_2}(\mu)$ with values in $\mathbb{C}$ there is a function
$h : X \to \mathbb{C}$ in $L^p(\mu)$ such that $\|A_N(f, g) - h\|_{L^p(\mu)} \to 0$ as the real
number $N$ tends to $\infty$.

This is Theorem 1.17(i) of Krause, Mirek and Tao.

Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_i {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ ∧
    Tendsto (fun N ↦ eLpNorm (A T N (X : ℤ[X]) P f g - h) p μ) atTop (𝓝 0)

/--
**Pointwise ergodic theorem for bilinear polynomial averages.** Let $(X, \mu)$ be a $\sigma$-finite
measure space and let $T : X \to X$ be a measurable bijection with measurable inverse that
preserves $\mu$. Let $P \in \mathbb{Z}[t]$ have degree at least $2$, and let
$p_1, p_2 \in (1, \infty)$ and $p \in [0, \infty]$ satisfy $p_1^{-1} + p_2^{-1} = p^{-1}$ and
$p^{-1} \le 1$. For a real number $N \ge 0$, functions $f, g : X \to \mathbb{C}$ and $x \in X$ let

$$A_N(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^n x)\, g(T^{P(n)} x),$$

with $A_N(f, g)(x) = 0$ when $\lfloor N \rfloor = 0$, where $T^k$ for $k \in \mathbb{Z}$ is the
$k$-th power of $T$ in the group of bijections of $X$. Then for
all $f \in L^{p_1}(\mu)$ and $g \in L^{p_2}(\mu)$ with values in $\mathbb{C}$ there is a function
$h : X \to \mathbb{C}$ in $L^p(\mu)$ such that for $\mu$-almost every $x \in X$,
$A_N(f, g)(x) \to h(x)$ as the real number $N$ tends to $\infty$.

This is Theorem 1.17(ii) of Krause, Mirek and Tao.

Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_ii {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ ∧
    ∀ᵐ x ∂μ, Tendsto (fun N ↦ A T N (X : ℤ[X]) P f g x) atTop (𝓝 (h x))

/--
**Maximal inequality for bilinear polynomial averages.** Let $(X, \mu)$ be a $\sigma$-finite
measure space and let $T : X \to X$ be a measurable bijection with measurable inverse that
preserves $\mu$. Let $P \in \mathbb{Z}[t]$ have degree at least $2$, and let
$p_1, p_2 \in (1, \infty)$ and $p \in [0, \infty]$ satisfy $p_1^{-1} + p_2^{-1} = p^{-1}$ and
$p^{-1} \le 1$. For a real number $N \ge 0$, functions $f, g : X \to \mathbb{C}$ and $x \in X$ let

$$A_N(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^n x)\, g(T^{P(n)} x),$$

with $A_N(f, g)(x) = 0$ when $\lfloor N \rfloor = 0$, where $T^k$ for $k \in \mathbb{Z}$ is the
$k$-th power of $T$ in the group of bijections of $X$. Then there is
a constant $C \ge 0$, which may depend on $(X, \mu, T)$, $P$, $p_1$, $p_2$ and $p$, such that
for all $f \in L^{p_1}(\mu)$ and $g \in L^{p_2}(\mu)$ with values in $\mathbb{C}$,

$$\Big\| \sup_{N \in \mathbb{Z}_{>0}} |A_N(f, g)| \Big\|_{L^p(\mu)} \le
C \, \|f\|_{L^{p_1}(\mu)} \, \|g\|_{L^{p_2}(\mu)},$$

where the supremum is taken pointwise in $[0, \infty]$.

This is Theorem 1.17(iii) of Krause, Mirek and Tao.

Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_iii : ∃ C : ℝ≥0, ∀ {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ),
    eLpNorm (fun x ↦ ⨆ (N : ℕ+), ‖A T N (X : ℤ[X]) P f g x‖ₑ) p μ ≤
      C * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

/--
**Long variational inequality for bilinear polynomial averages.** Let $(X, \mu)$ be a
$\sigma$-finite measure space and let $T : X \to X$ be a measurable bijection with measurable
inverse that preserves $\mu$. Let $P \in \mathbb{Z}[t]$ have degree at least $2$, and let
$p_1, p_2 \in (1, \infty)$ and $p \in [0, \infty]$ satisfy $p_1^{-1} + p_2^{-1} = p^{-1}$ and
$p^{-1} \le 1$. For a real number $N \ge 0$, functions $f, g : X \to \mathbb{C}$ and $x \in X$ let

$$A_N(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^n x)\, g(T^{P(n)} x),$$

with $A_N(f, g)(x) = 0$ when $\lfloor N \rfloor = 0$, where $T^k$ for $k \in \mathbb{Z}$ is the
$k$-th power of $T$ in the group of bijections of $X$. Then
for all real numbers $r > 2$ and $\Lambda > 1$ there is a constant $C \ge 0$, which may depend
on $r$, $\Lambda$ and all of the data above, such that for all $f \in L^{p_1}(\mu)$ and
$g \in L^{p_2}(\mu)$ with values in $\mathbb{C}$ and every $\Lambda$-lacunary sequence
$(a_n)_{n \in \mathbb{N}}$ of nonnegative reals (that is, $a_{n+1} / a_n > \Lambda$ for all $n$)
with $a_n \ge 1$ for all $n$,

$$\Big\| x \mapsto \big\| (A_{a_n}(f, g)(x))_{n \in \mathbb{N}} \big\|_{\mathbb{V}^r}
\Big\|_{L^p(\mu)} \le C \, \|f\|_{L^{p_1}(\mu)} \, \|g\|_{L^{p_2}(\mu)},$$

where $\| \cdot \|_{\mathbb{V}^r}$ is the $r$-variational norm of a sequence of complex numbers.

This is Theorem 1.17(iv) of Krause, Mirek and Tao.

Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_iv (r Λ : ℝ≥0) (hr : r > 2) (hΛ : Λ > 1) :
    ∃ C : ℝ≥0, ∀ {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0),
    Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x ↦ variationalNorm r fun n ↦ A T (a n) X P f g x) p μ ≤
      C * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

end PointwiseErgodicTheorems

end MathlibExt.Dynamics.PointwiseErgodicTheoremsWanted
