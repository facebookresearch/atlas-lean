/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Higher uniformity of bounded multiplicative functions in short intervals on average

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.BoundedMultiplicativeFunctions` — annals_bounded_multiplicative_functions (manifest `manifests/problems/annals_bounded_multiplicative_functions.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.BoundedMultiplicativeFunctionsWanted` namespace. Mathematical
statements are unchanged, except that the helper
`ArithmeticFunction.intExtension` returns `0` explicitly for `z ≤ 0`
(upstream's `f ⌊z⌋₊` gives `f 0`, which need not be `0`), matching its
documented semantics; `theorem_1_3` and `corollary_1_1` use that helper. Source: K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, and T. Ziegler, `Higher uniformity of bounded multiplicative functions in short intervals on average`, Annals of Math, 197 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-2-BoundedMultiplicativeFunctions.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.SmoothNumbers

@[expose] public section

namespace MathlibExt.NumberTheory.BoundedMultiplicativeFunctionsWanted
/-!
# Main Statements from Higher uniformity of bounded multiplicative functions in short intervals
# on average

We formalise the statements of the main results from K. Matomäki, M. Radziwiłł, T. Tao,
J. Teräväinen, and T. Ziegler,
`Higher uniformity of bounded multiplicative functions in short intervals on average`,
Annals of Math, 197 (2) 2023.
-/

set_option autoImplicit false

namespace BoundedMultiplicativeFunctions

open Polynomial Finset Real Complex Filter ArithmeticFunction

open scoped ComplexConjugate

/-- **Extension of an arithmetic function to the integers.** Let $R$ be a type with a zero
element $0$ and let $f$ be an arithmetic function with values in $R$. The extension of $f$ to the
integers is the function on $\mathbb{Z}$ that sends an integer $z$ to $f(z)$ if $z > 0$ and to
$0$ if $z \le 0$. -/
noncomputable def _root_.ArithmeticFunction.intExtension {R : Type*} [Zero R]
    (f : ArithmeticFunction R) (z : ℤ) : R := if z ≤ 0 then 0 else f ⌊z⌋₊

/-- Given `k : ℕ`, `x H : ℝ` we define the weak Gowers uniformity norm of a function `f : ℤ → ℂ`
by the formula:

`‖f‖_{uᵏ⁺¹[x, x + H]} :=`
  `sup_{P ∈ ℝ[X] | degree(P) ≤ k} (1/H) |∑_{x ≤ n ≤ x + H} f(n)exp(2πi(-P(n)))|`. -/
noncomputable
def weakGowersUniformityNorm (k : ℕ) (x H : ℝ) (f : ℤ → ℂ) : ℝ :=
  ⨆ P ∈ degreeLE ℝ k, 1 / H * ‖∑ n ∈ Icc ⌈x⌉ ⌊x + H⌋, f n * cexp (2 * π * I * - P.eval (n : ℝ))‖

/-- **1-bounded function.** A function $f \colon \mathbb{N} \to \mathbb{C}$ is 1-bounded if
$|f(n)| \le 1$ for every natural number $n$. -/
abbrev IsOneBounded (f : ℕ → ℂ) : Prop := ∀ n, ‖f n‖ ≤ 1

/-- Given `X : ℝ`, we define a distance `𝔻` on functions `ℕ → ℂ` by the formula:

`𝔻(f,g;X) := (∑_{p ≤ X | p is prime} ((1 - Re(f(p) conj(g(p)))) / p)) ^ (1/2)`.
-/
noncomputable
def 𝔻 (f g : ℕ → ℂ) (X : ℝ) : ℝ :=
  (∑ p ∈ ⌊X⌋₊.primesLE, (1 - (f p * conj (g p)).re) / p) ^ (1 / (2 : ℝ))

/-- Given `f : ℕ → ℂ`, `X : ℝ` and `Q : ℕ+`, we define the quantity

`M(f;X,Q) := inf_{|t| ≤ X} inf_{χ ∈ {Dirichlet character mod q s.t q ≤ Q}} 𝔻(f, n ↦ χ(n)n ^ it; X)`.
-/
noncomputable
def M (f : ℕ → ℂ) (X : ℝ) (Q : ℕ+) : ℝ :=
  ⨅ t : {t // |t| ≤ X}, ⨅ q : {q // q ≤ Q}, ⨅ (χ : DirichletCharacter ℂ q),
    𝔻 f (fun n ↦ χ n * n ^ (I * t)) X

/--
**Non-pretentious multiplicative functions do not correlate with polynomial phases on short
intervals on average.** For a function $g$ on the integers, a natural number $k$, a real $x$ and a
real $H > 0$ write
$$
\|g\|_{u^{k+1}[x, x+H]} = \sup_{\deg P \le k} \frac{1}{H}
\Bigl| \sum_{\lceil x \rceil \le n \le \lfloor x + H \rfloor} g(n) e^{-2\pi i P(n)} \Bigr|,
$$
the supremum taken over real polynomials $P$ of degree at most $k$. For functions
$f, g \colon \mathbb{N} \to \mathbb{C}$ and a real $X$ let
$$
\mathbb{D}(f, g; X) =
\Bigl( \sum_{p \le X} \frac{1 - \operatorname{Re}\bigl(f(p) \overline{g(p)}\bigr)}{p} \Bigr)^{1/2},
$$
the sum taken over primes $p \le X$, and for a positive integer $Q$ let $M(f; X, Q)$ be the
infimum of $\mathbb{D}(f, n \mapsto \chi(n) n^{it}; X)$ over real $t$ with $|t| \le X$, positive
integers $q \le Q$ and Dirichlet characters $\chi$ modulo $q$.

Let $k$ be a natural number, $\theta$ a real number with $0 < \theta < 1/2$ and $\eta > 0$ a real
number. Then there are a positive integer $Q$ and real numbers $C > 0$ and $B$ such that the
following holds for every multiplicative arithmetic function $f \colon \mathbb{N} \to \mathbb{C}$
with $|f(n)| \le 1$ for all $n$, extended to the integers by $f(n) = 0$ for $n \le 0$, every real
$X \ge 1$ and every real $H$ with $X^\theta \le H \le X^{1-\theta}$: if
$$
\int_X^{2X} \|f\|_{u^{k+1}[x, x+H]} \, dx \ge \eta X,
$$
then $M(f; C X^{k+1} / H^{k+1}, Q) \le B$.

Source: K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, and T. Ziegler, `Higher uniformity of bounded multiplicative functions in short intervals on average`, Annals of Math, 197 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-2-BoundedMultiplicativeFunctions.lean Via leanprover/lean-eval@38361be, problem `annals_bounded_multiplicative_functions`.
-/
public theorem_wanted theorem_1_3 (k : ℕ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1 / 2) (η : ℝ) (hη : η > 0) :
    ∃ (Q : ℕ+) (_hQ : 1 ≤ Q) (C : ℝ) (_hC : 0 < C) (B : ℝ),
      ∀ (f : ArithmeticFunction ℂ) (_hf : f.IsMultiplicative) (_hf' : IsOneBounded f)
        (X : ℝ) (_hX : X ≥ 1) (H : ℝ) (_hXH : X ^ θ ≤ H) (_hHX : H ≤ X ^ (1 - θ)),
          ∫ x in X..(2 * X), weakGowersUniformityNorm k x H f.intExtension ≥ η * X →
            M f (C * X ^ (k + 1) / H ^ (k + 1)) Q ≤ B

/--
**Liouville's function does not correlate with polynomial phases on short intervals on average.**
Let $\lambda$ be the Liouville function, extended to the integers by $\lambda(n) = 0$ for
$n \le 0$, let $k$ be a natural number and let $\theta$ be a real number with $0 < \theta < 1$.
For real $x$ and $H > 0$ write
$$
\|\lambda\|_{u^{k+1}[x, x+H]} = \sup_{\deg P \le k} \frac{1}{H}
\Bigl| \sum_{\lceil x \rceil \le n \le \lfloor x + H \rfloor} \lambda(n) e^{-2\pi i P(n)} \Bigr|,
$$
the supremum taken over real polynomials $P$ of degree at most $k$. Then
$$
\int_X^{2X} \|\lambda\|_{u^{k+1}[x, x + X^\theta]} \, dx = o(X)
$$
as the real number $X$ tends to infinity.

Source: K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, and T. Ziegler, `Higher uniformity of bounded multiplicative functions in short intervals on average`, Annals of Math, 197 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-2-BoundedMultiplicativeFunctions.lean Via leanprover/lean-eval@38361be, problem `annals_bounded_multiplicative_functions`.
-/
public theorem_wanted corollary_1_1 (k : ℕ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    (fun X ↦ ∫ x in X..(2 * X), weakGowersUniformityNorm k x (X ^ θ) (fun n ↦ liouville ⌊n⌋₊))
      =o[atTop] (fun X ↦ X)

end BoundedMultiplicativeFunctions

end MathlibExt.NumberTheory.BoundedMultiplicativeFunctionsWanted
