/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Binomial
public import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace MetaMathlibExt

@[expose] public section

open Filter
open scoped BigOperators Topology

/-!
# The ℓ-generalized Fibonacci zeta function

Statement-only formalizations of the principal results in Meher and Sahoo's paper.
The generalized Fibonacci sequence is represented by a quantified integer-indexed
function satisfying its initial window and recurrence, rather than by a new recursive
definition.
-/

/-- **ℓ-generalized Fibonacci sequence.** Let $\ell$ be a natural number. A function
$F : \mathbb{Z} \to \mathbb{Z}$ is an $\ell$-generalized Fibonacci sequence when $F(n) = 0$ for
every integer $n$ with $2 - \ell \le n \le 0$, $F(1) = 1$, and
$F(n) = \sum_{i=0}^{\ell-1} F(n-1-i)$ for every integer $n > 1$.

The values of $F$ below $2 - \ell$ are unconstrained, since the sequence is defined only from
that index onward.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Definition
preceding Proposition 1. -/
public def IsLGeneralizedFibonacci (ℓ : ℕ) (F : ℤ → ℤ) : Prop :=
  (∀ n : ℤ, 2 - (ℓ : ℤ) ≤ n → n < 1 → F n = 0) ∧
    F 1 = 1 ∧
    ∀ n : ℤ, 1 < n →
      F n = ∑ i ∈ Finset.range ℓ, F (n - 1 - (i : ℤ))

/-- **Characteristic polynomial of the ℓ-generalized Fibonacci recurrence.** For a natural number
$\ell$, the characteristic polynomial of the $\ell$-generalized Fibonacci recurrence is the
polynomial $\varphi_\ell(X) = X^\ell - \sum_{i=0}^{\ell-1} X^i$ in $\mathbb{C}[X]$; for
$\ell \ge 2$ this is $X^\ell - X^{\ell-1} - \cdots - X - 1$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Characteristic polynomial definition. -/
public noncomputable def lGeneralizedFibonacciCharacteristic (ℓ : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ ℓ - ∑ i ∈ Finset.range ℓ, Polynomial.X ^ i

/-- **Dresden–Du coefficient.** For a natural number $\ell$ and a complex number $\beta$, the
Dresden–Du coefficient is the complex number
$c(\beta) = \frac{\beta - 1}{2 + (\ell + 1)(\beta - 2)}$, taken to be $0$ when the denominator
vanishes.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Coefficient definition preceding Lemma 1. -/
public noncomputable def lGeneralizedFibonacciCoefficient (ℓ : ℕ) (β : ℂ) : ℂ :=
  (β - 1) / (2 + ((ℓ : ℂ) + 1) * (β - 2))

/-- **Other roots of the ℓ-generalized Fibonacci characteristic polynomial.** For a natural number
$\ell$ and a real number $\alpha$, this is the finite set of distinct complex roots of the
characteristic polynomial $\varphi_\ell(X) = X^\ell - \sum_{i=0}^{\ell-1} X^i$ other than $\alpha$.
In applications $\alpha$ is the dominant real root of $\varphi_\ell$.

Each root is listed once, without multiplicity; the roots of $\varphi_\ell$ are in fact simple.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Root notation preceding Proposition 1. -/
public noncomputable def lGeneralizedFibonacciOtherRoots (ℓ : ℕ) (α : ℝ) : Finset ℂ :=
  ((lGeneralizedFibonacciCharacteristic ℓ).roots.toFinset).erase (α : ℂ)

/-- **Possible pole of the ℓ-generalized Fibonacci zeta function at a given index.** Let $\ell$
be a natural number, let $\alpha$ be a real number, and let $R$ be the set of complex roots of
$X^\ell - \sum_{i<\ell} X^i$ other than $\alpha$. For a function $\kappa$ from $\mathbb{C}$ to the
natural numbers and an integer $n$, the possible pole indexed by $(\kappa, n)$ is
$$
s_{\kappa,n} = -\sum_{\beta \in R} \kappa(\beta) +
\frac{2 n \pi i + \sum_{\beta \in R} \kappa(\beta) \log \beta}{\log \alpha},
$$
where $\log$ is the principal branch of the complex logarithm.

Only the values of $\kappa$ on $R$ enter; their sum is the number called $k$ in the paper.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaPole
    (ℓ : ℕ) (α : ℝ) (κ : ℂ → ℕ) (n : ℤ) : ℂ :=
  -((∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ β : ℕ) : ℂ) +
    (2 * (n : ℂ) * (Real.pi : ℂ) * Complex.I +
        ∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, (κ β : ℂ) * Complex.log β) /
      Complex.log (α : ℂ)

/-- **The ℓ-generalized Fibonacci characteristic polynomial for ℓ = 2.** For $\ell = 2$ the
characteristic polynomial $\varphi_2$ of the $\ell$-generalized Fibonacci recurrence is the
Fibonacci polynomial $X^2 - X - 1$ in $\mathbb{C}[X]$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Equation (3). -/
public theorem lGeneralizedFibonacciCharacteristic_two :
    lGeneralizedFibonacciCharacteristic 2 = Polynomial.X ^ 2 - Polynomial.X - 1 := by
  simp [lGeneralizedFibonacciCharacteristic, Finset.sum_range_succ]
  ring

/-- **The possible pole at the zero index is zero.** For every natural number $\ell$ and every
real number $\alpha$, the possible pole $s_{\kappa,n}$ of the $\ell$-generalized Fibonacci zeta
function indexed by the identically zero function $\kappa$ and $n = 0$ equals $0$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public theorem lGeneralizedFibonacciZetaPole_zero (ℓ : ℕ) (α : ℝ) :
    lGeneralizedFibonacciZetaPole ℓ α (fun _ => 0) 0 = 0 := by
  simp [lGeneralizedFibonacciZetaPole]

/-- **Set of possible poles of the ℓ-generalized Fibonacci zeta function.** For a natural number
$\ell$ and a real number $\alpha$, let $R$ be the set of distinct complex roots of the
characteristic polynomial $X^\ell - \sum_{i=0}^{\ell-1} X^i$ other than $\alpha$. The set $S$ of
possible poles is the set of all complex numbers $-K + (2n\pi i + L)/\log\alpha$, where $n$ is
an integer, $(\kappa_\beta)_{\beta \in R}$ is a family of natural numbers,
$K = \sum_{\beta \in R} \kappa_\beta$ and $L = \sum_{\beta \in R} \kappa_\beta \log \beta$. Here
$\log$ is the principal complex logarithm.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaPoleSet (ℓ : ℕ) (α : ℝ) : Set ℂ :=
  {s | ∃ (κ : ℂ → ℕ) (n : ℤ), s = lGeneralizedFibonacciZetaPole ℓ α κ n}

/-- **Residue expression of the ℓ-generalized Fibonacci zeta function.** Let $\ell$ be a natural
number, let $\alpha$ be a real number, let $R$ be the set of complex roots of
$X^\ell - \sum_{i<\ell} X^i$ other than $\alpha$, let
$c(\beta) = (\beta - 1)/(2 + (\ell + 1)(\beta - 2))$ be the Dresden–Du coefficient, and put
$d = c(\alpha)/\alpha$. For a function $\kappa$ from $\mathbb{C}$ to the natural numbers and an
integer $n$, let $k = \sum_{\beta \in R} \kappa(\beta)$ and let $s_0$ be the possible pole
indexed by $(\kappa, n)$. The residue expression indexed by $(\kappa, n)$ is
$$
\rho_{\kappa,n} = d^{-s_0} \binom{-s_0}{k} d^{-k} \cdot
\frac{k!}{\prod_{\beta \in R} \kappa(\beta)!} \cdot
\prod_{\beta \in R} \left(\frac{c(\beta)}{\beta}\right)^{\kappa(\beta)} \cdot
\frac{1}{\log \alpha},
$$
where $\binom{-s_0}{k} = (-s_0)(-s_0 - 1)\cdots(-s_0 - k + 1)/k!$ is the generalized binomial
coefficient, $d^{-s_0}$ and $d^{-k}$ are principal complex powers, and $\log$ is the principal
branch of the complex logarithm.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaResidue
    (ℓ : ℕ) (α : ℝ) (κ : ℂ → ℕ) (n : ℤ) : ℂ :=
  let roots := lGeneralizedFibonacciOtherRoots ℓ α
  let k := (∑ β ∈ roots, κ β)
  let s₀ := lGeneralizedFibonacciZetaPole ℓ α κ n
  let dominant :=
    lGeneralizedFibonacciCoefficient ℓ (α : ℂ) * (α : ℂ)⁻¹
  dominant ^ (-s₀) *
    Ring.choose (-s₀) k *
    dominant ^ (-(k : ℂ)) *
    ((Nat.factorial k : ℂ) /
      ∏ β ∈ roots, (Nat.factorial (κ β) : ℂ)) *
    (∏ β ∈ roots,
      (lGeneralizedFibonacciCoefficient ℓ β * β⁻¹) ^ κ β) *
    (1 / Complex.log (α : ℂ))

/-- **Corollary pole of the ℓ-generalized Fibonacci zeta function.** For natural numbers $\ell$
and $k$, a real number $\alpha$ and an integer $n$, let $q$ be the quotient of $k$ by $\ell - 1$
in natural-number division, with $q = 0$ when $\ell \le 1$ (so $q = k/(\ell - 1)$ when
$\ell \ge 2$ and $\ell - 1$ divides $k$). The corollary pole is the complex number
$-(k + q) + i\pi(2n + q)/\log \alpha$ if $\ell$ is even and $-(k + q) + 2\pi i n/\log \alpha$ if
$\ell$ is odd, where $\log$ is the principal complex logarithm.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Corollary 1. -/
public noncomputable def lGeneralizedFibonacciZetaCorollaryPole
    (ℓ k : ℕ) (α : ℝ) (n : ℤ) : ℂ :=
  -((k + k / (ℓ - 1) : ℕ) : ℂ) +
    if Even ℓ then
      Complex.I * (Real.pi : ℂ) *
          ((2 * n + (k / (ℓ - 1) : ℕ) : ℤ) : ℂ) /
        Complex.log (α : ℂ)
    else
      Complex.I * (2 * (n : ℂ) * (Real.pi : ℂ)) /
        Complex.log (α : ℂ)

/-- **Absolute convergence of the ℓ-generalized Fibonacci zeta series.** Let $\ell \ge 2$ and let
$F$ be an $\ell$-generalized Fibonacci sequence. For every complex number $s$ with
$\operatorname{Re} s > 0$, the series $\sum_{n \ge 1} |F_n^{-s}|$ converges, where $F_n^{-s}$ is
the principal complex power of $F_n$ viewed as a complex number.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Proposition 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_summable
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (s : ℂ) (hs : 0 < s.re) :
    Summable (fun j : ℕ => ‖((F ((j : ℤ) + 1) : ℂ) ^ (-s))‖)

/-- **Meromorphic continuation of the ℓ-generalized Fibonacci zeta function.** Let $\ell \ge 2$,
let $F$ be an $\ell$-generalized Fibonacci sequence, let $\alpha > 1$ be a real number with
$\alpha^\ell = \sum_{i=0}^{\ell-1} \alpha^i$, and let $S$ be the set of possible poles determined
by $\ell$ and $\alpha$. Then there is a function $f : \mathbb{C} \to \mathbb{C}$ such that
$f(s) = \sum_{n \ge 1} F(n)^{-s}$ for every complex $s$ with $\operatorname{Re} s > 0$, $f$ is
complex differentiable at every point outside $S$, and for every $s_0 \in S$ the limit of
$(s - s_0) f(s)$ as $s \to s_0$ with $s \ne s_0$ exists in $\mathbb{C}$.

The last clause says that $f$ has at most simple poles, all lying in $S$; the residues are
stated separately.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_meromorphicContinuation
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i) :
    ∃ f : ℂ → ℂ,
      (∀ s : ℂ, 0 < s.re →
        f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
        DifferentiableAt ℂ f s) ∧
      ∀ s₀ : ℂ, s₀ ∈ lGeneralizedFibonacciZetaPoleSet ℓ α →
        ∃ r : ℂ,
          Tendsto (fun s : ℂ => (s - s₀) * f s) (𝓝[≠] s₀) (𝓝 r)

/-- **Residues of the ℓ-generalized Fibonacci zeta function.** Let $\ell \ge 2$, let $F$ be an
$\ell$-generalized Fibonacci sequence, and let $\alpha > 1$ be a real number with
$\alpha^\ell = \sum_{i<\ell} \alpha^i$. Let $R$ be the set of complex roots of
$X^\ell - \sum_{i<\ell} X^i$ other than $\alpha$, let $s_{\kappa,n}$ be the possible pole and
$\rho_{\kappa,n}$ the residue expression indexed by a function $\kappa$ from $\mathbb{C}$ to the
natural numbers and an integer $n$, and let $S$ be the set of all possible poles $s_{\kappa,n}$.
Fix $\kappa$ and $n$ such that whenever $s_{\kappa',n'} = s_{\kappa,n}$, we have $n' = n$ and
$\kappa'(\beta) = \kappa(\beta)$ for every $\beta \in R$. Let $f : \mathbb{C} \to \mathbb{C}$
satisfy $f(s) = \sum_{m \ge 1} F_m^{-s}$ (principal complex powers) for every $s$ with
$\operatorname{Re} s > 0$, and let $f$ be complex differentiable at every point outside $S$.
Then $(s - s_{\kappa,n}) f(s)$ tends to $\rho_{\kappa,n}$ as $s$ tends to $s_{\kappa,n}$ with
$s \ne s_{\kappa,n}$.

The hypothesis that $(\kappa, n)$ is the only index of its pole is not in the paper: when
different indices give the same pole, their residue contributions add up, a case the printed
formula does not address.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1
(residue formula). -/
public theorem_wanted lGeneralizedFibonacciZeta_residue
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (κ : ℂ → ℕ) (n : ℤ)
    (hunique : ∀ (κ' : ℂ → ℕ) (n' : ℤ),
      lGeneralizedFibonacciZetaPole ℓ α κ' n' =
          lGeneralizedFibonacciZetaPole ℓ α κ n →
        n' = n ∧
          ∀ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ' β = κ β)
    (f : ℂ → ℂ)
    (hseries : ∀ s : ℂ, 0 < s.re →
      f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s)))
    (hregular : ∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
      DifferentiableAt ℂ f s) :
    Tendsto
      (fun s : ℂ =>
        (s - lGeneralizedFibonacciZetaPole ℓ α κ n) * f s)
      (𝓝[≠] lGeneralizedFibonacciZetaPole ℓ α κ n)
      (𝓝 (lGeneralizedFibonacciZetaResidue ℓ α κ n))

/-- **Explicit possible poles of the ℓ-generalized Fibonacci zeta function.** Let $\ell \ge 2$, let
$\alpha > 1$ be a real number with $\alpha^\ell = \sum_{i=0}^{\ell-1} \alpha^i$, and let $k$ be a
natural number divisible by $\ell - 1$; write $q = k/(\ell - 1)$. Then for every integer $n$, the
point $-(k + q) + i\pi(2n + q)/\log \alpha$ if $\ell$ is even, and $-(k + q) + 2\pi i n/\log \alpha$
if $\ell$ is odd, belongs to the set $S$ of possible poles of the $\ell$-generalized Fibonacci
zeta function determined by $\ell$ and $\alpha$.

A witnessing exponent tuple takes the constant value $q$ at every root of the characteristic
polynomial other than $\alpha$.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Corollary 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_corollaryPole_mem
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (k : ℕ) (hk : ℓ - 1 ∣ k) (n : ℤ) :
    lGeneralizedFibonacciZetaCorollaryPole ℓ k α n ∈
      lGeneralizedFibonacciZetaPoleSet ℓ α

/-- **Rational values of the ℓ-generalized Fibonacci zeta function at negative integers.** Let
$\ell \ge 2$, let $F$ be an $\ell$-generalized Fibonacci sequence, let $\alpha > 1$ be a real
number with $\alpha^\ell = \sum_{i=0}^{\ell-1} \alpha^i$, and let $S$ be the set of possible
poles determined by $\ell$ and $\alpha$. Let $m$ be a positive integer and let
$f : \mathbb{C} \to \mathbb{C}$ be a function that satisfies $f(s) = \sum_{n \ge 1} F(n)^{-s}$
whenever $\operatorname{Re} s > 0$ and is complex differentiable at every point outside $S$. If
$f$ is complex differentiable at $-m$, then $f(-m)$ is a rational number.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 2. -/
public theorem_wanted lGeneralizedFibonacciZeta_negInt_rational
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (m : ℕ) (hm : 0 < m) (f : ℂ → ℂ)
    (hseries : ∀ s : ℂ, 0 < s.re →
      f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s)))
    (hregular : ∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
      DifferentiableAt ℂ f s)
    (hmregular : DifferentiableAt ℂ f (-(m : ℂ))) :
    ∃ q : ℚ, f (-(m : ℂ)) = (q : ℂ)

end

end MetaMathlibExt
