/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Power moments of Dedekind zeta coefficients over sums of six squares

Statements from Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the
Coefficients of the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25
(2025), Article A101.

For a number field `K`, `a_K(n)` is the number of integral ideals of `𝓞 K` of norm `n`, and
`S_ℓ(x) = ∑_{x₁² + ⋯ + x₆² ≤ x} a_K(x₁² + ⋯ + x₆²)^ℓ = ∑_{1 ≤ n ≤ x} r₆(n) a_K(n)^ℓ`
(the paper's equation (12); the zero vector is left out, as in that equation).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import WantedExt.NumberTheory.SquaresTriangularRepresentationsWanted

namespace MetaMathlibExt

@[expose] public section

open Complex NumberField

/-- **Fourth moment of the $L$-function modulo $4$.** Let $\chi$ be a nontrivial Dirichlet
character modulo $4$ and let $\varepsilon > 0$. Then there is a real constant $C$ such that for
every real $T \ge 1$, $\int_1^T |L(1/2 + it, \chi)|^4 \, dt \le C\, T^{1 + \varepsilon}$.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Lemma 5, third display (`integers-2025-A101-lem-5`). -/
public theorem_wanted dirichletLFunction_mod_four_fourth_moment_le {ε : ℝ} (hε : 0 < ε)
    (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫ t in (1 : ℝ)..T, ‖χ.LFunction (1 / 2 + t * I)‖ ^ 4 ≤ C * T ^ (1 + ε)

/-- **Coefficients of the Dedekind zeta function.** For a number field $K$ with ring of integers
$\mathcal{O}_K$ and a natural number $n$, $a_K(n)$ is the number of ideals of $\mathcal{O}_K$ of
absolute norm $n$. These are the coefficients of $\zeta_K(s) = \sum_{n \ge 1} a_K(n)\, n^{-s}$.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (2). -/
noncomputable def dedekindZetaCoeff (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- **The Dedekind zeta coefficient at $1$.** For every number field $K$, $a_K(1) = 1$, where
$a_K(n)$ is the number of ideals of the ring of integers of $K$ of absolute norm $n$: the unit
ideal is the only ideal of norm $1$.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (2). -/
theorem dedekindZetaCoeff_one (K : Type*) [Field K] [NumberField K] :
    dedekindZetaCoeff K 1 = 1 := by
  rw [dedekindZetaCoeff, Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.2)⟩

/-- **Six-squares moments of Dedekind zeta coefficients.** For a number field $K$, a natural
number $\ell$ and a real number $x$, the moment is the real number
$S_\ell(x) = \sum_{1 \le n \le x} r_6(n)\, a_K(n)^\ell$, where $n$ runs over the integers in
$[1, x]$, $a_K(n)$ is the number of ideals of the ring of integers of $K$ of absolute norm $n$,
and $r_6(n)$ is the coefficient of $q^n$ in $\theta(q)^6$, with
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$; that is, $r_6(n)$ is the number of representations
of $n$ as a sum of six squares of integers.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (4), and Section 2, equation (12). -/
noncomputable def sixSquaresDedekindMoment (K : Type*) [Field K] [NumberField K] (ℓ : ℕ)
    (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (sumOfSquaresRepCount 6 n : ℝ) * (dedekindZetaCoeff K n : ℝ) ^ ℓ

/-- **The six-squares moment vanishes below $1$.** For every number field $K$, every natural
number $\ell$ and every real $x < 1$, the six-squares moment
$S_\ell(x) = \sum_{1 \le n \le x} r_6(n)\, a_K(n)^\ell$ equals $0$, where $r_6(n)$ is the number
of representations of $n$ as a sum of six squares of integers and $a_K(n)$ is the number of
ideals of the ring of integers of $K$ of absolute norm $n$.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Section 1, equation (4). -/
theorem sixSquaresDedekindMoment_of_lt_one (K : Type*) [Field K] [NumberField K] (ℓ : ℕ)
    {x : ℝ} (hx : x < 1) : sixSquaresDedekindMoment K ℓ x = 0 := by
  simp [sixSquaresDedekindMoment, Nat.floor_eq_zero.mpr hx]

/-- **The exponent $a_{0,\ell}$.** For a natural number $\ell$, define

$$a_{0,\ell} = 1 + \sum_{i=1}^{\lfloor \ell/2 \rfloor} \binom{\ell}{2i} C_i,$$

where $C_i = (2i)!/(i!\,(i+1)!)$ is the $i$-th Catalan number.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 2 and equation (19). -/
def dedekindSixSquaresA0 (ℓ : ℕ) : ℕ :=
  1 + ∑ i ∈ Finset.Icc 1 (ℓ / 2), ℓ.choose (2 * i) * catalan i

/-- **The exponent $a_{3,\ell}$.** For a natural number $\ell$, $a_{3,\ell}$ is the sum over the
integers $1 \le i \le \lfloor (\ell - 1)/2 \rfloor$ of $\binom{\ell}{2i+1} q_i$, where $q_i$ is the
integer part of $4\,(2i+1)!/((i-1)!\,(i+3)!)$.

Each quotient $4\,(2i+1)!/((i-1)!\,(i+3)!)$ is in fact an integer, and the upper limit
$\lfloor (\ell - 1)/2 \rfloor$ equals the source's $\lceil \ell/2 - 1 \rceil$.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 2. -/
def dedekindSixSquaresA3 (ℓ : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 ((ℓ - 1) / 2), ℓ.choose (2 * i + 1) *
    (4 * (2 * i + 1).factorial / ((i - 1).factorial * (i + 3).factorial))

/-- **Values of $a_{0,\ell}$ and $a_{3,\ell}$ for $\ell = 3, 4, 5$.** For a natural number $\ell$
let $a_{0,\ell} = 1 + \sum_{i=1}^{\lfloor \ell/2 \rfloor} \binom{\ell}{2i} C_i$, with $C_i$ the
$i$-th Catalan number, and let $a_{3,\ell}$ be the sum over the integers
$1 \le i \le \lfloor (\ell - 1)/2 \rfloor$ of $\binom{\ell}{2i+1}$ times the integer part of
$4\,(2i+1)!/((i-1)!\,(i+3)!)$. Then $(a_{0,3}, a_{3,3}) = (4, 1)$, $(a_{0,4}, a_{3,4}) = (9, 4)$
and $(a_{0,5}, a_{3,5}) = (21, 14)$.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Table 1. -/
theorem dedekindSixSquaresA0_A3_small :
    (dedekindSixSquaresA0 3, dedekindSixSquaresA3 3) = (4, 1) ∧
      (dedekindSixSquaresA0 4, dedekindSixSquaresA3 4) = (9, 4) ∧
      (dedekindSixSquaresA0 5, dedekindSixSquaresA3 5) = (21, 14) := by
  decide +kernel

/-- **Second and third six-squares moments over a cubic field of negative discriminant.** Let
$K$ be a number field of degree $3$ over $\mathbb{Q}$ with negative discriminant. For $n \ge 1$
let $a_K(n)$ be the number of ideals of the ring of integers of $K$ of absolute norm $n$ and
$r_6(n)$ the number of representations of $n$ as a sum of six squares of integers, and for real
$x$ and natural $\ell$ let $S_\ell(x) = \sum_{1 \le n \le x} r_6(n)\, a_K(n)^\ell$. Then there
are real constants $c_1, c_2$ such that for every $\varepsilon > 0$,
$S_2(x) = c_1 x^3 + c_2 x^3 \log x + O(x^{25/9 + \varepsilon})$ as $x \to \infty$, and there is
a real polynomial $P$ of degree $4$ such that for every $\varepsilon > 0$,
$S_3(x) = x^3 P(\log x) + O(x^{79/27 + \varepsilon})$ as $x \to \infty$.

A cubic field of negative discriminant is not normal over $\mathbb{Q}$.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 1 (`integers-2025-A101-thm-1`). -/
public theorem_wanted sixSquaresDedekindMoment_two_three (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (hD : discr K < 0) :
    (∃ c₁ c₂ : ℝ, ∀ ε : ℝ, 0 < ε →
      (fun x => sixSquaresDedekindMoment K 2 x - c₁ * x ^ 3 - c₂ * x ^ 3 * Real.log x) =O[Filter.atTop]
        fun x => x ^ ((25 : ℝ) / 9 + ε)) ∧
    ∃ P : Polynomial ℝ, P.natDegree = 4 ∧ ∀ ε : ℝ, 0 < ε →
      (fun x => sixSquaresDedekindMoment K 3 x - x ^ 3 * P.eval (Real.log x)) =O[Filter.atTop]
        fun x => x ^ ((79 : ℝ) / 27 + ε)

/-- **Higher six-squares moments over a non-normal cubic field.** Let $K$ be a number field of
degree $3$ over $\mathbb{Q}$ with negative discriminant and let $\ell \ge 4$. For $n \ge 1$ let
$a_K(n)$ be the number of ideals of the ring of integers of $K$ of absolute norm $n$ and $r_6(n)$
the number of representations of $n$ as a sum of six squares of integers, and for real $x$ let
$S_\ell(x) = \sum_{1 \le n \le x} r_6(n)\, a_K(n)^\ell$. Let
$a_{0,\ell} = 1 + \sum_{i=1}^{\lfloor \ell/2 \rfloor} \binom{\ell}{2i} C_i$, with $C_i$ the
$i$-th Catalan number, and let $a_{3,\ell}$ be the sum over the integers
$1 \le i \le \lfloor (\ell - 1)/2 \rfloor$ of $\binom{\ell}{2i+1}$ times the integer part of
$4\,(2i+1)!/((i-1)!\,(i+3)!)$. Then there is a real polynomial $P$ of degree
$a_{0,\ell} + a_{3,\ell} - 1$ such that for every $\varepsilon > 0$,
$S_\ell(x) - x^3 P(\log x) = O(x^{3 - 2/3^\ell + \varepsilon})$ as $x \to \infty$.

Such a field is not normal over $\mathbb{Q}$. The polynomial is called $P_\ell$ for even $\ell$
and $Q_\ell$ for odd $\ell$ in the source.

Source: Naveen K. Godara and Prashant Tiwari, *The Higher Power Moments of the Coefficients of
the Dedekind Zeta Function over a Polynomial in Six Variables*, INTEGERS 25 (2025), Article
A101, Theorem 2 (`integers-2025-A101-thm-2`). -/
public theorem_wanted sixSquaresDedekindMoment_ge_four (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) (hD : discr K < 0) (ℓ : ℕ) (hℓ : 4 ≤ ℓ) :
    ∃ P : Polynomial ℝ, P.natDegree = dedekindSixSquaresA0 ℓ + dedekindSixSquaresA3 ℓ - 1 ∧
      ∀ ε : ℝ, 0 < ε →
        (fun x => sixSquaresDedekindMoment K ℓ x - x ^ 3 * P.eval (Real.log x)) =O[Filter.atTop]
          fun x => x ^ (3 - 2 / (3 : ℝ) ^ ℓ + ε)

end

end MetaMathlibExt
