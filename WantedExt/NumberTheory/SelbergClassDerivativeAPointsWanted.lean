/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# a-points of derivatives of functions in the Selberg class

Statements from M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui,
*On the a-Points of the kth Derivative of an L-Function in the Selberg Class*,
INTEGERS 24 (2024), Article A11.

`SelbergClassFunction` records the axioms of Section 2 of the paper together with the data
`Q_F`, `λ_j`, `μ_j`, `ω` of a functional equation. The derivative `F^(k)` is
`iteratedDeriv k F.toFun`; a-points are counted with multiplicity
(`analyticOrderNatAt` of `F^(k) - a`).

Lemmas 1, 3 and 4 fail as printed for `F = 1` and `a = 0` (then `F^(k)` vanishes
identically and every point is a `0`-point); they are stated under the hypothesis that
`a ≠ 0` or `F` has a nonzero Dirichlet coefficient `a(n)` with `n ≥ 2`, the setting of the
proofs (the paper's own proof of Lemma 1 treats `a ≠ 0` and cites Šimenas, who works with
nonconstant `F`, for `a = 0`).
-/

namespace MetaMathlibExt

open Filter Asymptotics

@[expose] public section

/-- **Functions in the Selberg class.** A function in the Selberg class consists of Dirichlet
coefficients $a \colon \mathbb{N} \to \mathbb{C}$, a function $F \colon \mathbb{C} \to \mathbb{C}$,
a number $r \in \mathbb{N}$ of Gamma factors, a conductor $Q > 0$, real numbers
$\lambda_1, \dots, \lambda_r > 0$, complex numbers $\mu_1, \dots, \mu_r$ with
$\operatorname{Re} \mu_j \ge 0$ and a root number $\omega \in \mathbb{C}$ with $|\omega| = 1$,
such that:

- $a(1) = 1$;
- for every $s$ with $\operatorname{Re} s > 1$ the Dirichlet series $\sum_{n \ge 1} a(n) n^{-s}$
  converges absolutely and equals $F(s)$;
- (Ramanujan hypothesis) for every $\varepsilon > 0$ there is a constant $C$ with
  $|a(n)| \le C n^{\varepsilon}$ for all $n$;
- (Euler product) there are $b \colon \mathbb{N} \to \mathbb{C}$ with $b(n) = 0$ unless $n$ is a
  prime power, a real $\theta < 1/2$ and a constant $C$ with $|b(n)| \le C n^{\theta}$ for all $n$,
  and a real $\sigma_0$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$ the series
  $\sum_{n \ge 1} b(n) n^{-s}$ converges absolutely and $F(s) = \exp \sum_{n \ge 1} b(n) n^{-s}$;
- (analytic continuation) there are $m \in \mathbb{N}$, an entire function $g$ and real numbers
  $\rho$, $A$ with $|g(s)| \le A e^{|s|^{\rho}}$ for all $s$ (so $g$ has finite order) and
  $g(s) = (s - 1)^m F(s)$ for all $s \ne 1$;
- (functional equation) with $\Phi(s) = F(s) Q^s \prod_{j=1}^r \Gamma(\lambda_j s + \mu_j)$, the
  identity $\Phi(s) = \omega \overline{\Phi(1 - \bar s)}$ holds for every $s \ne 0, 1$ such that
  for no $j$ is $\lambda_j s + \mu_j$ or $\lambda_j (1 - \bar s) + \mu_j$ an integer $\le 0$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
structure SelbergClassFunction where
  /-- The Dirichlet coefficients `a(n)`. -/
  coeff : ℕ → ℂ
  /-- The function `F` (its value at the possible pole `s = 1` is irrelevant). -/
  toFun : ℂ → ℂ
  coeff_one : coeff 1 = 1
  lseries : ∀ s : ℂ, 1 < s.re → LSeriesSummable coeff s ∧ LSeries coeff s = toFun s
  ramanujan : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, ‖coeff n‖ ≤ C * (n : ℝ) ^ ε
  eulerProduct : ∃ b : ℕ → ℂ, (∀ n, b n ≠ 0 → IsPrimePow n) ∧
    (∃ θ : ℝ, θ < 1 / 2 ∧ ∃ C : ℝ, ∀ n : ℕ, ‖b n‖ ≤ C * (n : ℝ) ^ θ) ∧
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → LSeriesSummable b s ∧ toFun s = Complex.exp (LSeries b s)
  analyticContinuation : ∃ m : ℕ, ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
    (∃ ρ A : ℝ, ∀ s : ℂ, ‖g s‖ ≤ A * Real.exp (‖s‖ ^ ρ)) ∧
    ∀ s : ℂ, s ≠ 1 → g s = (s - 1) ^ m * toFun s
  /-- The number `r` of Gamma factors. -/
  r : ℕ
  /-- The conductor `Q_F`. -/
  Q : ℝ
  Q_pos : 0 < Q
  /-- The Gamma-factor scalings `λ_j`. -/
  lam : Fin r → ℝ
  lam_pos : ∀ j, 0 < lam j
  /-- The Gamma-factor shifts `μ_j`. -/
  mu : Fin r → ℂ
  mu_re_nonneg : ∀ j, 0 ≤ (mu j).re
  /-- The root number `ω`. -/
  omega : ℂ
  norm_omega : ‖omega‖ = 1
  functionalEquation : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    (∀ j (n : ℕ), (lam j : ℂ) * s + mu j ≠ -(n : ℂ) ∧
      (lam j : ℂ) * (1 - (starRingEnd ℂ) s) + mu j ≠ -(n : ℂ)) →
    toFun s * (Q : ℂ) ^ s * ∏ j, Complex.Gamma ((lam j : ℂ) * s + mu j) =
      omega * (starRingEnd ℂ) (toFun (1 - (starRingEnd ℂ) s) *
        (Q : ℂ) ^ (1 - (starRingEnd ℂ) s) *
        ∏ j, Complex.Gamma ((lam j : ℂ) * (1 - (starRingEnd ℂ) s) + mu j))

namespace SelbergClassFunction

/-- **Degree of a function in the Selberg class.** For a function $F$ in the Selberg class whose
functional equation has Gamma-factor scalings $\lambda_1, \dots, \lambda_r$, the degree of $F$ is
$d_F = 2 \sum_{j=1}^{r} \lambda_j$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
noncomputable def degree (F : SelbergClassFunction) : ℝ :=
  2 * ∑ j, F.lam j

/-- **Nonnegativity of the degree.** Let $F$ be a function in the Selberg class with Gamma-factor
scalings $\lambda_1, \dots, \lambda_r$. Then the degree $d_F = 2 \sum_{j=1}^{r} \lambda_j$
satisfies $d_F \ge 0$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
theorem degree_nonneg (F : SelbergClassFunction) : 0 ≤ F.degree := by
  unfold degree
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ (F.lam_pos j).le
  linarith

/-- **Holomorphy of Selberg class functions away from $s = 1$.** For a function $F$ in the
Selberg class, $F$ is complex differentiable at every $s \in \mathbb{C}$ with $s \ne 1$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
theorem differentiableAt_toFun (F : SelbergClassFunction) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ F.toFun s := by
  obtain ⟨m, g, hg, -, hgeq⟩ := F.analyticContinuation
  have hne : (s - 1) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
  have hev : F.toFun =ᶠ[nhds s] fun w ↦ g w / (w - 1) ^ m := by
    filter_upwards [isOpen_ne.mem_nhds hs] with w hw
    rw [hgeq w hw, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hw))]
  exact ((hg s).div ((differentiableAt_id.sub_const 1).pow m) hne).congr_of_eventuallyEq hev

/-- **Counting function of a-points of derivatives.** Let $F$ be a function in the Selberg class,
$k \in \mathbb{N}$, $a \in \mathbb{C}$ and $E_2, E_1, T \in \mathbb{R}$. Then $N_k(a; T, F)$ is the
number of points $\rho$ with $F^{(k)}(\rho) = a$, where $F^{(k)}$ is the $k$-th derivative of $F$,
in the rectangle $E_2 < \operatorname{Re} \rho < E_1$, $0 < \operatorname{Im} \rho < T$, each
counted with its multiplicity as a zero of $F^{(k)} - a$.

A point near which $F^{(k)} - a$ vanishes identically is given multiplicity $0$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 1 and Section 2. -/
noncomputable def aPointCount (F : SelbergClassFunction) (k : ℕ) (a : ℂ) (E₂ E₁ T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
      iteratedDeriv k F.toFun ρ = a},
    analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - a) ρ

/-- **The a-point count vanishes at nonpositive height.** Let $F$ be a function in the Selberg
class, $k \in \mathbb{N}$, $a \in \mathbb{C}$ and $E_2, E_1 \in \mathbb{R}$. If $T \le 0$, then
$N_k(a; T, F) = 0$, where $N_k(a; T, F)$ is the number of a-points of the $k$-th derivative
$F^{(k)}$, counted with multiplicity, in $E_2 < \operatorname{Re} s < E_1$,
$0 < \operatorname{Im} s < T$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 1. -/
theorem aPointCount_of_nonpos (F : SelbergClassFunction) (k : ℕ) (a : ℂ) (E₂ E₁ : ℝ) {T : ℝ}
    (hT : T ≤ 0) : F.aPointCount k a E₂ E₁ T = 0 := by
  have hempty : {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
      iteratedDeriv k F.toFun ρ = a} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ ↦ ?_
    obtain ⟨-, -, h1, h2, -⟩ := hρ
    linarith
  rw [aPointCount, hempty, finsum_mem_empty]

end SelbergClassFunction

open SelbergClassFunction

/-- **Lemma 1 (no a-points of derivatives far to the right).** Let $F$ be a function in the
Selberg class with Dirichlet coefficients $a(n)$, let $k \ge 1$, and let $a \in \mathbb{C}$ be such
that $a \ne 0$ or $a(n) \ne 0$ for some $n \ge 2$. Then there is a real number $E_1 \ge 1$ such
that the $k$-th derivative $F^{(k)}$ satisfies $F^{(k)}(s) \ne a$ for every $s \in \mathbb{C}$
with $\operatorname{Re} s \ge E_1$.

For $F = 1$ and $a = 0$ every point is a $0$-point, so the hypothesis on $a$ cannot be dropped.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 1 (`integers-2024-A11-lem-1`). -/
public theorem_wanted SelbergClassFunction.exists_no_aPoint_right (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (hF : a ≠ 0 ∨ ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0) :
    ∃ E₁ : ℝ, 1 ≤ E₁ ∧ ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ a

/-- **Asymptotics of the derivatives of the reflected function (Lemma 2).** Let $F$ be a function
in the Selberg class with Gamma-factor data $\lambda_j$, $\mu_j$ for $1 \le j \le r$, conductor
$Q$, root number $\omega$ and degree $d_F = 2 \sum_j \lambda_j$, let $k \ge 1$ and let $c > 1$.
Write $\log$ for the principal branch of the logarithm and put

$$M(s) = \frac{d_F^k}{\pi^r \omega} Q^{2s - 1}
\prod_{j=1}^r \Gamma(\lambda_j s + \mu_j) \Gamma(\lambda_j s + 1 - \lambda_j - \bar\mu_j)
\prod_{j=1}^r \sin\bigl(\pi (\lambda_j + \bar\mu_j - \lambda_j s)\bigr) (\log s)^k F(s).$$

Let $G(w) = \overline{F(1 - \bar w)}$ and let $G^{(k)}$ be its $k$-th derivative. Then there are
real numbers $\tau$ and $C$ such that $|G^{(k)}(s) - M(s)| \le C |M(s)| / |\log s|$ for every
$s \in \mathbb{C}$ with $\operatorname{Re} s > c$ and $|\operatorname{Im} s| \ge \tau$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 2 (`integers-2024-A11-lem-2`). -/
public theorem_wanted SelbergClassFunction.iteratedDeriv_reflected_asymptotic
    (F : SelbergClassFunction) (k : ℕ) (hk : 1 ≤ k) (c : ℝ) (hc : 1 < c) :
    let M : ℂ → ℂ := fun s ↦
      (F.degree : ℂ) ^ k / ((Real.pi : ℂ) ^ F.r * F.omega) * (F.Q : ℂ) ^ (2 * s - 1) *
        (∏ j, Complex.Gamma ((F.lam j : ℂ) * s + F.mu j) *
          Complex.Gamma ((F.lam j : ℂ) * s + 1 - F.lam j - (starRingEnd ℂ) (F.mu j))) *
        (∏ j, Complex.sin (Real.pi * (-(F.lam j : ℂ) * s + F.lam j + (starRingEnd ℂ) (F.mu j)))) *
        Complex.log s ^ k * F.toFun s
    ∃ τ C : ℝ, ∀ s : ℂ, c < s.re → τ ≤ |s.im| →
      ‖iteratedDeriv k (fun w ↦ (starRingEnd ℂ) (F.toFun (1 - (starRingEnd ℂ) w))) s - M s‖ ≤
        C * ‖M s‖ / ‖Complex.log s‖

/-- **No $a$-points of derivatives far to the left (Lemma 3).** Let $F$ be a function in the
Selberg class with Dirichlet coefficients $a(n)$, let $k \ge 1$, and let $a \in \mathbb{C}$ be such
that $a \ne 0$ or $a(n) \ne 0$ for some $n \ge 2$. Then there are real numbers $E_2 \le 0$ and
$\tau$ such that the $k$-th derivative $F^{(k)}$ satisfies $F^{(k)}(s) \ne a$ for every
$s \in \mathbb{C}$ with $\operatorname{Re} s \le E_2$ and $|\operatorname{Im} s| \ge \tau$.

For $F = 1$ and $a = 0$ every point is a $0$-point, so the hypothesis on $a$ cannot be dropped.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 3 (`integers-2024-A11-lem-3`). -/
public theorem_wanted SelbergClassFunction.exists_no_aPoint_left (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (hF : a ≠ 0 ∨ ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0) :
    ∃ E₂ : ℝ, E₂ ≤ 0 ∧ ∃ τ : ℝ, ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| →
      iteratedDeriv k F.toFun s ≠ a

/-- **Lemma 4 (a-points of derivatives in windows of unit height).** Let $F$ be a function in the
Selberg class with Dirichlet coefficients $a(n)$, let $k \ge 1$, and let $a \in \mathbb{C}$ be such
that $a \ne 0$ or $a(n) \ne 0$ for some $n \ge 2$. Let $E_2, E_1$ be real numbers and let
$N_k(a; T, F)$ be the number of a-points of the $k$-th derivative $F^{(k)}$, counted with
multiplicity, in $E_2 < \operatorname{Re} s < E_1$, $0 < \operatorname{Im} s < T$. Then
$N_k(a; T + 1, F) - N_k(a; T, F) = O(\log T)$ as $T \to \infty$.

The paper takes $E_1$ and $E_2$ from Lemmas 1 and 3; the bound is stated here for every strip.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 4 (`integers-2024-A11-lem-4`). -/
public theorem_wanted SelbergClassFunction.aPointCount_unit_window (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (hF : a ≠ 0 ∨ ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0) (E₂ E₁ : ℝ) :
    (fun T : ℝ ↦ (F.aPointCount k a E₂ E₁ (T + 1) : ℝ) - F.aPointCount k a E₂ E₁ T)
      =O[atTop] Real.log

/-- **Local partial-fraction formula at the a-points of the k-th derivative (Lemma 5).** Let $F$
be a function in the Selberg class, let $k \ge 1$, write $F^{(k)}$ for the $k$-th derivative of
$F$, and let $a \in \mathbb{C}$ and let $\sigma_1$, $\sigma_2$ be real numbers. Then there are real
numbers $t_0$ and $C$ such that for every $s \in \mathbb{C}$ with
$\sigma_1 < \operatorname{Re} s < \sigma_2$, $\operatorname{Im} s \ge t_0$ and $F^{(k)}(s) \ne a$,

$$\left| \frac{F^{(k+1)}(s)}{F^{(k)}(s) - a} - \sum_{\rho} \frac{m(\rho)}{s - \rho} \right|
\le C \log \operatorname{Im} s,$$

where $\rho$ runs over the points with $F^{(k)}(\rho) = a$ and
$|\operatorname{Im} \rho - \operatorname{Im} s| \le 1$, and $m(\rho)$ is the order of the zero of
$F^{(k)} - a$ at $\rho$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 5 (`integers-2024-A11-lem-5`). -/
public theorem_wanted SelbergClassFunction.logDeriv_aPoint_partialFraction
    (F : SelbergClassFunction) (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (σ₁ σ₂ : ℝ) :
    ∃ t₀ C : ℝ, ∀ s : ℂ, σ₁ < s.re → s.re < σ₂ → t₀ ≤ s.im → iteratedDeriv k F.toFun s ≠ a →
      ‖iteratedDeriv (k + 1) F.toFun s / (iteratedDeriv k F.toFun s - a) -
          ∑ᶠ ρ ∈ {ρ : ℂ | |ρ.im - s.im| ≤ 1 ∧ iteratedDeriv k F.toFun ρ = a},
            (analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - a) ρ : ℂ) / (s - ρ)‖ ≤
        C * Real.log s.im

/-- **Lemma 6, case a ≠ 0 (expansion of the logarithmic derivative).** Let $F$ be a function in
the Selberg class with Dirichlet coefficients $a(n)$, let $k \ge 1$ and let $a \in \mathbb{C}$ with
$a \ne 0$. Then there is a real number $E$ such that for every $s \in \mathbb{C}$ with
$\operatorname{Re} s \ge E$,
$$
\frac{F^{(k+1)}(s)}{F^{(k)}(s) - a} = \sum_{l \ge 0} \sum_{n_0, \dots, n_l \ge 1}
\frac{(-1)^{k(l+1)}}{a^{l+1}} (\log n_0)^{k+1} (\log n_1 \cdots \log n_l)^k
\frac{a(n_0) \cdots a(n_l)}{n_0^s \cdots n_l^s},
$$
where $F^{(k)}$ is the $k$-th derivative of $F$ and the sum over all pairs of $l \ge 0$ and
positive integers $(n_0, \dots, n_l)$ converges unconditionally (equivalently, absolutely).

The paper sums over $n_i \ge \ell$, where $\ell \ge 2$ is least with $a(\ell) \ne 0$; the added
terms vanish because $\log 1 = 0$ and $a(n) = 0$ for $2 \le n < \ell$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 6 (`integers-2024-A11-lem-6`). -/
public theorem_wanted SelbergClassFunction.hasSum_logDeriv_aPoint_of_ne_zero
    (F : SelbergClassFunction) (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (ha : a ≠ 0) :
    ∃ E : ℝ, ∀ s : ℂ, E ≤ s.re →
      HasSum (fun p : (Σ l : ℕ, Fin (l + 1) → ℕ) ↦
          if ∀ i, 1 ≤ p.2 i then
            (-1) ^ (k * (p.1 + 1)) / a ^ (p.1 + 1) * (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
              (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) *
              (∏ i, F.coeff (p.2 i)) / ∏ i, ((p.2 i : ℕ) : ℂ) ^ s
          else 0)
        (iteratedDeriv (k + 1) F.toFun s / (iteratedDeriv k F.toFun s - a))

/-- **Expansion of the logarithmic derivative of the k-th derivative (Lemma 6, zeros case).**
Let $F$ be a function in the Selberg class with Dirichlet coefficients $a(n)$, write $F^{(k)}$ for
the $k$-th derivative of $F$, let $k \ge 1$, and let $\ell \ge 2$ be such that $a(\ell) \ne 0$
and $a(n) = 0$ for $2 \le n < \ell$. Then there is a real number $E$ such that for every
$s \in \mathbb{C}$ with $\operatorname{Re} s \ge E$,

$$\frac{F^{(k+1)}(s)}{F^{(k)}(s)} = \sum_{l \ge 0} \sum_{n_0, \dots, n_l}
\left(\frac{-1}{a(\ell) (\log \ell)^k}\right)^{l+1} (\log n_0)^{k+1} (\log n_1 \cdots \log n_l)^k
\frac{\ell^{(l+1)s} a(n_0) \cdots a(n_l)}{(n_0 \cdots n_l)^s},$$

where the inner sum runs over the natural numbers $n_0 \ge \ell$ and $n_1, \dots, n_l \ge \ell + 1$,
and the sum over all pairs of $l$ and $(n_0, \dots, n_l)$ converges absolutely.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 6 (`integers-2024-A11-lem-6`). -/
public theorem_wanted SelbergClassFunction.hasSum_logDeriv_zero (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓF : F.coeff ℓ ≠ 0)
    (hmin : ∀ n, 2 ≤ n → n < ℓ → F.coeff n = 0) :
    ∃ E : ℝ, ∀ s : ℂ, E ≤ s.re →
      HasSum (fun p : (Σ l : ℕ, Fin (l + 1) → ℕ) ↦
          if ℓ ≤ p.2 0 ∧ ∀ i : Fin p.1, ℓ + 1 ≤ p.2 i.succ then
            (-1 / (F.coeff ℓ * (Real.log ℓ : ℂ) ^ k)) ^ (p.1 + 1) *
              (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
              (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) *
              (ℓ : ℂ) ^ (((p.1 + 1 : ℕ) : ℂ) * s) *
              (∏ i, F.coeff (p.2 i)) / ∏ i, ((p.2 i : ℕ) : ℂ) ^ s
          else 0)
        (iteratedDeriv (k + 1) F.toFun s / iteratedDeriv k F.toFun s)

/-- **Asymptotic count of a-points of derivatives in the Selberg class.** Let $F$ be a function in
the Selberg class with conductor $Q$, Gamma-factor scalings $\lambda_1, \dots, \lambda_r$ and
degree $d_F$, let $k \ge 1$ and $a \in \mathbb{C}$ with $a \ne 0$, and put
$\lambda = \prod_{j=1}^{r} \lambda_j^{2\lambda_j}$. Let $E_1, E_2, \tau$ be real numbers such that
the $k$-th derivative $F^{(k)}$ satisfies $F^{(k)}(s) \ne a$ whenever $\operatorname{Re} s \ge E_1$,
and $F^{(k)}(s) \ne a$ whenever $\operatorname{Re} s \le E_2$ and $|\operatorname{Im} s| \ge \tau$.
Let $N_k(a; T, F)$ be the number of a-points of $F^{(k)}$, counted with multiplicity, in the
rectangle $E_2 < \operatorname{Re} s < E_1$, $0 < \operatorname{Im} s < T$. Then, as $T \to \infty$,
$$
N_k(a; T, F) = \frac{d_F T}{2\pi} \log T + \frac{T}{2\pi} \log (\lambda Q^2) -
\frac{d_F T}{2\pi} + O(\log T).
$$

The bounds $E_1 \ge 1$ and $E_2 \le 0$ of Lemmas 1 and 3 are not needed and are dropped.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 1 (`integers-2024-A11-thm-1`). -/
public theorem_wanted SelbergClassFunction.aPointCount_asymptotic (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (ha : a ≠ 0) (E₂ E₁ τ : ℝ)
    (h₁ : ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ a)
    (h₂ : ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| → iteratedDeriv k F.toFun s ≠ a) :
    (fun T : ℝ ↦ (F.aPointCount k a E₂ E₁ T : ℝ) -
        (F.degree * T / (2 * Real.pi) * Real.log T +
          T / (2 * Real.pi) * Real.log ((∏ j, F.lam j ^ (2 * F.lam j)) * F.Q ^ 2) -
          F.degree * T / (2 * Real.pi)))
      =O[atTop] Real.log

/-- **Landau-type formula for the a-points of the k-th derivative (Theorem 2, a ≠ 0).** Let $F$ be
a function in the Selberg class with Dirichlet coefficients $a_F(n)$, write $F^{(k)}$ for the
$k$-th derivative of $F$, let $k \ge 1$, let $a \ne 0$ be a complex number and let $x > 1$ be
real. Let $E_1$, $E_2$ and $\tau$ be real numbers such that $F^{(k)}(s) \ne a$ whenever
$\operatorname{Re} s \ge E_1$, and whenever $\operatorname{Re} s \le E_2$ and
$|\operatorname{Im} s| \ge \tau$. Put

$$c = \sum_{l \ge 0} \sum_{n_0 \cdots n_l = x} \frac{(-1)^{k(l+1)}}{a^{l+1}} (\log n_0)^{k+1}
(\log n_1 \cdots \log n_l)^k a_F(n_0) \cdots a_F(n_l),$$

the inner sum over the natural numbers $n_0, \dots, n_l \ge 1$ with product $x$ (only finitely
many terms are nonzero, since a term vanishes when some $n_i = 1$). Then, as $T \to \infty$,

$$\sum_{\rho} m(\rho) x^{\rho} = \frac{T}{2\pi} c + O(\log T),$$

where $\rho$ runs over the points with $F^{(k)}(\rho) = a$, $E_2 < \operatorname{Re} \rho < E_1$
and $0 < \operatorname{Im} \rho < T$, and $m(\rho)$ is the order of the zero of $F^{(k)} - a$ at
$\rho$.

The paper takes $E_1$, $E_2$, $\tau$ from Lemmas 1 and 3 and restricts to $n_i \ge \ell$, where
$\ell \ge 2$ is least with $a_F(\ell) \ne 0$; the added terms vanish. Its closing remark that the
sum is empty for $x \notin \mathbb{Z}$ is immediate from the condition on the $n_i$.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 2 (`integers-2024-A11-thm-2`). -/
public theorem_wanted SelbergClassFunction.sum_aPoint_pow_of_ne_zero (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (ha : a ≠ 0) (x : ℝ) (hx : 1 < x) (E₂ E₁ τ : ℝ)
    (h₁ : ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ a)
    (h₂ : ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| → iteratedDeriv k F.toFun s ≠ a) :
    let c : ℂ := ∑' p : (Σ l : ℕ, Fin (l + 1) → ℕ),
      if (∀ i, 1 ≤ p.2 i) ∧ ((∏ i, p.2 i : ℕ) : ℝ) = x then
        (-1) ^ (k * (p.1 + 1)) / a ^ (p.1 + 1) * (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
          (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) * ∏ i, F.coeff (p.2 i)
      else 0
    (fun T : ℝ ↦ (∑ᶠ ρ ∈ {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
          iteratedDeriv k F.toFun ρ = a},
        (analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - a) ρ : ℂ) * (x : ℂ) ^ ρ) -
        ((T / (2 * Real.pi) : ℝ) : ℂ) * c)
      =O[atTop] Real.log

/-- **Landau-type formula for the zeros of the k-th derivative (Theorem 2, zeros case).** Let $F$
be a function in the Selberg class with Dirichlet coefficients $a(n)$, write $F^{(k)}$ for the
$k$-th derivative of $F$, let $k \ge 1$, let $\ell \ge 2$ be such that $a(\ell) \ne 0$ and
$a(n) = 0$ for $2 \le n < \ell$, and let $x > 1$ be real. Let $E_1$, $E_2$ and $\tau$ be real
numbers such that $F^{(k)}(s) \ne 0$ whenever $\operatorname{Re} s \ge E_1$, and whenever
$\operatorname{Re} s \le E_2$ and $|\operatorname{Im} s| \ge \tau$. Put

$$c = \sum_{l \ge 0} \sum_{n_0, \dots, n_l} \left(\frac{-1}{a(\ell) (\log \ell)^k}\right)^{l+1}
(\log n_0)^{k+1} (\log n_1 \cdots \log n_l)^k a(n_0) \cdots a(n_l),$$

the inner sum over the natural numbers $n_0 \ge \ell$ and $n_1, \dots, n_l \ge \ell + 1$ with
$n_0 \cdots n_l = x \ell^{l+1}$ (a finite sum, since $n_0 \cdots n_l \ge \ell (\ell + 1)^l$).
Then, as $T \to \infty$,

$$\sum_{\rho} m(\rho) x^{\rho} = \frac{T}{2\pi} c + O(\log T),$$

where $\rho$ runs over the zeros of $F^{(k)}$ with $E_2 < \operatorname{Re} \rho < E_1$ and
$0 < \operatorname{Im} \rho < T$, and $m(\rho)$ is the order of the zero of $F^{(k)}$ at $\rho$.

The paper takes $E_1$, $E_2$, $\tau$ from Lemmas 1 and 3. Its closing remark that the sum is
empty when $\ell^n x \notin \mathbb{Z}$ for all $n$ is not stated separately.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 2 (`integers-2024-A11-thm-2`). -/
public theorem_wanted SelbergClassFunction.sum_zero_pow (F : SelbergClassFunction) (k : ℕ)
    (hk : 1 ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓF : F.coeff ℓ ≠ 0)
    (hmin : ∀ n, 2 ≤ n → n < ℓ → F.coeff n = 0) (x : ℝ) (hx : 1 < x) (E₂ E₁ τ : ℝ)
    (h₁ : ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ 0)
    (h₂ : ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| → iteratedDeriv k F.toFun s ≠ 0) :
    let c : ℂ := ∑' p : (Σ l : ℕ, Fin (l + 1) → ℕ),
      if ℓ ≤ p.2 0 ∧ (∀ i : Fin p.1, ℓ + 1 ≤ p.2 i.succ) ∧
          ((∏ i, p.2 i : ℕ) : ℝ) = x * (ℓ : ℝ) ^ (p.1 + 1) then
        (-1 / (F.coeff ℓ * (Real.log ℓ : ℂ) ^ k)) ^ (p.1 + 1) *
          (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
          (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) * ∏ i, F.coeff (p.2 i)
      else 0
    (fun T : ℝ ↦ (∑ᶠ ρ ∈ {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
          iteratedDeriv k F.toFun ρ = 0},
        (analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - 0) ρ : ℂ) * (x : ℂ) ^ ρ) -
        ((T / (2 * Real.pi) : ℝ) : ℂ) * c)
      =O[atTop] Real.log

end

end MetaMathlibExt
