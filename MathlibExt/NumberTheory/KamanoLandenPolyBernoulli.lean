/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Basic.Real.Basic

/-!
# Kamano's generalized Landen connection formula and poly-Bernoulli numbers

This file develops, formally in `ℝ⟦X⟧`, Kamano's generalized multiple polylogarithms
`generalizedMultiplePolylog D β γ k` attached to Landen data `D` (a matrix
`g₀ = (1 -1; c₀ d₀)` and matrices `g₁, …, gₛ`), and the generalized poly-Bernoulli numbers of the
first kind `generalizedPolyBernoulliC`. Its main result is the Landen formula for these numbers,
`generalizedPolyBernoulliC_landen`: for Landen data whose matrices `g₁, …, gₛ` are invertible,
`C_n^{(k, g, (β, γ))} = (-1)^{n+1} n! [tⁿ] d/dt Li_{k↑}(g̃; (β, γ); z(t))`, where `g̃ = D.tilde`
is the transformed data and `z(t) = (eᵗ - 1)/(c₀ eᵗ + d₀)` is the variable of `g`
(`landenExpVariable`).

The definitions, their basic lemmas and the statement of the main theorem come from the wanted
module `WantedExt.NumberTheory.KamanoLandenPolyBernoulliWanted`, with the same names, statements
and docstrings; their docstrings give the sources.

## Encoding

* For a matrix `g = (a b; c d)`, the function `G_g(t) = c/(a - c t) - d/(b - d t)` has at most a
  simple pole at `0`, so the power series `u · G_g(u)` is stored instead (`landenFormSeries`).
* For `h` with zero constant term, `∫₀^z h(u) du / u` is `integralDivX h`; every integration step
  of the recursion defining the polylogarithms has this form.
* Indices are lists of natural numbers, read from their last entry by `LandenData.polylogRev`.

## Proof of the Landen formula

Put `e = c₀ - d₀`, `w = ∑ eᵐ zᵐ = (1 - e z)⁻¹` and `φ = -z w = z / (e z - 1)`.

1. For `a, c` not both zero, the series `F = c u / (a - c u)` (`linearFractionalPoleSeries`)
   satisfies `w · F(φ) = F̃ - e z w` with `F̃ = c' z / (a - c' z)` and `c' = e a - c`: both sides
   agree after multiplication by the non-zero series `(a - c' z)(1 - e z)`. The terms `- e z w`
   cancel in `landenFormSeries`, so `w · Φ(φ) = Φ̃` for the weighted form series `Φ` of `g` and
   `Φ̃` of `g̃`, when the matrices `g₁, …, gₛ` are invertible.
2. Since `φ' = -w²`, the chain rule (`PowerSeries.derivative_subst`) gives
   `integralDivX h ∘ φ = integralDivX (w · (h ∘ φ))` for every `h` with zero constant term.
3. By induction along the recursion of `LandenData.polylogRev`, steps 1 and 2 give the
   generalized Landen connection formula `Li_k(g; (β, γ); φ) = Li_k(g̃; (β, γ); z)` for every
   list `k` (a private lemma below).
4. A computation with `eᵗ e⁻ᵗ = 1` shows `φ(z(t)) = z(-t)`. Hence
   `Li_{k↑}(g̃; z(t)) = Li_{k↑}(g; z(-t))`, and differentiating `F(-t)` multiplies the coefficient
   of `tⁿ` in `d/dt F` by `(-1)^{n+1}`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Linear fractional pole series.** For real numbers $a$ and $c$, this is the power series
$F_{a,c}(u)$ of $\frac{cu}{a - cu}$: it is $\sum_{n \ge 1} (c/a)^n u^n$ if $a \neq 0$, the
constant $-1$ if $a = 0$ and $c \neq 0$, and $0$ (a junk value) if $a = c = 0$. It is $u$
times the summand $\frac{c}{a - cu}$ of $G_g(u) = \frac{c}{a - cu} - \frac{d}{b - du}$ for
the matrix $g$ with rows $(a, b)$ and $(c, d)$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the function `G_g(t)` before Table 1. -/
public noncomputable def linearFractionalPoleSeries (a c : ℝ) : ℝ⟦X⟧ :=
  if a = 0 then (if c = 0 then 0 else -1)
  else mk fun n => if n = 0 then 0 else (c / a) ^ n

/-- **The linear fractional pole series solves its defining equation.** For all real numbers
$a$ and $c$, the linear fractional pole series $F_{a,c}(u)$, the power series of
$\frac{cu}{a - cu}$, satisfies $(a - cu) \cdot F_{a,c}(u) = cu$ in $\mathbb{R}[[u]]$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the function `G_g(t)` before Table 1. -/
public theorem linearFractionalPoleSeries_spec (a c : ℝ) :
    (C a - C c * X) * linearFractionalPoleSeries a c = C c * X := by
  unfold linearFractionalPoleSeries
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · simp [ha, hc]
    · simp [ha, hc]
  · simp only [ha, ite_false]
    ext n
    rw [sub_mul, map_sub, coeff_C_mul, mul_assoc, coeff_C_mul]
    rcases n with _ | _ | n
    · simp
    · simp [coeff_succ_X_mul]
      field_simp
    · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_C_mul, coeff_X]
      have h1 : n + 1 + 1 ≠ 1 := by omega
      simp only [Nat.succ_ne_zero, ite_false, h1, mul_zero]
      rw [pow_succ (c / a) (n + 1)]
      field_simp
      ring

/-- **Landen form series.** For real numbers $a, b, c, d$, viewed as the matrix $g$ with rows
$(a, b)$ and $(c, d)$, this is the power series
$u \cdot G_g(u) = \frac{cu}{a - cu} - \frac{du}{b - du} \in \mathbb{R}[[u]]$, where
$G_g(t) = \frac{c}{a - ct} - \frac{d}{b - dt}$. Here the power series of $\frac{cu}{a - cu}$ is
$\sum_{n \ge 1} (c/a)^n u^n$ if $a \neq 0$, the constant $-1$ if $a = 0$ and $c \neq 0$, and
$0$ if $a = c = 0$; likewise for $\frac{du}{b - du}$ with $b, d$ in place of $a, c$. For
$g \in GL_2(\mathbb{R})$ the last case does not occur.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the function `G_g(t)` before Table 1. -/
public noncomputable def landenFormSeries (a b c d : ℝ) : ℝ⟦X⟧ :=
  linearFractionalPoleSeries a c - linearFractionalPoleSeries b d

/-- **Landen form series of the identity matrix.** For the identity matrix $g$, with rows $(1, 0)$
and $(0, 1)$, the Landen form series $u \cdot G_g(u)$ is the constant power series $1$ in
$\mathbb{R}[[u]]$; that is, $G_g(t) = 1/t$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Table 1. -/
public theorem landenFormSeries_identity : landenFormSeries 1 0 0 1 = 1 := by
  ext n
  rcases n with _ | n <;> simp [landenFormSeries, linearFractionalPoleSeries]

/-- **Formal integral against $du/u$.** For a real power series $h$, this is the power series
$\int_0^z h(u)\,du/u$ computed coefficientwise: for $n \ge 1$ its coefficient of $z^n$ is the
coefficient of $u^n$ in $h$ divided by $n$, and its constant coefficient is $0$. The constant
coefficient of $h$ is ignored, so this is the termwise integral only when $h$ has zero constant
term.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the integrals defining `Li_k(g; (β, γ); z)`. -/
public noncomputable def integralDivX (h : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  mk fun n => coeff n h / n

/-- **The formal integral against $du/u$ is a right inverse of $z \, d/dz$.** Let
$h \in \mathbb{R}[[z]]$ be a power series with zero constant term, and let
$I(h) = \sum_{n \ge 1} \frac{[z^n] h}{n} z^n$ be its formal integral $\int_0^z h(u) \, du / u$,
where $[z^n] h$ is the coefficient of $z^n$ in $h$. Then $I(h)$ has zero constant term and
$z \, \frac{d}{dz} I(h) = h$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
the integrals defining `Li_k(g; (β, γ); z)`. -/
public theorem integralDivX_spec (h : ℝ⟦X⟧) (h0 : constantCoeff h = 0) :
    constantCoeff (integralDivX h) = 0 ∧ X * derivative (integralDivX h) = h := by
  refine ⟨by rw [← coeff_zero_eq_constantCoeff_apply]; simp [integralDivX], ?_⟩
  ext n
  rcases n with _ | n
  · rw [coeff_zero_eq_constantCoeff_apply] at *
    simp [h0]
  · rw [coeff_succ_X_mul, coeff_derivative, integralDivX, coeff_mk]
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at this ⊢
    field_simp

/-- **Landen data.** Landen data $g = (g_0, g_1, \dots, g_s)$ consist of a natural number $s$,
real numbers $c_0, d_0$, and real numbers $a_i, b_i, c_i, d_i$ for $1 \le i \le s$. They
encode the real $2 \times 2$ matrix $g_0$ with rows $(1, -1)$ and $(c_0, d_0)$ and, for
$1 \le i \le s$, the matrix $g_i$ with rows $(a_i, b_i)$ and $(c_i, d_i)$. No invertibility is
required.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public structure LandenData where
  /-- The number `s` of matrices `g_1, …, g_s`. -/
  s : ℕ
  /-- The entry `c₀` of `g₀ = (1 -1; c₀ d₀)`. -/
  c₀ : ℝ
  /-- The entry `d₀` of `g₀ = (1 -1; c₀ d₀)`. -/
  d₀ : ℝ
  /-- The upper-left entries `a_i` of `g_i`. -/
  a : Fin s → ℝ
  /-- The upper-right entries `b_i` of `g_i`. -/
  b : Fin s → ℝ
  /-- The lower-left entries `c_i` of `g_i`. -/
  c : Fin s → ℝ
  /-- The lower-right entries `d_i` of `g_i`. -/
  d : Fin s → ℝ

namespace LandenData

/-- **Transformed Landen data.** For Landen data $g = (g_0, g_1, \dots, g_s)$ with
$g_0 = \begin{pmatrix} 1 & -1 \\ c_0 & d_0 \end{pmatrix}$ and
$g_i = \begin{pmatrix} a_i & b_i \\ c_i & d_i \end{pmatrix}$ for $1 \le i \le s$, the transformed
data $\tilde g = (\tilde g_0, \tilde g_1, \dots, \tilde g_s)$ has the same $s$, with
$\tilde g_0 = \begin{pmatrix} 1 & -1 \\ -d_0 & -c_0 \end{pmatrix}$ and, for $1 \le i \le s$, the
matrix $\tilde g_i$ has first row $(a_i, b_i)$ and second row
$((c_0 - d_0) a_i - c_i, (c_0 - d_0) b_i - d_i)$. Equivalently,
$\tilde g_i = \begin{pmatrix} 1 & 0 \\ c_0 - d_0 & -1 \end{pmatrix} g_i$ for $0 \le i \le s$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
display before Theorem 2. -/
public def tilde (D : LandenData) : LandenData where
  s := D.s
  c₀ := -D.d₀
  d₀ := -D.c₀
  a := D.a
  b := D.b
  c := fun i => (D.c₀ - D.d₀) * D.a i - D.c i
  d := fun i => (D.c₀ - D.d₀) * D.b i - D.d i

/-- **The transformation of Landen data is an involution.** For Landen data
$g = (g_0, g_1, \dots, g_s)$ with $g_0 = \begin{pmatrix} 1 & -1 \\ c_0 & d_0 \end{pmatrix}$, let
$\tilde g$ be the transformed data, given by
$\tilde g_i = \begin{pmatrix} 1 & 0 \\ c_0 - d_0 & -1 \end{pmatrix} g_i$ for $0 \le i \le s$.
Then the transformed data of $\tilde g$ is $g$ itself: $\tilde{\tilde g} = g$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
remark before Theorem 2. -/
public theorem tilde_tilde (D : LandenData) : D.tilde.tilde = D := by
  cases D
  simp only [tilde, mk.injEq, neg_neg, heq_eq_eq, true_and]
  constructor <;> funext i <;> ring

/-- **Weighted form series.** Let $g = (g_0, g_1, \dots, g_s)$ be Landen data, where $g_i$ has
rows $(a_i, b_i)$ and $(c_i, d_i)$ for $1 \le i \le s$, and let $w_1, \dots, w_s$ be real
numbers. The weighted form series of $g$ with weights $w$ is the formal power series
$u \sum_{i=1}^{s} w_i G_{g_i}(u) \in \mathbb{R}[[u]]$, where $u\,G_{g_i}(u)$ is the Landen form
series of $g_i$: the expansion of $\frac{c_i u}{a_i - c_i u} - \frac{d_i u}{b_i - d_i u}$, a
fraction with zero numerator and zero denominator being read as $0$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
definition of `Li_k(g; (β, γ); z)`. -/
public noncomputable def formSeries (D : LandenData) (w : Fin D.s → ℝ) : ℝ⟦X⟧ :=
  ∑ i, C (w i) * landenFormSeries (D.a i) (D.b i) (D.c i) (D.d i)

/-- **Reversed recursion for Kamano's generalized multiple polylogarithm.** Fix Landen data $g$,
with $g_0 = \begin{pmatrix} 1 & -1 \\ c_0 & d_0 \end{pmatrix}$ and
$g_i = \begin{pmatrix} a_i & b_i \\ c_i & d_i \end{pmatrix}$ for $1 \le i \le s$, and weights
$\beta, \gamma \in \mathbb{R}^s$. For a real matrix
$h = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ let $z\,G_h(z) \in \mathbb{R}[[z]]$ be the
power series of $\frac{cz}{a - cz} - \frac{dz}{b - dz}$, where a term whose numerator and
denominator are both $0$ is read as $0$; for $w \in \mathbb{R}^s$ let
$\Phi_w = \sum_{i=1}^s w_i \, z\,G_{g_i}(z) \in \mathbb{R}[[z]]$; and for
$f = \sum_n f_n z^n \in \mathbb{R}[[z]]$ let $I(f) = \sum_{n \ge 1} (f_n / n) z^n$, which is the
formal integral $\int_0^z f(u) \, du / u$ when $f_0 = 0$. For a finite list $\ell$ of natural
numbers, the series $L(\ell) \in \mathbb{R}[[z]]$ is defined recursively: $L(\ell) = 0$ if $\ell$
is empty or its first entry is $0$; $L((1)) = I(z\,G_{g_0}(z))$;
$L((1, r, \ell')) = I(\Phi_\gamma \cdot L((r, \ell')))$ for every natural number $r$ and list
$\ell'$; and $L((n + 2, \ell')) = I(\Phi_\beta \cdot L((n + 1, \ell')))$ for every natural
number $n$ and list $\ell'$.

Applied to the reversed list $(k_r, \dots, k_1)$ of an index $k = (k_1, \dots, k_r)$, $L$ gives
Kamano's generalized multiple polylogarithm $\mathrm{Li}_k(g; (\beta, \gamma); z)$. A list with a
zero entry anywhere gives $0$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
display (6) and the two inductive integrals before it. -/
public noncomputable def polylogRev (D : LandenData) (β γ : Fin D.s → ℝ) :
    List ℕ → ℝ⟦X⟧
  | [] => 0
  | 0 :: _ => 0
  | [1] => integralDivX (landenFormSeries 1 (-1) D.c₀ D.d₀)
  | 1 :: r :: rs => integralDivX (D.formSeries γ * polylogRev D β γ (r :: rs))
  | (n + 2) :: rs => integralDivX (D.formSeries β * polylogRev D β γ ((n + 1) :: rs))
termination_by l => l.sum

end LandenData

/-- **Kamano's generalized multiple polylogarithm.** Let $g = (g_0, g_1, \dots, g_s)$ be Landen
data, where $g_0$ has rows $(1, -1)$ and $(c_0, d_0)$ and $g_i$ has rows $(a_i, b_i)$ and
$(c_i, d_i)$, and let $\beta, \gamma \in \mathbb{R}^s$. For a matrix $h$ with rows $(a, b)$ and
$(c, d)$ put $G_h(u) = \frac{c}{a - c u} - \frac{d}{b - d u}$, a fraction with zero numerator and
zero denominator being read as $0$. For an index $\mathbf{k} = (k_1, \dots, k_r)$ of positive
integers put $\mathbf{k}{\uparrow} = (k_1, \dots, k_r + 1)$ and
$\mathbf{k}{\rightarrow} = (k_1, \dots, k_r, 1)$. The generalized multiple polylogarithm
$\mathrm{Li}_{\mathbf{k}} = \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); z) \in \mathbb{R}[[z]]$
is defined recursively by
$\mathrm{Li}_{(1)} = \int_0^z \left(\frac{c_0}{1 - c_0 u} + \frac{d_0}{1 + d_0 u}\right) du$,
$\mathrm{Li}_{\mathbf{k}{\uparrow}} =
\int_0^z \sum_{i=1}^{s} \beta_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(u)\,du$ and
$\mathrm{Li}_{\mathbf{k}{\rightarrow}} =
\int_0^z \sum_{i=1}^{s} \gamma_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(u)\,du$, where
integrals of power series are taken term by term. A list of natural numbers that is empty or has
a zero entry gives $0$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
display (6). -/
public noncomputable def generalizedMultiplePolylog (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) : ℝ⟦X⟧ :=
  D.polylogRev β γ k.reverse

/-- **Initial value of the generalized multiple polylogarithm.** Let
$g = (g_0, g_1, \dots, g_s)$ be Landen data, where $g_0$ has rows $(1, -1)$ and $(c_0, d_0)$,
and let $\beta, \gamma \in \mathbb{R}^s$. Then
$\mathrm{Li}_{(1)}(g; (\beta, \gamma); z) = \int_0^z G_{g_0}(u)\,du$, where
$u\,G_{g_0}(u) = \frac{c_0 u}{1 - c_0 u} + \frac{d_0 u}{1 + d_0 u}$ is the Landen form series of
$g_0$ and the integral of a power series is taken term by term.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, display (6). -/
public theorem generalizedMultiplePolylog_one (D : LandenData) (β γ : Fin D.s → ℝ) :
    generalizedMultiplePolylog D β γ [1] =
      integralDivX (landenFormSeries 1 (-1) D.c₀ D.d₀) := by
  simp [generalizedMultiplePolylog, LandenData.polylogRev]

/-- **Recurrence for raising the last entry.** Let $g = (g_0, g_1, \dots, g_s)$ be Landen data and
let $\beta, \gamma \in \mathbb{R}^s$. For every list $(k_1, \dots, k_{r-1})$ of natural numbers
(possibly empty) and every natural number $m$, writing $\mathbf{k} = (k_1, \dots, k_{r-1}, m + 1)$,
$\mathrm{Li}_{(k_1, \dots, k_{r-1}, m + 2)}(g; (\beta, \gamma); z) =
\int_0^z \sum_{i=1}^{s} \beta_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); u)\,du$,
where $u \sum_{i} \beta_i G_{g_i}(u)$ is the weighted form series of $g$ with weights $\beta$
and the integral of a power series is taken term by term.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public theorem generalizedMultiplePolylog_up (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (m : ℕ) :
    generalizedMultiplePolylog D β γ (k ++ [m + 2]) =
      integralDivX (D.formSeries β * generalizedMultiplePolylog D β γ (k ++ [m + 1])) := by
  simp [generalizedMultiplePolylog, LandenData.polylogRev]

/-- **Recurrence for appending the entry 1.** Let $g = (g_0, g_1, \dots, g_s)$ be Landen data and
let $\beta, \gamma \in \mathbb{R}^s$. For every nonempty list $\mathbf{k} = (k_1, \dots, k_r)$ of
natural numbers,
$\mathrm{Li}_{(k_1, \dots, k_r, 1)}(g; (\beta, \gamma); z) =
\int_0^z \sum_{i=1}^{s} \gamma_i G_{g_i}(u) \, \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); u)\,du$,
where $u \sum_{i} \gamma_i G_{g_i}(u)$ is the weighted form series of $g$ with weights $\gamma$
and the integral of a power series is taken term by term.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public theorem generalizedMultiplePolylog_right (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (hk : k ≠ []) :
    generalizedMultiplePolylog D β γ (k ++ [1]) =
      integralDivX (D.formSeries γ * generalizedMultiplePolylog D β γ k) := by
  obtain ⟨r, rs, h⟩ : ∃ r rs, k.reverse = r :: rs := by
    cases hr : k.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp hr) hk
    | cons r rs => exact ⟨r, rs, rfl⟩
  simp [generalizedMultiplePolylog, h, LandenData.polylogRev]

/-- **Landen exponential variable.** For Landen data $g$ whose matrix $g_0$ has rows $(1, -1)$
and $(c_0, d_0)$, this is the formal power series $z(t) = (e^t - 1)(c_0 e^t + d_0)^{-1}$ in
$\mathbb{R}[[t]]$. The inverse is the power series inverse, which exists exactly when
$c_0 + d_0 \neq 0$; when $c_0 + d_0 = 0$ the inverse is taken to be $0$, so $z(t) = 0$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4,
definition of `C_n^{(k, g, (β, γ))}`. -/
public noncomputable def landenExpVariable (D : LandenData) : ℝ⟦X⟧ :=
  (exp ℝ - 1) * (C D.c₀ * exp ℝ + C D.d₀)⁻¹

/-- **Defining relation of the Landen exponential variable.** Let $g$ be Landen data whose
matrix $g_0$ has rows $(1, -1)$ and $(c_0, d_0)$ with $c_0 + d_0 \neq 0$, and let
$z(t) = (e^t - 1)(c_0 e^t + d_0)^{-1} \in \mathbb{R}[[t]]$ be its Landen exponential variable.
Then $(c_0 e^t + d_0)\, z(t) = e^t - 1$ in $\mathbb{R}[[t]]$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public theorem landenExpVariable_spec (D : LandenData) (h : D.c₀ + D.d₀ ≠ 0) :
    (C D.c₀ * exp ℝ + C D.d₀) * landenExpVariable D = exp ℝ - 1 := by
  have h0 : constantCoeff (C D.c₀ * exp ℝ + C D.d₀) ≠ 0 := by simpa using h
  rw [landenExpVariable, mul_comm, mul_assoc, PowerSeries.inv_mul_cancel _ h0, mul_one]

/-- **Generalized poly-Bernoulli numbers of the first kind.** Let $g = (g_0, g_1, \dots, g_s)$ be
Landen data, where $(c_0, d_0)$ is the bottom row of the matrix $g_0$, let
$\beta, \gamma \in \mathbb{R}^s$, and let $k = (k_1, \dots, k_r)$ be a list of natural numbers;
write $k\uparrow = (k_1, \dots, k_r + 1)$, with $k\uparrow = ()$ when $k$ is empty. Let
$z(t) \in \mathbb{R}[[t]]$ be the power series of $(e^t - 1)/(c_0 e^t + d_0)$ (the zero series
when $c_0 + d_0 = 0$). The numbers $C_n^{(k, g, (\beta, \gamma))} \in \mathbb{R}$, $n \ge 0$, are
defined by
$$\frac{d}{dt} \mathrm{Li}_{k\uparrow}(g; (\beta, \gamma); z(t)) =
\sum_{n \ge 0} C_n^{(k, g, (\beta, \gamma))} \frac{t^n}{n!},$$
where $\mathrm{Li}_{k\uparrow}(g; (\beta, \gamma); z)$ is Kamano's generalized multiple
polylogarithm, into which the series $z(t)$ is substituted.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public noncomputable def generalizedPolyBernoulliC (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (n : ℕ) : ℝ :=
  n.factorial * coeff n (derivative (subst (landenExpVariable D)
    (generalizedMultiplePolylog D β γ (k.modifyLast (· + 1)))))

/-- **Generalized poly-Bernoulli numbers $C_n$ as Taylor coefficients.** Let
$g = (g_0, g_1, \dots, g_s)$ be Landen data, where $(c_0, d_0)$ is the bottom row of the matrix
$g_0$, let $\beta, \gamma \in \mathbb{R}^s$, let $k = (k_1, \dots, k_r)$ be a list of natural
numbers, and write $k\uparrow = (k_1, \dots, k_r + 1)$, with $k\uparrow = ()$ when $k$ is empty.
Let $z(t) \in \mathbb{R}[[t]]$ be the power series of $(e^t - 1)/(c_0 e^t + d_0)$ (the zero
series when $c_0 + d_0 = 0$). Then for every $n \ge 0$ the generalized poly-Bernoulli number of
the first kind satisfies
$$C_n^{(k, g, (\beta, \gamma))} =
(n + 1)! \, [t^{n+1}] \, \mathrm{Li}_{k\uparrow}(g; (\beta, \gamma); z(t)),$$
where $[t^m] F$ is the coefficient of $t^m$ in a power series $F$ and $\mathrm{Li}$ is Kamano's
generalized multiple polylogarithm.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public theorem generalizedPolyBernoulliC_eq_coeff (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (n : ℕ) :
    generalizedPolyBernoulliC D β γ k n = (n + 1).factorial * coeff (n + 1)
      (subst (landenExpVariable D) (generalizedMultiplePolylog D β γ (k.modifyLast (· + 1)))) := by
  rw [generalizedPolyBernoulliC, coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

/-! ### Auxiliary lemmas for the Landen formula -/

namespace generalizedPolyBernoulliC_landen

/-- The geometric series `∑ eᵐ zᵐ` inverts `1 - e z`. -/
private theorem one_sub_C_mul_X_mul_geom (e : ℝ) :
    (1 - C e * X) * (mk fun m => e ^ m : ℝ⟦X⟧) = 1 := by
  ext n
  rcases n with _ | n
  · simp
  · rw [sub_mul, map_sub, one_mul, mul_assoc, coeff_C_mul, coeff_succ_X_mul]
    simp only [coeff_mk, coeff_one, Nat.add_one_ne_zero, ite_false, pow_succ]
    ring

private theorem derivative_geom (e : ℝ) :
    derivative (mk fun m => e ^ m : ℝ⟦X⟧) = C e * (mk fun m => e ^ m) ^ 2 := by
  have h := congrArg derivative (one_sub_C_mul_X_mul_geom e)
  rw [Derivation.leibniz, map_sub, derivative_one, Derivation.leibniz, derivative_C,
    derivative_X] at h
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub] at h
  linear_combination (mk fun m => e ^ m : ℝ⟦X⟧) * h -
    derivative (mk fun m => e ^ m : ℝ⟦X⟧) * one_sub_C_mul_X_mul_geom e

/-- The derivative of `φ = -z ∑ eᵐ zᵐ = z / (e z - 1)` is `-(∑ eᵐ zᵐ)²`. -/
private theorem derivative_neg_X_mul_geom (e : ℝ) :
    derivative (-(X * mk fun m => e ^ m) : ℝ⟦X⟧) = -(mk fun m => e ^ m : ℝ⟦X⟧) ^ 2 := by
  rw [map_neg, Derivation.leibniz, derivative_X, derivative_geom]
  simp only [smul_eq_mul]
  linear_combination (mk fun m => e ^ m : ℝ⟦X⟧) * one_sub_C_mul_X_mul_geom e

private theorem C_sub_C_mul_X_ne_zero {a c : ℝ} (h : ¬(a = 0 ∧ c = 0)) :
    (C a - C c * X : ℝ⟦X⟧) ≠ 0 := by
  intro H
  apply h
  have h0 := congrArg (coeff 0) H
  have h1 := congrArg (coeff 1) H
  simp only [coeff_zero_eq_constantCoeff, map_sub, constantCoeff_C, map_mul, constantCoeff_X,
    mul_zero, sub_zero, coeff_succ_C, coeff_succ_mul_X, coeff_zero_C, zero_sub, map_zero,
    neg_eq_zero] at h0 h1
  exact ⟨h0, h1⟩

private theorem one_sub_C_mul_X_ne_zero (e : ℝ) : (1 - C e * X : ℝ⟦X⟧) ≠ 0 := by
  intro H
  simpa using congrArg (coeff 0) H

private theorem hasSubst_neg_X_mul (w : ℝ⟦X⟧) : HasSubst (-(X * w)) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/-- Substituting `φ = z / (e z - 1)` into `c u / (a - c u)` and multiplying by `φ / (-z)` gives
`c' z / (a - c' z) - e z / (1 - e z)` with `c' = e a - c`, unless `a = c = 0`. -/
private theorem mul_subst_linearFractionalPoleSeries (e : ℝ) {a c : ℝ}
    (h : ¬(a = 0 ∧ c = 0)) :
    (mk fun m => e ^ m) *
        subst (-(X * mk fun m => e ^ m) : ℝ⟦X⟧) (linearFractionalPoleSeries a c) =
      linearFractionalPoleSeries a (e * a - c) - C e * X * mk fun m => e ^ m := by
  set w : ℝ⟦X⟧ := mk fun m => e ^ m
  have hφ := hasSubst_neg_X_mul w
  have h1 := congrArg (subst (-(X * w))) (linearFractionalPoleSeries_spec a c)
  simp only [subst_mul hφ, subst_sub hφ, subst_C, subst_X hφ] at h1
  change (C a - C c * -(X * w)) * subst (-(X * w)) (linearFractionalPoleSeries a c) =
    C c * -(X * w) at h1
  have h2 := linearFractionalPoleSeries_spec a (e * a - c)
  have hM : (C a - C (e * a - c) * X) * (1 - C e * X) ≠ 0 :=
    mul_ne_zero (C_sub_C_mul_X_ne_zero (by rintro ⟨rfl, hc⟩; exact h ⟨rfl, by linarith⟩))
      (one_sub_C_mul_X_ne_zero e)
  apply mul_left_cancel₀ hM
  rw [map_sub, map_mul] at h2 ⊢
  set S := subst (-(X * w)) (linearFractionalPoleSeries a c)
  linear_combination (1 - C e * X) * h1 - (1 - C e * X) * h2 +
    ((C a - (C e * C a - C c) * X) * S - C c * X * S - C c * X +
      C e * X * (C a - (C e * C a - C c) * X)) * one_sub_C_mul_X_mul_geom e

private theorem mul_subst_landenFormSeries (e : ℝ) {a b c d : ℝ} (hac : ¬(a = 0 ∧ c = 0))
    (hbd : ¬(b = 0 ∧ d = 0)) :
    (mk fun m => e ^ m) * subst (-(X * mk fun m => e ^ m) : ℝ⟦X⟧) (landenFormSeries a b c d) =
      landenFormSeries a b (e * a - c) (e * b - d) := by
  rw [landenFormSeries, landenFormSeries, subst_sub (hasSubst_neg_X_mul _), mul_sub,
    mul_subst_linearFractionalPoleSeries e hac, mul_subst_linearFractionalPoleSeries e hbd]
  ring

/-- The transformed Landen data `D.tilde`, written as a structure instance. Its field `s` is
syntactically `D.s`, so that `rw` and `simp` accept terms such as
`(tildeData D).polylogRev β γ l` with `β : Fin D.s → ℝ`. -/
private abbrev tildeData (D : LandenData) : LandenData :=
  ⟨D.s, -D.d₀, -D.c₀, D.a, D.b, fun i => (D.c₀ - D.d₀) * D.a i - D.c i,
    fun i => (D.c₀ - D.d₀) * D.b i - D.d i⟩

private theorem mul_subst_formSeries (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (v : Fin D.s → ℝ) :
    (mk fun m => (D.c₀ - D.d₀) ^ m) *
        subst (-(X * mk fun m => (D.c₀ - D.d₀) ^ m) : ℝ⟦X⟧) (D.formSeries v) =
      (tildeData D).formSeries v := by
  have hφ := hasSubst_neg_X_mul (mk fun m => (D.c₀ - D.d₀) ^ m)
  rw [LandenData.formSeries, LandenData.formSeries, ← coe_substAlgHom hφ, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, coe_substAlgHom, subst_C, mul_left_comm]
  change _ * (_ * subst _ (landenFormSeries (D.a i) (D.b i) (D.c i) (D.d i))) = _
  rw [mul_subst_landenFormSeries]
  · rfl
  · rintro ⟨ha, hc⟩
    exact hD i (by rw [ha, hc]; ring)
  · rintro ⟨hb, hd⟩
    exact hD i (by rw [hb, hd]; ring)

private theorem constantCoeff_integralDivX (h : ℝ⟦X⟧) : constantCoeff (integralDivX h) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, integralDivX, coeff_mk, Nat.cast_zero, div_zero]

private theorem constantCoeff_subst_neg_X_mul (w f : ℝ⟦X⟧) :
    constantCoeff (subst (-(X * w)) f) = constantCoeff f := by
  have h := constantCoeff_subst_of_constantCoeff_zero (a := (-(X * w) : ℝ⟦X⟧)) (S := ℝ)
    (show constantCoeff (-(X * w)) = 0 by simp) f
  exact h.trans (by simp)

/-- Substituting `φ = -z ∑ eᵐ zᵐ` commutes with the formal integral against `du/u`, up to the
factor `φ / (-z) = ∑ eᵐ zᵐ`. -/
private theorem subst_integralDivX (e : ℝ) {h : ℝ⟦X⟧} (h0 : constantCoeff h = 0) :
    subst (-(X * mk fun m => e ^ m) : ℝ⟦X⟧) (integralDivX h) =
      integralDivX ((mk fun m => e ^ m) * subst (-(X * mk fun m => e ^ m) : ℝ⟦X⟧) h) := by
  set w : ℝ⟦X⟧ := mk fun m => e ^ m
  have hφ := hasSubst_neg_X_mul w
  obtain ⟨-, hI⟩ := integralDivX_spec h h0
  have h0' : constantCoeff (w * subst (-(X * w)) h) = 0 := by
    rw [map_mul, constantCoeff_subst_neg_X_mul, h0, mul_zero]
  obtain ⟨hJ0, hJ⟩ := integralDivX_spec _ h0'
  have key : X * derivative (subst (-(X * w)) (integralDivX h)) = w * subst (-(X * w)) h := by
    have := congrArg (subst (-(X * w))) hI
    rw [subst_mul hφ, subst_X hφ] at this
    rw [derivative_subst hφ, derivative_neg_X_mul_geom, ← this]
    ring
  apply derivative.ext
  · apply X_mul_cancel
    rw [key, hJ]
  · rw [hJ0, constantCoeff_subst_neg_X_mul, constantCoeff_integralDivX]

private theorem constantCoeff_polylogRev (D : LandenData) (β γ : Fin D.s → ℝ) (l : List ℕ) :
    constantCoeff (D.polylogRev β γ l) = 0 := by
  induction l using LandenData.polylogRev.induct <;>
    simp [LandenData.polylogRev, constantCoeff_integralDivX]

/-- The generalized Landen connection formula along the recursion of `LandenData.polylogRev`,
for every list, with the transformed data written as `tildeData D`. -/
private theorem subst_polylogRev_tildeData (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (β γ : Fin D.s → ℝ) (l : List ℕ) :
    subst (-(X * mk fun m => (D.c₀ - D.d₀) ^ m) : ℝ⟦X⟧) (D.polylogRev β γ l) =
      (tildeData D).polylogRev β γ l := by
  have hφ := hasSubst_neg_X_mul (mk fun m => (D.c₀ - D.d₀) ^ m)
  induction l using LandenData.polylogRev.induct with
  | case1 =>
    rw [LandenData.polylogRev, LandenData.polylogRev, ← coe_substAlgHom hφ, map_zero]
  | case2 tail =>
    rw [LandenData.polylogRev, LandenData.polylogRev, ← coe_substAlgHom hφ, map_zero]
  | case3 =>
    rw [LandenData.polylogRev, LandenData.polylogRev, subst_integralDivX,
      mul_subst_landenFormSeries]
    · congr 2 <;> ring
    · simp
    · simp
    · rw [landenFormSeries, map_sub, ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_zero_eq_constantCoeff_apply]
      simp [linearFractionalPoleSeries]
  | case4 r rs ih =>
    rw [LandenData.polylogRev, LandenData.polylogRev, subst_integralDivX, subst_mul hφ, ih,
      ← mul_assoc, mul_subst_formSeries D hD]
    rw [map_mul, constantCoeff_polylogRev, mul_zero]
  | case5 n rs ih =>
    rw [LandenData.polylogRev, LandenData.polylogRev, subst_integralDivX, subst_mul hφ, ih,
      ← mul_assoc, mul_subst_formSeries D hD]
    rw [map_mul, constantCoeff_polylogRev, mul_zero]

/-- The generalized Landen connection formula for every list: substituting
`z / ((c₀ - d₀) z - 1)` into the reversed recursion of `g` gives that of `g̃`. -/
private theorem subst_polylogRev (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (β γ : Fin D.s → ℝ) (l : List ℕ) :
    subst (-(X * mk fun m => (D.c₀ - D.d₀) ^ m) : ℝ⟦X⟧) (D.polylogRev β γ l) =
      D.tilde.polylogRev β γ l :=
  subst_polylogRev_tildeData D hD β γ l

private theorem constantCoeff_landenExpVariable (D : LandenData) :
    constantCoeff (landenExpVariable D) = 0 := by
  simp [landenExpVariable]

private theorem rescale_C_eq (a r : ℝ) : rescale a (C r : ℝ⟦X⟧) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

private theorem constantCoeff_rescale_eq (a : ℝ) (f : ℝ⟦X⟧) :
    constantCoeff (rescale a f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

/-- Substituting the variable `z(t) = (eᵗ - 1)/(c₀ eᵗ + d₀)` into `z / ((c₀ - d₀) z - 1)` gives
`z(-t)`. -/
private theorem subst_landenExpVariable (D : LandenData) :
    subst (landenExpVariable D) (-(X * mk fun m => (D.c₀ - D.d₀) ^ m) : ℝ⟦X⟧) =
      rescale (-1) (landenExpVariable D) := by
  set e := D.c₀ - D.d₀ with he
  set z := landenExpVariable D with hz_def
  have hz0 : constantCoeff z = 0 := constantCoeff_landenExpVariable D
  have hz : HasSubst z := HasSubst.of_constantCoeff_zero' hz0
  by_cases h : D.c₀ + D.d₀ = 0
  · have hz0 : z = 0 := by
      rw [hz_def, landenExpVariable, PowerSeries.inv_eq_zero.mpr (by simpa using h), mul_zero]
    rw [hz0, map_zero]
    exact subst_zero_of_constantCoeff_zero (by simp)
  · set W := subst z (mk fun m => e ^ m : ℝ⟦X⟧)
    have hW : (1 - C e * z) * W = 1 := by
      have := congrArg (subst z) (one_sub_C_mul_X_mul_geom e)
      simp only [subst_mul hz, subst_sub hz, subst_C, subst_X hz] at this
      rw [← coe_substAlgHom hz, map_one, coe_substAlgHom] at this
      exact this
    have hQ := landenExpVariable_spec D h
    set Q := C D.c₀ * exp ℝ + C D.d₀
    set E' := rescale (-1 : ℝ) (exp ℝ)
    have hE : exp ℝ * E' = 1 := exp_mul_exp_neg_eq_one
    have hE0 : constantCoeff E' = 1 := by simp [E', constantCoeff_rescale_eq]
    have hQ' : (C D.c₀ * E' + C D.d₀) * rescale (-1) z = E' - 1 := by
      simpa [Q, E', rescale_C_eq] using congrArg (rescale (-1 : ℝ)) hQ
    rw [← coe_substAlgHom hz, map_neg, map_mul, coe_substAlgHom, subst_X hz]
    have hQ0 : Q ≠ 0 := fun H => h (by simpa [Q] using congrArg constantCoeff H)
    have hQ'0 : C D.c₀ * E' + C D.d₀ ≠ 0 := fun H =>
      h (by simpa [hE0] using congrArg constantCoeff H)
    have hz10 : 1 - C e * z ≠ 0 := fun H => by
      simpa [hz0] using congrArg constantCoeff H
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hQ'0 hz10) hQ0)
    rw [he, map_sub] at hW ⊢
    linear_combination (-(C D.c₀ * E' + C D.d₀)) * hQ -
      (C D.c₀ * E' + C D.d₀) * Q * z * hW + (C D.c₀ - C D.d₀) * (E' - 1) * hQ -
      (1 - (C D.c₀ - C D.d₀) * z) * Q * hQ' - (C D.c₀ + C D.d₀) * hE

private theorem subst_rescale_eq (r : ℝ) {z : ℝ⟦X⟧} (hz : HasSubst z) (f : ℝ⟦X⟧) :
    subst (rescale r z) f = rescale r (subst z f) := by
  rw [rescale_eq_subst, rescale_eq_subst, subst_comp_subst_apply hz (HasSubst.smul_X' r)]

private theorem coeff_derivative_rescale_neg_one (F : ℝ⟦X⟧) (n : ℕ) :
    coeff n (derivative (rescale (-1) F)) = (-1) ^ (n + 1) * coeff n (derivative F) := by
  rw [coeff_derivative, coeff_derivative, coeff_rescale]
  ring

end generalizedPolyBernoulliC_landen

/-- **Landen formula for generalized poly-Bernoulli numbers $C_n$.** Let
$g = (g_0, g_1, \dots, g_s)$ be Landen data whose matrices $g_1, \dots, g_s$ are invertible, where
$(c_0, d_0)$ is the bottom row of $g_0$. Let $\tilde g$ be the transformed data: $\tilde g_0$ has
rows $(1, -1)$ and $(-d_0, -c_0)$, and $\tilde g_i = h g_i$ for $1 \le i \le s$, where $h$ is the
matrix with rows $(1, 0)$ and $(c_0 - d_0, -1)$. Let $\beta, \gamma \in \mathbb{R}^s$, let $k$ be a
composition of a natural number $m$ (the empty index when $m = 0$), and write $k\uparrow$ for $k$
with its last entry increased by $1$ ($k\uparrow$ is empty when $k$ is). Let
$z(t) \in \mathbb{R}[[t]]$, the variable of $g$, be the power series of
$(e^t - 1)/(c_0 e^t + d_0)$ (the zero series when $c_0 + d_0 = 0$). Then for every $n \ge 0$,
$$C_n^{(k, g, (\beta, \gamma))} =
(-1)^{n+1} \, n! \, [t^n] \, \frac{d}{dt}
\mathrm{Li}_{k\uparrow}(\tilde g; (\beta, \gamma); z(t)),$$
where $C_n$ is the generalized poly-Bernoulli number of the first kind, $\mathrm{Li}$ is Kamano's
generalized multiple polylogarithm and $[t^n] F$ is the coefficient of $t^n$ in $F$. Here
$\tilde g$ is evaluated at the variable $z(t)$ of $g$, not at its own variable.

This is Theorem 5 in the reading its proof establishes: the proof differentiates
$\mathrm{Li}_{k\uparrow}(g; z(t)) = \mathrm{Li}_{k\uparrow}(\tilde g; z(-t))$. The paper's sign
$(-1)^{n-1}$ equals $(-1)^{n+1}$ for all $n \ge 0$.

As printed, with $C_n^{(k, \tilde g, (\beta, \gamma))}$ formed from the variable
$(e^t - 1)/(-d_0 e^t - c_0) = z(-t)$ of $\tilde g$, the theorem is false: then
$C_n^{(k, \tilde g, (\beta, \gamma))} = C_n^{(k, g, (\beta, \gamma))}$ for all $n$. For instance,
$s = 1$, $g_0$ with rows $(1, -1)$ and $(1, 0)$, $g_1$ the identity matrix, $\beta = \gamma = (1)$,
$k = (1)$ and $n = 0$ give
$C_0^{(k, g, (\beta, \gamma))} = C_0^{(k, \tilde g, (\beta, \gamma))} = 1$, while the printed
identity asks for $1 = -1$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 5. -/
public theorem generalizedPolyBernoulliC_landen (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (β γ : Fin D.s → ℝ) {m : ℕ}
    (k : Composition m) (n : ℕ) :
    generalizedPolyBernoulliC D β γ k.blocks n =
      (-1 : ℝ) ^ (n + 1) * (n.factorial * coeff n (derivative (subst (landenExpVariable D)
        (generalizedMultiplePolylog D.tilde β γ (k.blocks.modifyLast (· + 1)))))) := by
  have hz : HasSubst (landenExpVariable D) := HasSubst.of_constantCoeff_zero'
    (generalizedPolyBernoulliC_landen.constantCoeff_landenExpVariable D)
  have hφ := generalizedPolyBernoulliC_landen.hasSubst_neg_X_mul
    (mk fun j => (D.c₀ - D.d₀) ^ j)
  -- The generalized Landen connection formula: `Li(g̃; z) = Li(g; φ(z))`.
  have key : generalizedMultiplePolylog D.tilde β γ (k.blocks.modifyLast (· + 1)) =
      subst (-(X * mk fun j => (D.c₀ - D.d₀) ^ j) : ℝ⟦X⟧)
        (generalizedMultiplePolylog D β γ (k.blocks.modifyLast (· + 1))) :=
    (generalizedPolyBernoulliC_landen.subst_polylogRev D hD β γ _).symm
  -- With `φ(z(t)) = z(-t)`, the right-hand side is about `Li(g; z(-t))`.
  rw [key, subst_comp_subst_apply hφ hz,
    generalizedPolyBernoulliC_landen.subst_landenExpVariable,
    generalizedPolyBernoulliC_landen.subst_rescale_eq _ hz,
    generalizedPolyBernoulliC_landen.coeff_derivative_rescale_neg_one, generalizedPolyBernoulliC]
  have h1 : ((-1 : ℝ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (-(n.factorial * coeff n (derivative (subst (landenExpVariable D)
    (generalizedMultiplePolylog D β γ (k.blocks.modifyLast (· + 1))))))) * h1

/-! ### Landen formula in the classical case -/

namespace generalizedMultiplePolylog_landen_connection_classical

open generalizedPolyBernoulliC_landen (tildeData)

private noncomputable abbrev classicalData : LandenData :=
  ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩

private theorem linearFractionalPoleSeries_zero_right (a : ℝ) :
    linearFractionalPoleSeries a 0 = 0 := by
  by_cases ha : a = 0
  · simp [linearFractionalPoleSeries, ha]
  · ext n
    cases n <;> simp [linearFractionalPoleSeries, ha]

private theorem pole_neg_one_neg_one :
    linearFractionalPoleSeries (-1) (-1) = linearFractionalPoleSeries 1 1 := by
  norm_num [linearFractionalPoleSeries]

-- Writing `P = z / (1 - z)`, the forms `1, P` become `1 + P, -P`.
private theorem formSeries_tilde (w₁ w₂ : ℝ) :
    (tildeData classicalData).formSeries ![w₁, w₂] = classicalData.formSeries ![w₁, w₁ - w₂] := by
  norm_num [LandenData.formSeries, Fin.sum_univ_two, tildeData, classicalData]
  have hp : linearFractionalPoleSeries 0 1 = -1 := by
    norm_num [linearFractionalPoleSeries]
  have hm : linearFractionalPoleSeries 0 (-1) = -1 := by
    norm_num [linearFractionalPoleSeries]
  simp [landenFormSeries, linearFractionalPoleSeries_zero_right, pole_neg_one_neg_one, hp, hm,
    map_sub]
  ring

private theorem integralDivX_neg (f : ℝ⟦X⟧) : integralDivX (-f) = -integralDivX f := by
  ext n
  simp [integralDivX, neg_div]

private theorem polylogRev_tilde (β₁ β₂ γ₁ γ₂ : ℝ) (l : List ℕ) :
    (tildeData classicalData).polylogRev ![β₁, β₂] ![γ₁, γ₂] l =
      -classicalData.polylogRev ![β₁, β₁ - β₂] ![γ₁, γ₁ - γ₂] l := by
  induction l using LandenData.polylogRev.induct with
  | case1 => simp only [LandenData.polylogRev.eq_1, neg_zero]
  | case2 tail => simp only [LandenData.polylogRev.eq_2, neg_zero]
  | case3 =>
    rw [LandenData.polylogRev.eq_3, LandenData.polylogRev.eq_3, ← integralDivX_neg]
    norm_num [classicalData, tildeData, landenFormSeries,
      linearFractionalPoleSeries_zero_right, pole_neg_one_neg_one]
  | case4 r rs ih =>
    rw [LandenData.polylogRev.eq_4, LandenData.polylogRev.eq_4, formSeries_tilde, ih, mul_neg,
      integralDivX_neg]
  | case5 n rs ih =>
    rw [LandenData.polylogRev.eq_5, LandenData.polylogRev.eq_5, formSeries_tilde, ih, mul_neg,
      integralDivX_neg]

end generalizedMultiplePolylog_landen_connection_classical

open generalizedMultiplePolylog_landen_connection_classical in
/-- **Landen formula in the classical case.** Let $g = (g_0, g_1, g_2)$ be the Landen data in
which $g_0 = g_2$ has rows $(1, -1)$ and $(1, 0)$ and $g_1$ is the identity matrix, so that
$G_{g_1}(t) = 1/t$ and $G_{g_2}(t) = 1/(1 - t)$. For all real numbers $\beta_1$, $\beta_2$,
$\gamma_1$, $\gamma_2$ and every finite (possibly empty) sequence $\mathbf{k}$ of positive
integers,
$\mathrm{Li}_{\mathbf{k}}(g; ((\beta_1, \beta_2), (\gamma_1, \gamma_2)); \frac{z}{z - 1}) =
-\mathrm{Li}_{\mathbf{k}}(g; ((\beta_1, \beta_1 - \beta_2), (\gamma_1, \gamma_1 - \gamma_2)); z)$
in $\mathbb{R}[[z]]$, where $\frac{z}{z - 1} = -\sum_{n \ge 1} z^n$ is substituted for $z$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 3,
Identity (10). -/
public theorem generalizedMultiplePolylog_landen_connection_classical
    (β₁ β₂ γ₁ γ₂ : ℝ) {n : ℕ} (k : Composition n) :
    subst (-(X * mk fun _ => (1 : ℝ)))
        (generalizedMultiplePolylog ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩
          ![β₁, β₂] ![γ₁, γ₂] k.blocks) =
      -generalizedMultiplePolylog ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩
          ![β₁, β₁ - β₂] ![γ₁, γ₁ - γ₂] k.blocks := by
  have hD : ∀ i,
      classicalData.a i * classicalData.d i - classicalData.b i * classicalData.c i ≠ 0 := by
    intro i
    fin_cases i <;> norm_num [classicalData]
  unfold generalizedMultiplePolylog
  calc
    _ = classicalData.tilde.polylogRev ![β₁, β₂] ![γ₁, γ₂] k.blocks.reverse := by
      simpa only [classicalData, sub_zero, one_pow] using
        generalizedPolyBernoulliC_landen.subst_polylogRev classicalData hD ![β₁, β₂] ![γ₁, γ₂]
          k.blocks.reverse
    _ = _ := polylogRev_tilde β₁ β₂ γ₁ γ₂ k.blocks.reverse

end

end MetaMathlibExt
