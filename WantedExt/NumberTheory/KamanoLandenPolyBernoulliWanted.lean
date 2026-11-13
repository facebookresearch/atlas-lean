/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Basic.Real.Basic

/-!
# Kamano, generalized Landen connection formula and poly-Bernoulli numbers — wishlist

Statement-only records for Ken Kamano's INTEGERS 24 (2024) paper. Everything is
formal: power series live in `ℝ⟦X⟧`, and the iterated integrals
`∫₀^z G_{g_i}(u) f(u) du` of the paper are realised coefficientwise.

* For `g = (a b; c d) ∈ GL₂(ℝ)` the paper's `G_g(t) = c/(a - c t) - d/(b - d t)`
  has at most a simple pole at `0` (when `a = 0` or `b = 0`), so we store the
  power series `u · G_g(u)` (`landenFormSeries`).
* For `h` with zero constant term, `∫₀^z h(u) du / u` has coefficients
  `[z^n] = [u^n] h / n` (`integralDivX`); every integration step of the paper is
  `integralDivX (u G(u) · f(u))` because each polylogarithm has no constant term.
* Indices `k ∈ ℤ_{>0}^r` are the blocks of a `Composition` (so `|k|` is the
  composition's total and `d(k)` its length). The arrow notation of the paper is
  `k↑ = k.modifyLast (· + 1)` and `k→ = k ++ [1]`.
* Substituting a series into a series is `PowerSeries.subst`; the variable
  `z(t) = (e^t - 1)/(c₀ e^t + d₀)` is `landenExpVariable`.

Theorem 5 is false as printed with the paper's own definitions (see the
docstring of `generalizedPolyBernoulliC_landen`); it is stated in the reading
its proof establishes.
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

/-- **Coefficient recursion for multiple polylogarithms.** For a finite list $\ell$ of natural
numbers and $m \in \mathbb{N}$, the real number $c_\ell(m)$ is defined by recursion on $\ell$:
for the empty list, $c_{()}(m)$ is $1$ if $m = 0$ and $0$ otherwise; for the list $(a, \ell')$
with first entry $a$ followed by the list $\ell'$,
$c_{(a, \ell')}(m) = \big(\sum_{m' < m} c_{\ell'}(m')\big) / m^a$.

The multiple polylogarithm $\mathrm{Li}_{(k_1, \dots, k_r)}(z)$ is defined as the power series
whose coefficient of $z^m$ is $c_{(k_r, \dots, k_1)}(m)$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1,
definition of `Li_k(z)`. -/
public noncomputable def multiplePolylogCoeffRev : List ℕ → ℕ → ℝ
  | [], m => if m = 0 then 1 else 0
  | a :: rs, m => (∑ m' ∈ Finset.range m, multiplePolylogCoeffRev rs m') / (m : ℝ) ^ a

/-- **Multiple polylogarithm.** For a finite sequence $k = (k_1, \dots, k_r)$ of natural numbers
with $r \ge 1$, the multiple polylogarithm is the formal power series
$$\mathrm{Li}_k(z) = \sum_{0 < m_1 < \cdots < m_r} \frac{z^{m_r}}{m_1^{k_1} \cdots m_r^{k_r}}$$
in $\mathbb{R}[[z]]$; for the empty sequence it is the constant series $1$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public noncomputable def multiplePolylog (k : List ℕ) : ℝ⟦X⟧ :=
  mk (multiplePolylogCoeffRev k.reverse)

/-- **Depth-one multiple polylogarithm.** For every natural number $a$ and every integer
$m \ge 1$, the coefficient of $z^m$ in the multiple polylogarithm $\mathrm{Li}_{(a)}(z)$ is
$1/m^a$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public theorem coeff_multiplePolylog_singleton (a : ℕ) {m : ℕ} (hm : 0 < m) :
    coeff m (multiplePolylog [a]) = 1 / (m : ℝ) ^ a := by
  simp [multiplePolylog, multiplePolylogCoeffRev, Finset.sum_ite_eq', hm]

/-- **Coefficient recursion for the non-strict multiple polylogarithm.** For a finite list $\ell$
of natural numbers and $m \in \mathbb{N}$, the real number $c_\ell(m)$ is defined by recursion on
$\ell$: for the empty list, $c_\ell(m) = 1$ if $m = 0$ and $c_\ell(m) = 0$ otherwise; for a list
$\ell = (a, \ell')$ with first entry $a$ followed by the list $\ell'$,
$$c_{(a, \ell')}(m) = \frac{1}{m^a} \sum_{m' = 0}^{m} c_{\ell'}(m'),$$
where $0^0 = 1$ and $1/0 = 0$.

Applied to the reversed list $(k_r, \dots, k_1)$ of positive integers $k_1, \dots, k_r$ with
$r \ge 1$, it gives the coefficient of $z^m$ in
$\sum_{0 < m_1 \le \cdots \le m_r} z^{m_r} / (m_1^{k_1} \cdots m_r^{k_r})$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1,
definition of `Li⋆_k(z)`. -/
public noncomputable def multiplePolylogStarCoeffRev : List ℕ → ℕ → ℝ
  | [], m => if m = 0 then 1 else 0
  | a :: rs, m =>
      (∑ m' ∈ Finset.range (m + 1), multiplePolylogStarCoeffRev rs m') / (m : ℝ) ^ a

/-- **Non-strict multiple polylogarithm.** For an index $k = (k_1, \dots, k_r)$ of positive
integers with $r \ge 1$, the non-strict multiple polylogarithm is the formal power series
$$\mathrm{Li}^\star_k(z) = \sum_{0<m_1\le\cdots\le m_r} \frac{z^{m_r}}{m_1^{k_1} \cdots m_r^{k_r}}$$
in $\mathbb{R}[[z]]$.

The definition accepts every finite list $k$ of natural numbers: for $r \ge 1$ the coefficient
of $z^m$ is the sum of $1/(m_1^{k_1} \cdots m_r^{k_r})$ over $0 \le m_1 \le \cdots \le m_r = m$,
where $0^0 = 1$ and $1/0 = 0$ (so for an index the terms with some $m_i = 0$ vanish), and the
empty list gives the constant series $1$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public noncomputable def multiplePolylogStar (k : List ℕ) : ℝ⟦X⟧ :=
  mk (multiplePolylogStarCoeffRev k.reverse)

/-- **Depth-one non-strict multiple polylogarithm.** For all natural numbers $a$ and $m$, the
coefficient of $z^m$ in the non-strict multiple polylogarithm $\mathrm{Li}^{\star}_{(a)}(z)$ is
$1/m^a$, with the conventions $0^0 = 1$ and $1/0 = 0$. In particular
$\mathrm{Li}^{\star}_{(a)}(z) = \sum_{m \ge 1} z^m / m^a$ for $a \ge 1$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 1. -/
public theorem coeff_multiplePolylogStar_singleton (a m : ℕ) :
    coeff m (multiplePolylogStar [a]) = 1 / (m : ℝ) ^ a := by
  simp [multiplePolylogStar, multiplePolylogStarCoeffRev, Finset.sum_ite_eq']

/-- **Hoffman dual on reversed lists.** The auxiliary map $R$ on finite lists
$l = (l_1, \dots, l_m)$ of natural numbers is defined recursively by: $R(()) = ()$; $R(l) = ()$
if $l_1 = 0$; $R((1)) = (1)$; if $l_1 = 1$ and $m \ge 2$, then $R(l)$ is $R((l_2, \dots, l_m))$
with its first entry increased by $1$ (unchanged if that list is empty); and if $l_1 \ge 2$, then
$R(l) = (1, r_1, \dots, r_p)$ where $(r_1, \dots, r_p) = R((l_1 - 1, l_2, \dots, l_m))$.

Reading an index from its last entry, these are the rules $(1)^\vee = (1)$,
$(k\rightarrow)^\vee = (k^\vee)\uparrow$ and $(k\uparrow)^\vee = (k^\vee)\rightarrow$ of Hoffman's
dual index, where $k\uparrow$ increases the last entry of $k$ by $1$ and $k\rightarrow$ appends an
entry $1$: the Hoffman dual of an index $k$ is the reverse of $R$ applied to the reverse of $k$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2,
definition of Hoffman's dual index. -/
public def hoffmanDualRev : List ℕ → List ℕ
  | [] => []
  | 0 :: _ => []
  | [1] => [1]
  | 1 :: r :: rs => (hoffmanDualRev (r :: rs)).modifyHead (· + 1)
  | (n + 2) :: rs => 1 :: hoffmanDualRev ((n + 1) :: rs)
termination_by l => l.sum

/-- **Hoffman dual index.** For an index $k = (k_1, \dots, k_r)$ of positive integers write
$k\uparrow = (k_1, \dots, k_r + 1)$ and $k\rightarrow = (k_1, \dots, k_r, 1)$. The Hoffman dual
index $k^\vee$ is defined recursively by $(1)^\vee = (1)$, $(k\uparrow)^\vee = (k^\vee)\rightarrow$
and $(k\rightarrow)^\vee = (k^\vee)\uparrow$. On other finite lists of natural numbers, the empty
list is sent to the empty list and a list with an entry $0$ is sent to an unspecified junk value.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public def hoffmanDual (k : List ℕ) : List ℕ :=
  (hoffmanDualRev k.reverse).reverse

/-- **Small values of the Hoffman dual.** The Hoffman dual index satisfies $(1)^\vee = (1)$,
$(3)^\vee = (1, 1, 1)$ and $(1, 2)^\vee = (2, 1)$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2. -/
public theorem hoffmanDual_small_values :
    hoffmanDual [1] = [1] ∧ hoffmanDual [3] = [1, 1, 1] ∧ hoffmanDual [1, 2] = [2, 1] := by
  simp [hoffmanDual, hoffmanDualRev]

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

/-- **Generalized poly-Bernoulli numbers of the second kind.** Let $g = (g_0, g_1, \dots, g_s)$ be
Landen data, where $(c_0, d_0)$ is the bottom row of the matrix $g_0$, let
$\beta, \gamma \in \mathbb{R}^s$, and let $k = (k_1, \dots, k_r)$ be a list of natural numbers;
write $k\rightarrow = (k_1, \dots, k_r, 1)$, with $k\rightarrow = (1)$ when $k$ is empty. Let
$z(t) \in \mathbb{R}[[t]]$ be the power series of $(e^t - 1)/(c_0 e^t + d_0)$ (the zero series
when $c_0 + d_0 = 0$). The numbers $B_n^{(k, g, (\beta, \gamma))} \in \mathbb{R}$, $n \ge 0$, are
defined by
$$\frac{d}{dt} \mathrm{Li}_{k\rightarrow}(g; (\beta, \gamma); z(t)) =
\sum_{n \ge 0} B_n^{(k, g, (\beta, \gamma))} \frac{t^n}{n!},$$
where $\mathrm{Li}_{k\rightarrow}(g; (\beta, \gamma); z)$ is Kamano's generalized multiple
polylogarithm, into which the series $z(t)$ is substituted.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 4. -/
public noncomputable def generalizedPolyBernoulliB (D : LandenData) (β γ : Fin D.s → ℝ)
    (k : List ℕ) (n : ℕ) : ℝ :=
  n.factorial * coeff n (derivative (subst (landenExpVariable D)
    (generalizedMultiplePolylog D β γ (k ++ [1]))))

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

/-- **Landen connection formula** (Okuda–Ueno). Let $n \ge 0$ and let $k = (k_1, \dots, k_r)$ be
an index of weight $n$, that is, a finite sequence of positive integers with sum $n$. Then the
multiple polylogarithms satisfy the identity
$$\mathrm{Li}_k\left(\frac{z}{z - 1}\right) = (-1)^r \sum_{k'} \mathrm{Li}_{k'}(z)$$
in $\mathbb{R}[[z]]$, where $\mathrm{Li}_k(z) \in \mathbb{R}[[z]]$ is the multiple polylogarithm,
$\frac{z}{z - 1}$ stands for the series $-\sum_{m \ge 1} z^m$ substituted into $\mathrm{Li}_k$, and
the sum runs over all indices $k'$ of weight $n$ from which $k$ is obtained by adding up blocks of
consecutive entries; equivalently, every partial sum $k_1 + \cdots + k_j$ of $k$ is also a partial
sum of $k'$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 1
(quoting Okuda and Ueno, Prop. 9). -/
public theorem_wanted multiplePolylog_landen_connection {n : ℕ} (k : Composition n) :
    subst (-(X * mk fun _ => (1 : ℝ))) (multiplePolylog k.blocks) =
      (-1 : ℝ) ^ k.length •
        ∑ k' : Composition n with k.boundaries ⊆ k'.boundaries, multiplePolylog k'.blocks

/-- **Sum formula.** Let $g = (g_0, g_1, \dots, g_s)$ be Landen data, let
$\beta, \gamma, \delta \in \mathbb{R}^s$, let $\mu$ be a real number and let $k \ge 1$ be an
integer. Then
$\sum_{\mathbf{k}} \mu^{d(\mathbf{k}) - 1} \mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); z) =
\mathrm{Li}_{(k)}(g; (\beta + \mu \gamma, \delta); z)$, where the sum runs over all compositions
$\mathbf{k} = (k_1, \dots, k_r)$ of $k$ (sequences of positive integers with
$k_1 + \dots + k_r = k$) and $d(\mathbf{k}) = r$ is the depth of $\mathbf{k}$.

The paper takes $\mu$ an indeterminate; both sides are polynomials in $\mu$, so this
is equivalent.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 1,
Identity (7). -/
public theorem_wanted generalizedMultiplePolylog_sum_formula (D : LandenData)
    (β γ δ : Fin D.s → ℝ) (μ : ℝ) (k : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) • generalizedMultiplePolylog D β γ c.blocks =
      generalizedMultiplePolylog D (β + μ • γ) δ [k]

/-- **Generalized Landen connection formula.** Let $g = (g_0, g_1, \dots, g_s)$ be Landen data,
where $g_0$ has rows $(1, -1)$ and $(c_0, d_0)$ and each $g_i$ ($1 \le i \le s$) has rows
$(a_i, b_i)$ and $(c_i, d_i)$ with $a_i d_i - b_i c_i \ne 0$. Let $\tilde g$ be the transformed
data: $\tilde g_0$ has rows $(1, -1)$ and $(-d_0, -c_0)$, and $\tilde g_i = M g_i$, where $M$ is
the matrix with rows $(1, 0)$ and $(c_0 - d_0, -1)$. For all $\beta, \gamma \in \mathbb{R}^s$ and
every finite (possibly empty) sequence $\mathbf{k}$ of positive integers,
$\mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); \frac{z}{(c_0 - d_0) z - 1}) =
\mathrm{Li}_{\mathbf{k}}(\tilde g; (\beta, \gamma); z)$ in $\mathbb{R}[[z]]$, where
$\frac{z}{(c_0 - d_0) z - 1} = -\sum_{n \ge 0} (c_0 - d_0)^n z^{n+1}$ is substituted for $z$.

The paper also assumes $g_0 \in \mathrm{GL}_2(\mathbb{R})$, that is $c_0 + d_0 \ne 0$; this is not
needed. The invertibility of the $g_i$ is needed: with $a_i = c_i = 0$ the identity fails.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 2,
Identity (8). -/
public theorem_wanted generalizedMultiplePolylog_landen_connection (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (β γ : Fin D.s → ℝ) {n : ℕ}
    (k : Composition n) :
    subst (-(X * mk fun m => (D.c₀ - D.d₀) ^ m)) (generalizedMultiplePolylog D β γ k.blocks) =
      generalizedMultiplePolylog D.tilde β γ k.blocks

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
public theorem_wanted generalizedMultiplePolylog_landen_connection_classical
    (β₁ β₂ γ₁ γ₂ : ℝ) {n : ℕ} (k : Composition n) :
    subst (-(X * mk fun _ => (1 : ℝ)))
        (generalizedMultiplePolylog ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩
          ![β₁, β₂] ![γ₁, γ₂] k.blocks) =
      -generalizedMultiplePolylog ⟨2, 1, 0, ![1, 1], ![0, -1], ![0, 1], ![1, 0]⟩
          ![β₁, β₁ - β₂] ![γ₁, γ₁ - γ₂] k.blocks

/-- **Duality of multi-poly-Bernoulli-star numbers.** This duality is due to Imatomi. Let $k$
be an index (a composition of a natural number $m$), let $k^\vee$ be its Hoffman dual, and let
$\mathrm{Li}^\star_k$ be the non-strict multiple polylogarithm. Let $F, G \in \mathbb{R}[[t]]$
satisfy $(e^t - 1) F = \mathrm{Li}^\star_k(1 - e^{-t})$ and
$(1 - e^{-t}) G = \mathrm{Li}^\star_{k^\vee}(1 - e^{-t})$, and write
$F = \sum_{n \ge 0} C_{n,\star}^{(k)} t^n / n!$ and
$G = \sum_{n \ge 0} B_{n,\star}^{(k^\vee)} t^n / n!$. Then
$C_{n,\star}^{(k)} = (-1)^n B_{n,\star}^{(k^\vee)}$ for every $n \ge 0$.

Since $e^t - 1$ and $1 - e^{-t}$ are non-zero-divisors in $\mathbb{R}[[t]]$, these equations
determine $F$ and $G$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 4
(quoting Imatomi, Theorem 3.2), with generating functions (13) and (14). -/
public theorem_wanted multiPolyBernoulliStar_duality {m : ℕ} (k : Composition m)
    (F G : ℝ⟦X⟧)
    (hF : (exp ℝ - 1) * F =
      subst (1 - rescale (-1 : ℝ) (exp ℝ)) (multiplePolylogStar k.blocks))
    (hG : (1 - rescale (-1 : ℝ) (exp ℝ)) * G =
      subst (1 - rescale (-1 : ℝ) (exp ℝ)) (multiplePolylogStar (hoffmanDual k.blocks)))
    (n : ℕ) :
    n.factorial * coeff n F = (-1 : ℝ) ^ n * (n.factorial * coeff n G)

/-- **Sum formula for generalized poly-Bernoulli numbers $C_n$.** Let $g = (g_0, g_1, \dots, g_s)$
be Landen data, let $\beta, \gamma \in \mathbb{R}^s$, let $\mu$ be a real number, and let $k \ge 1$
and $n \ge 0$ be integers. Write $B_n$ and $C_n$ for Kamano's generalized poly-Bernoulli numbers of
the second and first kind, $d(\mathbf{k})$ for the number of entries of an index $\mathbf{k}$, and
$\{1\}^k = (1, \dots, 1)$ for the index of $k$ ones. Then
$$\sum_{|\mathbf{k}| = k} \mu^{d(\mathbf{k}) - 1} C_n^{(\mathbf{k}, g, (\beta, \gamma))} =
B_n^{((k), g, (\beta + \mu\gamma, \beta))} =
C_n^{(\{1\}^k, g, (\beta, \beta + \mu\gamma))},$$
where the sum runs over all compositions $\mathbf{k}$ of $k$, that is, all tuples of positive
integers with sum $k$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 2,
Identity (16). -/
public theorem_wanted generalizedPolyBernoulliC_sum_formula (D : LandenData)
    (β γ : Fin D.s → ℝ) (μ : ℝ) (k n : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) * generalizedPolyBernoulliC D β γ c.blocks n =
        generalizedPolyBernoulliB D (β + μ • γ) β [k] n ∧
      generalizedPolyBernoulliB D (β + μ • γ) β [k] n =
        generalizedPolyBernoulliC D β (β + μ • γ) (List.replicate k 1) n

/-- **Sum formula for generalized poly-Bernoulli numbers $B_n$.** Let $g = (g_0, g_1, \dots, g_s)$
be Landen data, let $\beta, \gamma \in \mathbb{R}^s$, let $\mu$ be a real number, and let $k \ge 1$
and $n \ge 0$ be integers. Write $B_n$ and $C_n$ for Kamano's generalized poly-Bernoulli numbers of
the second and first kind, $d(\mathbf{k})$ for the number of entries of an index $\mathbf{k}$, and
$\{1\}^k = (1, \dots, 1)$ for the index of $k$ ones. Then
$$\sum_{|\mathbf{k}| = k} \mu^{d(\mathbf{k}) - 1} B_n^{(\mathbf{k}, g, (\beta, \gamma))} =
B_n^{((k), g, (\beta + \mu\gamma, \gamma))} =
C_n^{(\{1\}^k, g, (\gamma, \beta + \mu\gamma))},$$
where the sum runs over all compositions $\mathbf{k}$ of $k$, that is, all tuples of positive
integers with sum $k$.

Source: Ken Kamano, *A Generalization of the Landen Connection Formula and
Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Proposition 2,
Identity (17). -/
public theorem_wanted generalizedPolyBernoulliB_sum_formula (D : LandenData)
    (β γ : Fin D.s → ℝ) (μ : ℝ) (k n : ℕ) (hk : 0 < k) :
    ∑ c : Composition k, μ ^ (c.length - 1) * generalizedPolyBernoulliB D β γ c.blocks n =
        generalizedPolyBernoulliB D (β + μ • γ) γ [k] n ∧
      generalizedPolyBernoulliB D (β + μ • γ) γ [k] n =
        generalizedPolyBernoulliC D γ (β + μ • γ) (List.replicate k 1) n

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
public theorem_wanted generalizedPolyBernoulliC_landen (D : LandenData)
    (hD : ∀ i, D.a i * D.d i - D.b i * D.c i ≠ 0) (β γ : Fin D.s → ℝ) {m : ℕ}
    (k : Composition m) (n : ℕ) :
    generalizedPolyBernoulliC D β γ k.blocks n =
      (-1 : ℝ) ^ (n + 1) * (n.factorial * coeff n (derivative (subst (landenExpVariable D)
        (generalizedMultiplePolylog D.tilde β γ (k.blocks.modifyLast (· + 1))))))

end

end MetaMathlibExt
