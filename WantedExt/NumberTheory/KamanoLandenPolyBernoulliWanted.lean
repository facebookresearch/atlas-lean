/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.KamanoLandenPolyBernoulli
public import MathlibExt.NumberTheory.KamanoLandenPolyBernoulliGeneralizedMultiplePolylogSumFormula

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

Proved in `MathlibExt.NumberTheory.KamanoLandenPolyBernoulli`, which this module
imports: the Landen formula for the generalized poly-Bernoulli numbers of the first
kind (`generalizedPolyBernoulliC_landen`). Theorem 5 is false as printed with the
paper's own definitions (see the docstring of `generalizedPolyBernoulliC_landen`); it
is stated and proved in the reading its proof establishes. The definitions it uses
(`linearFractionalPoleSeries`, `landenFormSeries`, `integralDivX`, `LandenData` with
`LandenData.tilde`, `LandenData.formSeries` and `LandenData.polylogRev`,
`generalizedMultiplePolylog`, `landenExpVariable` and `generalizedPolyBernoulliC`)
moved there with it, together with their proved lemmas, with the same names,
statements and docstrings.

Proved in
`MathlibExt.NumberTheory.KamanoLandenPolyBernoulliGeneralizedMultiplePolylogSumFormula`:
`generalizedMultiplePolylog_sum_formula`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
