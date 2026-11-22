/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Points of valuation 1 for a polynomial in two variables

Statements from Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for
a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82.

`ν_p(v) = 1` is written `p ∣ v ∧ ¬ p² ∣ v` and `ν_p(v) > 1` is written `p² ∣ v` (so `v = 0` has
valuation `> 1`). A polynomial `f ∈ ℤ[x, y]` is an `MvPolynomial (Fin 2) ℤ` evaluated at `![x, y]`,
with partial derivatives `f_x = pderiv 0 f`, `f_y = pderiv 1 f`; a point of `C_f(𝔽_p)` is a pair
`0 ≤ r, s < p` with `p ∣ f(r, s)`, and its lifts are `(r + kp, s + lp)`, `0 ≤ k, l < p`.

Section 3 onwards: the paper's random variables live on the uniform probability space
`(k, l) ∈ 𝔽_p²`, so an expectation or probability is a count over `range p ×ˢ range p` divided by
`p²`. Limits `p → ∞` run over primes, through the filter `atTop ⊓ 𝓟 {p | p.Prime}`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **At most one lift has valuation above one.** Let $p$ be a prime, $g \in \mathbb{Z}[x]$ and
$r$ an integer with $0 \le r < p$ such that $g(r)$ and $g'(r)$ are not both divisible by $p$.
Then at most one $k \in \{0, \dots, p - 1\}$ satisfies $p^2 \mid g(r + kp)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 1
(`integers-2026-A82-prop-1`). -/
public theorem_wanted card_lift_padicVal_gt_one_le_one {p : ℕ} (hp : p.Prime) (g : Polynomial ℤ)
    {r : ℕ} (hr : r < p)
    (hroot : ¬ ((p : ℤ) ∣ g.eval (r : ℤ) ∧ (p : ℤ) ∣ (Polynomial.derivative g).eval (r : ℤ))) :
    ((Finset.range p).filter fun k : ℕ => (p : ℤ) ^ 2 ∣ g.eval ((r : ℤ) + k * p)).card ≤ 1

/-- **Few residues modulo $p^2$ with valuation above one.** Let $g \in \mathbb{Z}[x]$ be a
non-zero polynomial of degree $d$ with non-zero discriminant. Then there is a natural number $P$
such that for every prime $p \ge P$, at most $d$ integers $x$ with $0 \le x < p^2$ satisfy
$p^2 \mid g(x)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Corollary 1
(`integers-2026-A82-cor-1`). -/
public theorem_wanted card_padicVal_gt_one_le_natDegree (g : Polynomial ℤ) (hg : g ≠ 0)
    (hdisc : g.discr ≠ 0) :
    ∃ P : ℕ, ∀ p : ℕ, p.Prime → P ≤ p →
      ((Finset.range (p ^ 2)).filter fun x : ℕ => (p : ℤ) ^ 2 ∣ g.eval (x : ℤ)).card ≤ g.natDegree

/-- **Lifts of a nonsingular point with valuation one.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $r, s$ be integers in
$\{0, \dots, p - 1\}$ with $p \mid f(r, s)$ such that $f_x(r, s)$ and $f_y(r, s)$ are not both
divisible by $p$. Then exactly $p(p - 1)$ of the pairs $(k, l)$ with $0 \le k, l < p$ satisfy
$p \mid f(r + kp, s + lp)$ and $p^2 \nmid f(r + kp, s + lp)$, that is,
$\nu_p(f(r + kp, s + lp)) = 1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 2
(`integers-2026-A82-prop-2`). -/
public theorem_wanted card_lift_padicVal_eq_one {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r s : ℕ} (hr : r < p) (hs : s < p)
    (hcurve : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f)
    (hgrad : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
      (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f))) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card =
      p * (p - 1)

/-- **Common lifts of two points with independent gradients.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $(r_1, s_1)$ and
$(r_2, s_2)$ be pairs of integers in $\{0, \dots, p - 1\}$ with $p \mid f(r_i, s_i)$ for
$i = 1, 2$ and
$$
p \nmid f_x(r_1, s_1) f_y(r_2, s_2) - f_y(r_1, s_1) f_x(r_2, s_2).
$$
Write $F_i(k, l) = f(r_i + kp, s_i + lp)$. Among the pairs $(k, l)$ with $0 \le k, l < p$,
exactly $(p - 1)^2$ have $p \mid F_i(k, l)$ and $p^2 \nmid F_i(k, l)$ for both $i$, exactly
$p - 1$ have $p^2 \mid F_1(k, l)$, $p \mid F_2(k, l)$ and $p^2 \nmid F_2(k, l)$, and exactly
one has $p^2 \mid F_1(k, l)$ and $p^2 \mid F_2(k, l)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 3
(`integers-2026-A82-prop-3`). -/
public theorem_wanted card_common_lift_padicVal_of_gradients_independent {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r₁ s₁ r₂ s₂ : ℕ} (hr₁ : r₁ < p) (hs₁ : s₁ < p) (hr₂ : r₂ < p)
    (hs₂ : s₂ < p) (h₁ : (p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] f)
    (h₂ : (p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] f)
    (hind : ¬ (p : ℤ) ∣
      MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f) -
        MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f)) :
    let F₁ : ℕ × ℕ → ℤ := fun kl => MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f
    let F₂ : ℕ × ℕ → ℤ := fun kl => MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f
    let one : ℤ → Prop := fun v => (p : ℤ) ∣ v ∧ ¬ (p : ℤ) ^ 2 ∣ v
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ => one (F₁ kl) ∧ one (F₂ kl)).card =
        (p - 1) ^ 2 ∧
      ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ F₁ kl ∧ one (F₂ kl)).card = p - 1 ∧
      ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ F₁ kl ∧ (p : ℤ) ^ 2 ∣ F₂ kl).card = 1

/-- **Number of points of valuation one modulo $p^2$.** Let $p$ be a prime and let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$. Suppose that for all integers
$r, s \in \{0, \dots, p - 1\}$ with $p \mid f(r, s)$, the integers $f_x(r, s)$ and $f_y(r, s)$
are not both divisible by $p$. Let $m$ be the number of pairs $(r, s)$ with $0 \le r, s < p$ and
$p \mid f(r, s)$. Then the number of pairs $(x, y)$ with $0 \le x, y < p^2$, $p \mid f(x, y)$
and $p^2 \nmid f(x, y)$ is $m p (p - 1)$.

Without the hypothesis on $f_x$ and $f_y$ the count fails: for $f = x^2 - y^2$ and $p = 3$ one
has $m = 5$, but only $24$ pairs, not $30$, have valuation $1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Corollary 2 (`integers-2026-A82-cor-2`). -/
public theorem_wanted card_padicVal_eq_one_mod_sq_eq {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ)
    (hns : ∀ r < p, ∀ s < p, (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f →
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f))) :
    ((Finset.range (p ^ 2) ×ˢ Finset.range (p ^ 2)).filter fun xy : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f).card =
      ((Finset.range p ×ˢ Finset.range p).filter fun rs : ℕ × ℕ =>
          (p : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f).card * (p * (p - 1))

/-- **Lifts of a singular point with valuation one.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $r, s$ be integers in
$\{0, \dots, p - 1\}$ such that $p$ divides $f(r, s)$, $f_x(r, s)$ and $f_y(r, s)$. Then the
number of pairs $(k, l)$ with $0 \le k, l < p$, $p \mid f(r + kp, s + lp)$ and
$p^2 \nmid f(r + kp, s + lp)$ is $0$ if $p^2 \mid f(r, s)$, and $p^2$ otherwise.

The cited statement prints the two cases swapped. By the paper's eq. (7) every lift
$f(r + kp, s + lp)$ is congruent to $f(r, s)$ modulo $p^2$. The printed version fails for
$f = x^2 + y^2 + 3$, $p = 3$, $(r, s) = (0, 0)$: $f(0, 0) = 3$ is not divisible by $9$, and all
$9$ lifts have valuation $1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Corollary 3 (`integers-2026-A82-cor-3`). -/
public theorem_wanted card_lift_padicVal_eq_one_of_singular {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r s : ℕ} (hr : r < p) (hs : s < p)
    (hcurve : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f)
    (hx : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f))
    (hy : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card =
      if (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ), s] f then 0 else p ^ 2

/-- **Common lifts of two points with dependent gradients.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $(r_1, s_1)$ and
$(r_2, s_2)$ be pairs of integers in $\{0, \dots, p - 1\}$ with $p \mid f(r_i, s_i)$ for
$i = 1, 2$. Write $a_i = f_x(r_i, s_i)$, $b_i = f_y(r_i, s_i)$ and $c_i = f(r_i, s_i)/p$.
Suppose that for each $i$ the integers $a_i$ and $b_i$ are not both divisible by $p$, and that
$p \mid a_1 b_2 - b_1 a_2$. Write $F_i(k, l) = f(r_i + kp, s_i + lp)$, and among the pairs
$(k, l)$ with $0 \le k, l < p$ let $n_1$ be the number with $p \mid F_i(k, l)$ and
$p^2 \nmid F_i(k, l)$ for both $i$, let $n_2$ be the number with $p^2 \mid F_1(k, l)$,
$p \mid F_2(k, l)$ and $p^2 \nmid F_2(k, l)$, and let $n_3$ be the number with
$p^2 \mid F_1(k, l)$ and $p^2 \mid F_2(k, l)$. If $p$ divides both $a_1 c_2 - c_1 a_2$ and
$b_1 c_2 - c_1 b_2$ (the matrix with rows $(a_i, b_i, c_i)$ has rank $1$ modulo $p$), then
$n_1 = p(p - 1)$, $n_2 = 0$ and $n_3 = p$. Otherwise (rank $2$) $n_1 = p(p - 2)$, $n_2 = p$
and $n_3 = 0$.

The source assumes only that $f$ has no zero modulo $p^2$ at which $f_x \equiv f_y \equiv 0
\pmod p$ and that one column is non-zero. The counts need both gradients $(a_i, b_i)$ non-zero
modulo $p$, which the paper's Case 2 uses. Without this they fail for $f = -x^2 + y^2 - x - 1$,
$p = 3$, $(r_1, s_1) = (0, 1)$, $(r_2, s_2) = (1, 0)$: the gradient vanishes at $(1, 0)$, the
rank is $2$, and $(n_1, n_2, n_3) = (6, 3, 0)$ rather than $(3, 3, 0)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Proposition 4 (`integers-2026-A82-prop-4`). -/
public theorem_wanted card_common_lift_padicVal_of_gradients_dependent {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r₁ s₁ r₂ s₂ : ℕ} (hr₁ : r₁ < p) (hs₁ : s₁ < p) (hr₂ : r₂ < p)
    (hs₂ : s₂ < p) (h₁ : (p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] f)
    (h₂ : (p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] f)
    (hns₁ : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f) ∧
      (p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f)))
    (hns₂ : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f) ∧
      (p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f)))
    (hdep : (p : ℤ) ∣
      MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f) -
        MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f)) :
    let a₁ := MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f)
    let b₁ := MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f)
    let c₁ := MvPolynomial.eval ![(r₁ : ℤ), s₁] f / p
    let a₂ := MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f)
    let b₂ := MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f)
    let c₂ := MvPolynomial.eval ![(r₂ : ℤ), s₂] f / p
    let rankOne : Prop := (p : ℤ) ∣ a₁ * c₂ - c₁ * a₂ ∧ (p : ℤ) ∣ b₁ * c₂ - c₁ * b₂
    let F₁ : ℕ × ℕ → ℤ := fun kl =>
      MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f
    let F₂ : ℕ × ℕ → ℤ := fun kl =>
      MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f
    let one : ℤ → Prop := fun v => (p : ℤ) ∣ v ∧ ¬ (p : ℤ) ^ 2 ∣ v
    let n₁ := ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
      one (F₁ kl) ∧ one (F₂ kl)).card
    let n₂ := ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
      (p : ℤ) ^ 2 ∣ F₁ kl ∧ one (F₂ kl)).card
    let n₃ := ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
      (p : ℤ) ^ 2 ∣ F₁ kl ∧ (p : ℤ) ^ 2 ∣ F₂ kl).card
    (rankOne → n₁ = p * (p - 1) ∧ n₂ = 0 ∧ n₃ = p) ∧
      (¬ rankOne → n₁ = p * (p - 2) ∧ n₂ = p ∧ n₃ = 0)

/-- **Points of $C_f(\mathbb{F}_p)$.** For $f \in \mathbb{Z}[x, y]$ and a natural number $p$,
$C_f(\mathbb{F}_p)$ is the set of pairs $(r, s)$ of natural numbers with $r, s < p$ such that $p$
divides $f(r, s)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`C_f(𝔽_p)` and `m = |C_f(𝔽_p)|`). -/
public noncomputable def valuationCurvePoints (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Finset (ℕ × ℕ) := by
  classical exact
    (Finset.range p ×ˢ Finset.range p).filter fun rs : ℕ × ℕ =>
      (p : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f

/-- **$C_f(\mathbb{F}_p)$ has at most $p^2$ points.** For every $f \in \mathbb{Z}[x, y]$ and
every natural number $p$, the set $C_f(\mathbb{F}_p)$ of pairs $(r, s)$ of natural numbers with
$r, s < p$ such that $p$ divides $f(r, s)$ has at most $p^2$ elements.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`C_f(𝔽_p)`). -/
public theorem valuationCurvePoints_card_le (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    (valuationCurvePoints f p).card ≤ p ^ 2 := by
  classical
  unfold valuationCurvePoints
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product, sq]

/-- **Valuation row of a point.** For $f \in \mathbb{Z}[x, y]$ with partial derivatives $f_x$ and
$f_y$, a natural number $p$ and a pair $(r, s)$ of natural numbers, the valuation row at $(r, s)$
is the vector $(f_x(r, s), f_y(r, s), q)$ reduced modulo $p$, an element of
$(\mathbb{Z}/p\mathbb{Z})^3$, where $q$ is $f(r, s)/p$ rounded down ($q = 0$ when $p = 0$).
These are the rows of the matrix in the paper's eq. (2); when $p$ divides $f(r, s)$, the
division by $p$ is exact.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, eq. (2). -/
public noncomputable def valuationRow (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) (rs : ℕ × ℕ) :
    Fin 3 → ZMod p :=
  ![((MvPolynomial.eval ![(rs.1 : ℤ), rs.2] (MvPolynomial.pderiv 0 f) : ℤ) : ZMod p),
    ((MvPolynomial.eval ![(rs.1 : ℤ), rs.2] (MvPolynomial.pderiv 1 f) : ℤ) : ZMod p),
    ((MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f / p : ℤ) : ZMod p)]

/-- **Distinct $k$-tuples of points of $C_f(\mathbb{F}_p)$.** For $f \in \mathbb{Z}[x, y]$ and
natural numbers $p$ and $k$, let $C_f(\mathbb{F}_p)$ be the set of pairs $(r, s)$ of natural
numbers with $r, s < p$ such that $p$ divides $f(r, s)$. The distinct $k$-tuples of points of
$C_f(\mathbb{F}_p)$ are the $k$-tuples $(P_1, \dots, P_k)$ with every $P_i$ in $C_f(\mathbb{F}_p)$
and $P_i \ne P_j$ for $i \ne j$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`m_k(f, p)`) and Section 3 (sums over `l₁ ≠ l₂ ≠ ⋯ ≠ l_k`). -/
public noncomputable def valuationDistinctTuples (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ) :
    Finset (Fin k → ℕ × ℕ) := by
  classical exact
    (Fintype.piFinset fun _ : Fin k => valuationCurvePoints f p).filter Function.Injective

/-- **Rank-two tuple count $m_k(f, p)$.** For $f \in \mathbb{Z}[x, y]$ and natural numbers $p$
and $k$, let $C_f(\mathbb{F}_p)$ be the set of pairs $(r, s)$ of natural numbers with $r, s < p$
such that $p$ divides $f(r, s)$. Then $m_k(f, p)$ is the number of $k$-tuples
$P = (P_1, \dots, P_k)$ of pairwise distinct points of $C_f(\mathbb{F}_p)$ such that the
$k \times 3$ matrix $B_k(P)$ over $\mathbb{Z}/p\mathbb{Z}$ whose $i$-th row is the valuation row
at $P_i$ has rank $2$ and the $k \times 2$ submatrix of its first two columns also has
rank $2$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 (definition of
`m_k(f, p)` after eq. (2)). -/
public noncomputable def valuationRankTwoTupleCount (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ) :
    ℕ := by
  classical exact
    ((valuationDistinctTuples f p k).filter fun P =>
      (Matrix.of fun i j => valuationRow f p (P i) j).rank = 2 ∧
        (Matrix.of fun i (j : Fin 2) => valuationRow f p (P i) j.castSucc).rank = 2).card

/-- **The rank-two tuple count vanishes for $k = 1$.** For every $f \in \mathbb{Z}[x, y]$ and
every prime $p$, the rank-two tuple count $m_1(f, p)$ is $0$: a matrix with a single row has rank
at most $1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1 ("For `k = 1`, we
observe that `m_k(f, p) = 0` trivially"). -/
public theorem valuationRankTwoTupleCount_one (f : MvPolynomial (Fin 2) ℤ) (p : ℕ)
    [Fact p.Prime] : valuationRankTwoTupleCount f p 1 = 0 := by
  classical
  unfold valuationRankTwoTupleCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro P - ⟨h, -⟩
  have := Matrix.rank_le_height (Matrix.of fun i j => valuationRow f p (P i) j)
  omega

/-- **Rank-one tuple count $o_k(f, p)$.** For $f \in \mathbb{Z}[x, y]$ and natural numbers $p$
and $k$, let $C_f(\mathbb{F}_p)$ be the set of pairs $(r, s)$ of natural numbers with $r, s < p$
such that $p$ divides $f(r, s)$. Then $o_k(f, p)$ is the number of $k$-tuples
$P = (P_1, \dots, P_k)$ of pairwise distinct points of $C_f(\mathbb{F}_p)$ such that the
$k \times 3$ matrix $B_k(P)$ over $\mathbb{Z}/p\mathbb{Z}$ whose $i$-th row is the valuation row
at $P_i$ has rank $1$ and the first two columns of $B_k(P)$ are not both zero.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 3 (definition of
`o_k(f, p)` before Proposition 6). -/
public noncomputable def valuationRankOneTupleCount (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ) :
    ℕ := by
  classical exact
    ((valuationDistinctTuples f p k).filter fun P =>
      (Matrix.of fun i j => valuationRow f p (P i) j).rank = 1 ∧
        (Matrix.of fun i (j : Fin 2) => valuationRow f p (P i) j.castSucc) ≠ 0).card

/-- **Common lift count.** Let $f \in \mathbb{Z}[x, y]$, let $p$ and $k$ be natural numbers and
let $P = ((r_1, s_1), \dots, (r_k, s_k))$ be a $k$-tuple of pairs of natural numbers. The common
lift count of $P$ is the number of pairs $(a, b)$ of natural numbers with $a, b < p$ such that
$p^2$ divides $f(r_i + ap, s_i + bp)$ for every $i$.

For a prime $p$ this says that every lift $(r_i + ap, s_i + bp)$ has $p$-adic valuation of $f$
greater than $1$ (a zero value counts as valuation greater than $1$); divided by $p^2$, the count
is the probability of this event for a uniformly random $(a, b) \in \mathbb{F}_p^2$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 3 (definition of the
indicator random variables `Y_{x,y}`). -/
public noncomputable def valuationCommonLiftCount (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ)
    (P : Fin k → ℕ × ℕ) : ℕ := by
  classical exact
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ => ∀ i,
      (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![((P i).1 : ℤ) + kl.1 * p, ((P i).2 : ℤ) + kl.2 * p] f).card

/-- **The common lift count is at most $p^2$.** For every $f \in \mathbb{Z}[x, y]$, all natural
numbers $p$ and $k$ and every $k$-tuple $P$ of pairs of natural numbers, the common lift count of
$P$ is at most $p^2$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 3 (definition of the
indicator random variables `Y_{x,y}`). -/
public theorem valuationCommonLiftCount_le (f : MvPolynomial (Fin 2) ℤ) (p k : ℕ)
    (P : Fin k → ℕ × ℕ) : valuationCommonLiftCount f p k P ≤ p ^ 2 := by
  classical
  unfold valuationCommonLiftCount
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product, sq]

/-- **Count of points of high valuation in a square.** For a polynomial $f \in \mathbb{Z}[x, y]$
and natural numbers $p$, $k$ and $l$, $X(k, l)$ is the number of points $(x, y)$ of the square
$\{kp, \dots, kp + p - 1\} \times \{lp, \dots, lp + p - 1\}$ with $p^2 \mid f(x, y)$. For a
prime $p$ this is the condition $\nu_p(f(x, y)) > 1$, where points with $f(x, y) = 0$ count.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, eq. (1). -/
public noncomputable def valuationSquareCount (f : MvPolynomial (Fin 2) ℤ) (p k l : ℕ) : ℕ := by
  classical exact
    ((Finset.range p ×ˢ Finset.range p).filter fun xy : ℕ × ℕ =>
      (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![((k * p + xy.1 : ℕ) : ℤ), ((l * p + xy.2 : ℕ) : ℤ)] f).card

/-- **Trivial bound for the square count.** For every polynomial $f \in \mathbb{Z}[x, y]$ and all
natural numbers $p$, $k$ and $l$, the number $X(k, l)$ of points $(x, y)$ of the square
$\{kp, \dots, kp + p - 1\} \times \{lp, \dots, lp + p - 1\}$ with $p^2 \mid f(x, y)$ is at most
$p^2$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, eq. (1). -/
public theorem valuationSquareCount_le (f : MvPolynomial (Fin 2) ℤ) (p k l : ℕ) :
    valuationSquareCount f p k l ≤ p ^ 2 := by
  classical
  unfold valuationSquareCount
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product, sq]

/-- **Rajkumar–Shubham Conjecture 1.** For $f \in \mathbb{Z}[x, y]$, the proposition that for
every $k \ge 2$, $m_k(f, p)/p^2 \to 1$ as $p \to \infty$ through the primes, where $m_k(f, p)$ is
the rank-two tuple count.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 1, Conjecture 1,
eq. (3). -/
public def ValuationConjectureOne (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ k ≥ 2, Filter.Tendsto (fun p : ℕ => (valuationRankTwoTupleCount f p k : ℝ) / (p : ℝ) ^ 2)
    (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1)

/-- **Sum of expectations over distinct tuples of points.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $C_f(\mathbb{F}_p)$
be the set of pairs of integers $0 \le r, s < p$ with $p \mid f(r, s)$. Suppose that no
$(r, s) \in C_f(\mathbb{F}_p)$ has $p \mid f_x(r, s)$ and $p \mid f_y(r, s)$, and let $k \ge 1$.
For a $k$-tuple $P$ of points of $C_f(\mathbb{F}_p)$, let $N(P)$ be the number of pairs
$(a, b)$ with $0 \le a, b < p$ such that $p^2 \mid f(r + ap, s + bp)$ for every point $(r, s)$
of $P$. Then
$$
\sum_P \frac{N(P)}{p^2} = \frac{m_k(f, p)}{p^2} + \frac{o_k(f, p)}{p},
$$
where $P$ runs over the $k$-tuples of pairwise distinct points of $C_f(\mathbb{F}_p)$. Here
$m_k(f, p)$ is the number of such $P$ whose matrix $B_k(P)$, with rows
$(f_x(r, s), f_y(r, s), f(r, s)/p)$ modulo $p$ at the points of $P$, has rank $2$ and whose first
two columns have rank $2$, and $o_k(f, p)$ is the number of such $P$ for which $B_k(P)$ has rank
$1$ and its first two columns are not both zero.

In the paper's notation the left side is $\sum_{l_1 \ne \dots \ne l_k} E[Y_{l_1} \cdots Y_{l_k}]$
(eq. (15)). The hypothesis is the paper's standing assumption of Section 3 at this $p$; its
proof uses it to rule out rank $0$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 6, eq. (15)
(`integers-2026-A82-prop-6`). -/
public theorem_wanted sum_expectation_distinct_tuples_eq {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ)
    (hns : ∀ r < p, ∀ s < p, (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f →
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)))
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ P ∈ valuationDistinctTuples f p k, (valuationCommonLiftCount f p k P : ℝ) / (p : ℝ) ^ 2 =
      (valuationRankTwoTupleCount f p k : ℝ) / (p : ℝ) ^ 2 +
        (valuationRankOneTupleCount f p k : ℝ) / p

/-- **Sums of expectations over distinct tuples tend to one.** Let $f \in \mathbb{Z}[x, y]$ have
partial derivatives $f_x$ and $f_y$, and for a prime $p$ let $C_f(\mathbb{F}_p)$ be the set of
pairs of integers $0 \le r, s < p$ with $p \mid f(r, s)$. Suppose that there is a natural number
$P_0$ such that for every prime $p \ge P_0$ and all integers $x, y$, the integers $f(x, y)$,
$f_x(x, y)$ and $f_y(x, y)$ are not all divisible by $p$; that $|C_f(\mathbb{F}_p)|/p \to 1$ as
$p \to \infty$ through the primes; and that Conjecture 1 holds for $f$. For a tuple $P$ of points
of $C_f(\mathbb{F}_p)$, let $N(P)$ be the number of pairs $(a, b)$ with $0 \le a, b < p$ such that
$p^2 \mid f(r + ap, s + bp)$ for every point $(r, s)$ of $P$. Then for every $k \ge 1$,
$\sum_P N(P)/p^2 \to 1$ as $p \to \infty$ through the primes, where $P$ runs over the $k$-tuples
of pairwise distinct points of $C_f(\mathbb{F}_p)$.

In the paper's notation the sum is $\sum_{l_1 \ne \dots \ne l_k} E[Y_{l_1} \cdots Y_{l_k}]$.
The paper's proof takes $|C_f(\mathbb{F}_p)|/p \to 1$ from the Hasse–Weil bounds, which need an
irreducibility hypothesis the paper does not state; it is assumed directly here.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Corollary 5
(`integers-2026-A82-cor-5`), under the standing assumption of Section 3. -/
public theorem_wanted tendsto_sum_expectation_distinct_tuples (f : MvPolynomial (Fin 2) ℤ)
    (hsing : ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ x y : ℤ,
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![x, y] f ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 1 f)))
    (hcurve : Filter.Tendsto (fun p : ℕ => ((valuationCurvePoints f p).card : ℝ) / p)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1))
    (hconj : ValuationConjectureOne f) {k : ℕ} (hk : 1 ≤ k) :
    Filter.Tendsto (fun p : ℕ =>
        ∑ P ∈ valuationDistinctTuples f p k, (valuationCommonLiftCount f p k P : ℝ) / (p : ℝ) ^ 2)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1)

/-- **Poisson limit for points of valuation $> 1$.** Let $f \in \mathbb{Z}[x, y]$ have partial
derivatives $f_x$ and $f_y$, and for a prime $p$ let $C_f(\mathbb{F}_p)$ be the set of pairs of
integers $0 \le r, s < p$ with $p \mid f(r, s)$. Suppose that there is a natural number $P_0$
such that for every prime $p \ge P_0$ and all integers $x, y$, the integers $f(x, y)$,
$f_x(x, y)$ and $f_y(x, y)$ are not all divisible by $p$; that $|C_f(\mathbb{F}_p)|/p \to 1$ as
$p \to \infty$ through the primes; and that Conjecture 1 holds for $f$. For $0 \le k, l < p$ let
$X(k, l)$ be the number of points $(x, y)$ of the square
$\{kp, \dots, kp + p - 1\} \times \{lp, \dots, lp + p - 1\}$ with $p^2 \mid f(x, y)$. Then for
every $j \ge 0$,
$$
\frac{\#\{(k, l) : 0 \le k, l < p,\ X(k, l) = j\}}{p^2} \to \frac{e^{-1}}{j!}
$$
as $p \to \infty$ through the primes. That is, for $(k, l)$ uniformly random in
$\{0, \dots, p - 1\}^2$, $X(k, l)$ converges in distribution to a Poisson variable with
parameter $1$ (for $\mathbb{N}$-valued variables, pointwise convergence of the mass functions is
convergence in distribution).

The hypothesis $|C_f(\mathbb{F}_p)|/p \to 1$ is the Hasse–Weil input of the paper's proof,
assumed directly, as in the companion statement about sums over distinct tuples.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Theorem 1
(`integers-2026-A82-thm-1`). -/
public theorem_wanted tendsto_valuationSquareCount_poisson (f : MvPolynomial (Fin 2) ℤ)
    (hsing : ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ x y : ℤ,
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![x, y] f ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![x, y] (MvPolynomial.pderiv 1 f)))
    (hcurve : Filter.Tendsto (fun p : ℕ => ((valuationCurvePoints f p).card : ℝ) / p)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1))
    (hconj : ValuationConjectureOne f) (j : ℕ) :
    Filter.Tendsto (fun p : ℕ =>
        (((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          valuationSquareCount f p kl.1 kl.2 = j).card : ℝ) / (p : ℝ) ^ 2)
      (Filter.atTop ⊓ Filter.principal {p : ℕ | p.Prime})
      (nhds (Real.exp (-1) / (j.factorial : ℝ)))

end

end MetaMathlibExt
