/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Values of CL-polynomials on the canonical line

A CL-polynomial of degree `d` takes values in `ℝ · I ^ d` on the line of real part `-1/2`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public noncomputable section

/-- **Canonical line.** The canonical line $\mathrm{CL}$ is the vertical line of complex numbers
with real part $-1/2$, that is, $\mathrm{CL} = \{z \in \mathbb{C} : \operatorname{Re} z = -1/2\}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Definition of `CL`.
-/
public def canonicalLine : Set ℂ := {z | z.re = -(1 / 2 : ℝ)}

/-- **Product of quadratic canonical-line factors.** For a finite list $c_1, \dots, c_m$ of real
numbers, this is the monic complex polynomial $\prod_{k=1}^{m} (X^2 + X + c_k)$; the empty list
gives the constant polynomial $1$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, factored definition of CL-polynomials.
-/
public def clQuadraticProduct (cs : List ℝ) : Polynomial ℂ :=
  (cs.map fun c => X ^ 2 + X + C (c : ℂ)).prod

/-- **CL-polynomials with given parameters.** Let $f$ be a complex polynomial of degree $d$, let
$a$ be a real number, and let $c_1, \dots, c_m$ be a list of real numbers. Then $f$ is a
CL-polynomial with scale $a$ and parameters $c_1, \dots, c_m$ when $a \ne 0$, every $c_i \ge 1/4$,
$m = \lfloor d/2 \rfloor$, and $f = a \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is even and
$f = a (2X + 1) \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is odd.

The parameters form a list so that later statements can refer to individual parameters.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of CL-polynomial.
-/
public def IsCLWithParameters (f : Polynomial ℂ) (a : ℝ) (cs : List ℝ) : Prop :=
  a ≠ 0 ∧
    (∀ c ∈ cs, (1 / 4 : ℝ) ≤ c) ∧
    if Even f.natDegree then
      f = C (a : ℂ) * clQuadraticProduct cs ∧ cs.length = f.natDegree / 2
    else
      f = C (a : ℂ) * (2 * X + 1) * clQuadraticProduct cs ∧
        cs.length = f.natDegree / 2

/-- **CL-polynomials.** A complex polynomial $f$ of degree $d$ is a CL-polynomial when there are
a real number $a \ne 0$ and real numbers $c_1, \dots, c_m \ge 1/4$ with $m = \lfloor d/2 \rfloor$
such that $f = a \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is even and
$f = a (2X + 1) \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is odd.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of CL-polynomial.
-/
public def IsCL (f : Polynomial ℂ) : Prop := ∃ a cs, IsCLWithParameters f a cs

private theorem eval_clQuadraticProduct (cs : List ℝ) (z : ℂ) (hz : z ∈ canonicalLine) :
    ∃ r : ℝ, (clQuadraticProduct cs).eval z = (r : ℂ) * Complex.I ^ (2 * cs.length) := by
  change z.re = -(1 / 2 : ℝ) at hz
  induction cs with
  | nil => exact ⟨1, by simp [clQuadraticProduct]⟩
  | cons c cs ih =>
    obtain ⟨r, hr⟩ := ih
    have hquad : z ^ 2 + z + (c : ℂ) =
        ((z.im ^ 2 + 1 / 4 - c : ℝ) : ℂ) * Complex.I ^ 2 := by
      rw [Complex.I_sq]
      apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, hz] <;> ring
    refine ⟨(z.im ^ 2 + 1 / 4 - c) * r, ?_⟩
    change ((X ^ 2 + X + C (c : ℂ)) * clQuadraticProduct cs).eval z = _
    simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, hquad, hr, List.length_cons,
      Nat.mul_succ, pow_add, Complex.ofReal_mul]
    ring

/-- **Values of CL-polynomials on the canonical line.** If $f$ is a CL-polynomial of degree $d$,
then for every $z$ on the canonical line there is a real number $r$ with $f(z) = r\, i^d$; that
is, $f$ maps the canonical line into $\mathbb{R}\, i^d$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 2.
-/
public theorem cl_value_on_canonicalLine (f : Polynomial ℂ) (hf : IsCL f)
    (z : ℂ) (hz : z ∈ canonicalLine) :
    ∃ r : ℝ, f.eval z = (r : ℂ) * Complex.I ^ f.natDegree := by
  obtain ⟨a, cs, _, _, hfactor⟩ := hf
  obtain ⟨r, hr⟩ := eval_clQuadraticProduct cs z hz
  split at hfactor
  · rename_i heven
    obtain ⟨hf, hlen⟩ := hfactor
    have hd : f.natDegree = 2 * cs.length := by
      obtain ⟨k, hk⟩ := heven
      omega
    exact ⟨a * r, by rw [hd, hf, eval_mul, eval_C, hr, Complex.ofReal_mul, mul_assoc]⟩
  · rename_i hodd
    obtain ⟨hf, hlen⟩ := hfactor
    have hd : f.natDegree = 2 * cs.length + 1 := by
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
      omega
    have hlinear : 2 * z + 1 = ((2 * z.im : ℝ) : ℂ) * Complex.I := by
      change z.re = -(1 / 2 : ℝ) at hz
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hz]
    refine ⟨a * (2 * z.im) * r, ?_⟩
    rw [hd, hf]
    simp only [eval_mul, eval_C, eval_add, eval_ofNat, eval_X, eval_one, hlinear, hr,
      Complex.ofReal_mul, pow_succ]
    ring

/-- **Binomial polynomial.** For an integer $n$ and a natural number $d$, the binomial polynomial
$\binom{X+n}{d}$ is the real polynomial $\frac{1}{d!} \prod_{i=0}^{d-1} (X + n - i)$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 7.
-/
public def binomialPolynomial (n : ℤ) (d : ℕ) : Polynomial ℝ :=
  ((d.factorial : ℝ)⁻¹) •
    ∏ i ∈ Finset.range d, (X + C ((n - (i : ℤ) : ℤ) : ℝ))

-- Keep the original index bounds in the API; the factorization does not need them.
set_option linter.unusedVariables false in
/-- **Multiplying a binomial polynomial by a quadratic.** For an integer $n$ and a natural number
$k$, write $\binom{X+n}{k} = \frac{1}{k!} \prod_{i=0}^{k-1} (X + n - i)$ for the real binomial
polynomial. Let $d$ and $j$ be natural numbers with $0 < d$ and $j \le d$, and let $c$ be a real
number. Then
$$
(X^2 + X + c) \binom{X+d-j}{d} = \alpha \binom{X+d-j+2}{d+2} + \beta \binom{X+d-j+1}{d+2} +
\gamma \binom{X+d-j}{d+2},
$$
where $\alpha = j^2 + j + c$, $\beta = 2(dj - j^2 + d + 1 - c)$ and
$\gamma = d^2 - 2dj - j + j^2 + d + c$.

The paper assumes $c \ge 1/4$; the identity holds for every real $c$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 7.
-/
public theorem quadratic_mul_binomialPolynomial (d j : ℕ) (hd : 0 < d) (hj : j ≤ d)
    (c : ℝ) :
    (X ^ 2 + X + C c) * binomialPolynomial ((d : ℤ) - (j : ℤ)) d =
      C ((j : ℝ) ^ 2 + (j : ℝ) + c) *
          binomialPolynomial ((d : ℤ) - (j : ℤ) + 2) (d + 2) +
        C (2 * ((d : ℝ) * (j : ℝ) - (j : ℝ) ^ 2 + (d : ℝ) + 1 - c)) *
          binomialPolynomial ((d : ℤ) - (j : ℤ) + 1) (d + 2) +
        C ((d : ℝ) ^ 2 - 2 * (d : ℝ) * (j : ℝ) - (j : ℝ) +
            (j : ℝ) ^ 2 + (d : ℝ) + c) *
          binomialPolynomial ((d : ℤ) - (j : ℤ)) (d + 2) := by
  let P (a : ℝ) (k : ℕ) : Polynomial ℝ :=
    ∏ i ∈ Finset.range k, (X + C (a - (i : ℝ)))
  have hbinom (n : ℤ) (k : ℕ) :
      binomialPolynomial n k = C ((k.factorial : ℝ)⁻¹) * P n k := by
    simp only [binomialPolynomial, P, smul_eq_C_mul, Int.cast_sub, Int.cast_natCast]
  have hfront (a : ℝ) (k : ℕ) :
      P (a + 1) (k + 1) = P a k * (X + C (a + 1)) := by
    dsimp only [P]
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_succ, add_sub_add_right_eq_sub, Nat.cast_zero, sub_zero]
  have hback (a : ℝ) (k : ℕ) :
      P a (k + 1) = P a k * (X + C (a - (k : ℝ))) :=
    Finset.prod_range_succ _ _
  have hfactorial : (d.factorial : ℝ)⁻¹ =
      ((d : ℝ) + 2) * ((d : ℝ) + 1) * (((d + 2).factorial : ℝ)⁻¹) := by
    rw [show d + 2 = (d + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp (disch := positivity)
    ring
  -- Each degree-(d+2) product contains P (d - j) d, with two extra factors.
  simp only [hbinom, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Int.cast_one]
  set a : ℝ := (d : ℝ) - (j : ℝ)
  rw [show a + 2 = (a + 1) + 1 by ring, hfront (a + 1) (d + 1), hfront a d,
    hfront a (d + 1), hback a (d + 1), hback a d, hfactorial]
  dsimp only [a]
  simp only [Nat.cast_succ, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  ring

end

end MetaMathlibExt
