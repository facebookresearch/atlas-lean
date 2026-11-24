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
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Values of CL-polynomials on the canonical line

A CL-polynomial of degree `d` takes values in `ℝ · I ^ d` on the line of real part `-1/2`.
-/

namespace MetaMathlibExt

open Polynomial
open scoped BigOperators

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

/-- **The h-star coefficients of a polynomial.** Let $f$ be a complex polynomial of degree $d$,
with $d = 0$ for the zero polynomial. For a natural number $i$, the $i$-th $h^*$-coefficient of
$f$ is
$$h^*_i(f) = \sum_{j=0}^{i} (-1)^j \binom{d+1}{j} f(i-j),$$
the coefficient of $t^i$ in the power series $(1-t)^{d+1} \sum_{k \ge 0} f(k)\, t^k$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of the `h*`-polynomial.
-/
public def hStarCoeff (f : Polynomial ℂ) (i : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (i + 1),
    (-1 : ℂ) ^ j * (Nat.choose (f.natDegree + 1) j : ℂ) * f.eval (i - j : ℂ)

/-- **SNN polynomials.** For a complex polynomial $f$ of degree $d$ and a natural number $i$, let
$h^*_i(f)$ be the coefficient of $t^i$ in $(1 - t)^{d+1} \sum_{k \ge 0} f(k)\, t^k$. Then $f$ is
SNN when $f \ne 0$ and its $h^*$-coefficients $h^*_0(f), \dots, h^*_d(f)$ are real and
nonnegative.

Coefficients beyond the degree, which vanish by the generating-series identity, are not part of
the condition.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of SNN-polynomial.
-/
public def IsSNN (f : Polynomial ℂ) : Prop :=
  f ≠ 0 ∧ ∀ i ≤ f.natDegree, 0 ≤ (hStarCoeff f i).re ∧ (hStarCoeff f i).im = 0

-- At the first index beyond the degree, the sum is a full forward difference
-- evaluated at zero, with its summation order reversed.
private theorem hStarCoeff_natDegree_add_one (f : Polynomial ℂ) :
    hStarCoeff f (f.natDegree + 1) = 0 := by
  let n := f.natDegree + 1
  have h := congrFun f.fwdDiff_iter_degree_add_one_eq_zero (0 : ℂ)
  rw [fwdDiff_iter_eq_sum_shift] at h
  change (∑ k ∈ Finset.range (n + 1),
    ((-1 : ℤ) ^ (n - k) * n.choose k) • f.eval (0 + k • (1 : ℂ))) = 0 at h
  unfold hStarCoeff
  change (∑ j ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ j * (n.choose j : ℂ) * f.eval ((n : ℂ) - (j : ℂ))) = 0
  rw [← Finset.sum_range_reflect (fun j ↦
    (-1 : ℂ) ^ j * (n.choose j : ℂ) * f.eval ((n : ℂ) - (j : ℂ))) (n + 1)]
  refine Eq.trans (Finset.sum_congr rfl fun k hk ↦ ?_) h
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [Nat.add_sub_cancel, Nat.choose_symm hk', Nat.cast_sub hk', sub_sub_cancel]
  simp [zsmul_eq_mul, nsmul_eq_mul]

private def signedChoose (n j : ℕ) : ℂ := (-1 : ℂ) ^ j * (n.choose j : ℂ)

-- Pascal's identity and the weighted binomial identity combine the two adjacent terms.
private theorem signedChoose_mul_linear (n j : ℕ) (x : ℂ) :
    signedChoose (n + 1) (j + 1) * (2 * (x - (j + 1 : ℕ)) + 1) =
      (2 * x + 1) * signedChoose n (j + 1) +
        (2 * (n : ℂ) + 1 - 2 * x) * signedChoose n j := by
  have hPascal : signedChoose (n + 1) (j + 1) = signedChoose n (j + 1) - signedChoose n j := by
    simp only [signedChoose, Nat.choose_succ_succ' n j, Nat.cast_add, pow_succ]
    ring
  have hWeighted : ((j + 1 : ℕ) : ℂ) * signedChoose (n + 1) (j + 1) =
      -((n + 1 : ℕ) : ℂ) * signedChoose n j := by
    have h := congrArg (fun k : ℕ ↦ (k : ℂ)) (Nat.add_one_mul_choose_eq n j)
    push_cast at h
    simp only [signedChoose, pow_succ, Nat.cast_add, Nat.cast_one]
    calc
      _ = -((-1 : ℂ) ^ j) * (↑((n + 1).choose (j + 1)) * ((j : ℂ) + 1)) := by ring
      _ = _ := by rw [← h]; ring
  calc
    _ = (2 * x + 1) * signedChoose (n + 1) (j + 1) -
        2 * (((j + 1 : ℕ) : ℂ) * signedChoose (n + 1) (j + 1)) := by ring
    _ = _ := by rw [hWeighted, hPascal]; push_cast; ring

-- The new h-star coefficient is a weighted sum of two adjacent old coefficients.
private theorem hStarCoeff_mul_linear_succ (f : Polynomial ℂ)
    (hd : ((2 * X + 1) * f).natDegree = f.natDegree + 1) (i : ℕ) :
    hStarCoeff ((2 * X + 1) * f) (i + 1) =
      (2 * ((i + 1 : ℕ) : ℂ) + 1) * hStarCoeff f (i + 1) +
        (2 * ((f.natDegree + 1 : ℕ) : ℂ) + 1 - 2 * ((i + 1 : ℕ) : ℂ)) * hStarCoeff f i := by
  unfold hStarCoeff
  rw [hd]
  let n := f.natDegree + 1
  let x : ℂ := (i + 1 : ℕ)
  change (∑ j ∈ Finset.range (i + 1 + 1), signedChoose (n + 1) j *
      ((2 * X + 1) * f).eval (x - (j : ℂ))) =
    (2 * x + 1) * (∑ j ∈ Finset.range (i + 1 + 1), signedChoose n j * f.eval (x - (j : ℂ))) +
      (2 * (n : ℂ) + 1 - 2 * x) *
        (∑ j ∈ Finset.range (i + 1), signedChoose n j * f.eval ((i : ℂ) - (j : ℂ)))
  rw [Finset.sum_range_succ', Finset.mul_sum, Finset.mul_sum,
    Finset.sum_range_succ' (n := i + 1)]
  have hzero (m : ℕ) : signedChoose m 0 = 1 := by simp [signedChoose]
  simp only [hzero, Nat.cast_zero, sub_zero, eval_mul, eval_add, eval_ofNat, eval_X, eval_one,
    one_mul]
  conv_rhs => rw [add_right_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← mul_assoc, signedChoose_mul_linear,
    show x - ((j + 1 : ℕ) : ℂ) = (i : ℂ) - (j : ℂ) by dsimp [x]; push_cast; ring]
  ring

/-- **Multiplying by $2X+1$ preserves SNN.** For every complex polynomial $f$, if $f$ is an SNN
polynomial, then so is $(2X + 1) f$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 6.
-/
public theorem two_mul_X_add_one_preserves_snn (f : Polynomial ℂ) (hf : IsSNN f) :
    IsSNN ((2 * X + 1) * f) := by
  have hlinear : (2 * X + 1 : Polynomial ℂ).natDegree = 1 := by
    rw [show (2 : Polynomial ℂ) = C (2 : ℂ) from (map_ofNat C 2).symm]
    rw [← C_1, natDegree_add_C, natDegree_C_mul (by norm_num : (2 : ℂ) ≠ 0), natDegree_X]
  have hne : (2 * X + 1 : Polynomial ℂ) ≠ 0 := by
    intro h
    simp [h] at hlinear
  have hd : ((2 * X + 1) * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_mul hne hf.1, hlinear, add_comm]
  refine ⟨mul_ne_zero hne hf.1, ?_⟩
  rw [hd]
  intro i hi
  cases i with
  | zero =>
    have hzero (p : Polynomial ℂ) : hStarCoeff p 0 = p.eval 0 := by simp [hStarCoeff]
    simpa [hzero] using hf.2 0 (Nat.zero_le _)
  | succ i =>
    have hi' : i ≤ f.natDegree := Nat.le_of_succ_le_succ hi
    obtain ⟨hre₀, him₀⟩ := hf.2 i hi'
    have hnext : 0 ≤ (hStarCoeff f (i + 1)).re ∧ (hStarCoeff f (i + 1)).im = 0 := by
      rcases hi.lt_or_eq with hlt | heq
      · exact hf.2 _ (Nat.le_of_lt_succ hlt)
      · rw [heq, hStarCoeff_natDegree_add_one]
        simp
    obtain ⟨hre₁, him₁⟩ := hnext
    rw [hStarCoeff_mul_linear_succ f hd]
    have hgap : 0 ≤ (f.natDegree : ℝ) - i := sub_nonneg.mpr (by exact_mod_cast hi')
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat, him₀, him₁,
      mul_zero, zero_mul, add_zero, sub_zero, and_true]
    push_cast
    rw [show 2 * ((f.natDegree : ℝ) + 1) + 1 - 2 * ((i : ℝ) + 1) =
      2 * ((f.natDegree : ℝ) - i) + 1 by ring]
    exact add_nonneg (mul_nonneg (by positivity) hre₁) (mul_nonneg (by positivity) hre₀)

end

end MetaMathlibExt
