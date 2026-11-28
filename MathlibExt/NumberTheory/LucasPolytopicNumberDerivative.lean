/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.NumberTheory.LucasPolytopicNumber
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.LucasPolytopicNumberClosedForm

/-!
# Iterated Lucas derivatives of the geometric kernel

For nondegenerate real Lucas parameters $(s,t)$, distinct real numbers $\varphi,\varphi'$
with $\varphi+\varphi'=s$ and $\varphi\varphi'=-t$, and a natural number $n$, the $n$-fold Lucas
derivative of $y\mapsto 1/(1-y)$ at a real number $x$ is the Lucas factorial $\{n\}_{s,t}!$
divided by $\prod_{k=0}^{n}(1-\varphi^{n-k}\varphi'^k x)$, provided this product is nonzero.
The formula includes the zero-fold iterate, whose denominator is $1-x$. At $x=0$ the
Lucas derivative is the ordinary derivative, and the product is nonzero in a neighborhood of $0$.

## References

* Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
  Journal of Integer Sequences 28 (2025), Article 25.5.6, pp. 1–19, §2 and Theorem 8.
* `lucasDerivative`, `lucasDerivative_of_ne_zero`, `lucasDerivative_zero` and `lucasDerivative_id`
  come from `WantedExt.NumberTheory.LucasPolytopicNumberWanted`.
-/

namespace MetaMathlibExt

open scoped BigOperators Topology
open Filter

/-- **Lucas derivative.** For real numbers $\varphi$ and $\varphi'$, the Lucas derivative
$D_{\varphi,\varphi'}$ sends a function $f : \mathbb{R} \to \mathbb{R}$ to the function whose
value at $x \ne 0$ is $(f(\varphi x) - f(\varphi' x))/((\varphi - \varphi')x)$, read as $0$ when
$\varphi = \varphi'$, and whose value at $0$ is the derivative $f'(0)$, read as $0$ when $f$ is
not differentiable at $0$.

In the paper $\varphi \ne \varphi'$ are the roots of $x^2 - sx - t$; its separate definition for
$s^2 + 4t = 0$ is not covered.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
@[expose] public noncomputable def lucasDerivative (φ φ' : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then deriv f 0 else (f (φ * x) - f (φ' * x)) / ((φ - φ') * x)

/-- **The Lucas derivative away from the origin.** For all real numbers $\varphi$, $\varphi'$
and $x \ne 0$ and every function $f : \mathbb{R} \to \mathbb{R}$, the Lucas derivative
$D_{\varphi,\varphi'}$ satisfies
$D_{\varphi,\varphi'} f(x) = (f(\varphi x) - f(\varphi' x))/((\varphi - \varphi')x)$, where the
quotient is read as $0$ when $\varphi = \varphi'$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
public theorem lucasDerivative_of_ne_zero (φ φ' : ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    lucasDerivative φ φ' f x = (f (φ * x) - f (φ' * x)) / ((φ - φ') * x) := by
  simp [lucasDerivative, hx]

/-- **The Lucas derivative at the origin.** For all real numbers $\varphi$, $\varphi'$ and every
function $f : \mathbb{R} \to \mathbb{R}$, the Lucas derivative $D_{\varphi,\varphi'}$ satisfies
$D_{\varphi,\varphi'} f(0) = f'(0)$, where $f'(0)$ is read as $0$ when $f$ is not differentiable
at $0$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
public theorem lucasDerivative_zero (φ φ' : ℝ) (f : ℝ → ℝ) :
    lucasDerivative φ φ' f 0 = deriv f 0 := by
  simp [lucasDerivative]

/-- **The Lucas derivative of the identity.** For distinct real numbers $\varphi \ne \varphi'$,
the Lucas derivative $D_{\varphi,\varphi'}$ of the identity function $y \mapsto y$ equals $1$ at
every real number $x$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Section 2 (definition of the
Lucas-derivative). -/
public theorem lucasDerivative_id {φ φ' : ℝ} (h : φ ≠ φ') (x : ℝ) :
    lucasDerivative φ φ' (fun y => y) x = 1 := by
  by_cases hx : x = 0
  · simp [lucasDerivative, hx]
  · rw [lucasDerivative_of_ne_zero _ _ _ hx, ← sub_mul]
    exact div_self (mul_ne_zero (sub_ne_zero.mpr h) hx)

private def lucasDenominator (φ φ' : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), (1 - φ ^ (n - k) * φ' ^ k * x)

private theorem lucasDenominator_succ_left (φ φ' : ℝ) (n : ℕ) (x : ℝ) :
    lucasDenominator φ φ' (n + 1) x =
      lucasDenominator φ φ' n (φ * x) * (1 - φ' ^ (n + 1) * x) := by
  simp only [lucasDenominator, Finset.prod_range_succ _ (n + 1), Nat.sub_self, pow_zero, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [show n + 1 - k = (n - k) + 1 by have := Finset.mem_range.mp hk; omega, pow_succ]
  ring

private theorem lucasDenominator_succ_right (φ φ' : ℝ) (n : ℕ) (x : ℝ) :
    lucasDenominator φ φ' (n + 1) x =
      lucasDenominator φ φ' n (φ' * x) * (1 - φ ^ (n + 1) * x) := by
  simp only [lucasDenominator, Finset.prod_range_succ' _ (n + 1), Nat.add_sub_add_right,
    Nat.sub_zero, pow_zero, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [pow_succ φ' k, mul_assoc]

private theorem lucasDenominator_zero (φ φ' : ℝ) (n : ℕ) :
    lucasDenominator φ φ' n 0 = 1 := by
  simp [lucasDenominator]

private theorem hasDerivAt_lucasDenominator_zero (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (hne : φ ≠ φ') (n : ℕ) :
    HasDerivAt (lucasDenominator φ φ' n) (-lucasBracket P (n + 1)) 0 := by
  have hsum_coeff : ∑ k ∈ Finset.range (n + 1), φ ^ (n - k) * φ' ^ k = lucasBracket P (n + 1) := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
    calc
      _ = -(∑ k ∈ Finset.range (n + 1), φ ^ (n - k) * φ' ^ k) * (φ' - φ) := by ring
      _ = φ ^ (n + 1) - φ' ^ (n + 1) := by
        simpa only [Nat.add_sub_cancel, mul_comm (φ' ^ _), neg_mul, neg_sub] using
          congrArg Neg.neg (geom_sum₂_mul φ' φ (n + 1))
      _ = _ := by rw [mul_comm, lucasBracket_closed_form P φ φ' hsum hprod]
  have hf (k : ℕ) : HasDerivAt (fun y : ℝ => 1 - φ ^ (n - k) * φ' ^ k * y)
      (-(φ ^ (n - k) * φ' ^ k)) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub
      ((hasDerivAt_id (0 : ℝ)).const_mul (φ ^ (n - k) * φ' ^ k))
  unfold lucasDenominator
  simpa only [mul_zero, sub_zero, Finset.prod_const_one, one_smul,
    Finset.sum_neg_distrib, hsum_coeff] using
      HasDerivAt.fun_finsetProd (u := Finset.range (n + 1)) (fun k _ => hf k)

/-- **Iterated Lucas derivatives of $1/(1 - x)$.** Let $(s, t)$ be nondegenerate Lucas
parameters, let $\varphi \ne \varphi'$ be real numbers with $\varphi + \varphi' = s$ and
$\varphi\varphi' = -t$, write $D_{\varphi,\varphi'}$ for the Lucas derivative and
$\{n\}_{s,t}!$ for the $s,t$-factorial. For every natural number $n$ and every real number $x$
with $\prod_{k=0}^{n} (1 - \varphi^{n-k}\varphi'^k x) \ne 0$, the $n$-fold iterate of
$D_{\varphi,\varphi'}$ applied to the function $y \mapsto 1/(1 - y)$ has value at $x$
$$\frac{\{n\}_{s,t}!}{\prod_{k=0}^{n} (1 - \varphi^{n-k}\varphi'^k x)}.$$

With $q = \varphi'/\varphi$ the denominator is the $q$-Pochhammer symbol
$(\varphi^n x; q)_{n+1}$ of the paper, which states the identity for $n \ge 1$. Real distinct
$\varphi, \varphi'$ exist only when $s^2 + 4t > 0$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 8
(`jis-2025-25.5.6-thm-8`). -/
public theorem iterate_lucasDerivative_inv_one_sub (P : LucasParameters) (φ φ' : ℝ)
    (hsum : φ + φ' = P.s) (hprod : φ * φ' = -P.t) (hne : φ ≠ φ') (n : ℕ) (x : ℝ)
    (hx : ∏ k ∈ Finset.range (n + 1), (1 - φ ^ (n - k) * φ' ^ k * x) ≠ 0) :
    (lucasDerivative φ φ')^[n] (fun y => 1 / (1 - y)) x =
      lucasFactorial P n / ∏ k ∈ Finset.range (n + 1), (1 - φ ^ (n - k) * φ' ^ k * x) := by
  change (lucasDerivative φ φ')^[n] (fun y => 1 / (1 - y)) x =
    lucasFactorial P n / lucasDenominator φ φ' n x
  change lucasDenominator φ φ' n x ≠ 0 at hx
  induction n generalizing x with
  | zero => simp [lucasDenominator]
  | succ n ih =>
    rw [Function.iterate_succ_apply', lucasFactorial_succ]
    by_cases hx₀ : x = 0
    · subst x
      rw [lucasDerivative_zero, lucasDenominator_zero, div_one]
      -- The induction hypothesis describes the iterate on a whole neighborhood of zero.
      have hd := hasDerivAt_lucasDenominator_zero P φ φ' hsum hprod hne n
      have hnz : lucasDenominator φ φ' n 0 ≠ 0 := by simp [lucasDenominator_zero]
      have heq : (lucasDerivative φ φ')^[n] (fun y : ℝ => 1 / (1 - y)) =ᶠ[𝓝 0]
          (fun y => lucasFactorial P n / lucasDenominator φ φ' n y) :=
        (hd.continuousAt.eventually_ne hnz).mono fun y hy => ih y hy
      have hquot := (hd.inv hnz).const_mul (lucasFactorial P n)
      have hq : HasDerivAt (fun y => lucasFactorial P n / lucasDenominator φ φ' n y)
          (lucasFactorial P n * lucasBracket P (n + 1)) 0 := by
        simpa [div_eq_mul_inv, lucasDenominator_zero] using hquot
      exact (hq.congr_of_eventuallyEq heq).deriv
    · -- Each shifted product is missing a different endpoint of the new denominator.
      have hleft := lucasDenominator_succ_left φ φ' n x
      have hright := lucasDenominator_succ_right φ φ' n x
      obtain ⟨hl, hlast⟩ := mul_ne_zero_iff.mp (hleft ▸ hx)
      obtain ⟨hr, hfirst⟩ := mul_ne_zero_iff.mp (hright ▸ hx)
      rw [lucasDerivative_of_ne_zero _ _ _ hx₀, ih _ hl, ih _ hr]
      have hterm_left :
          lucasFactorial P n / lucasDenominator φ φ' n (φ * x) =
            lucasFactorial P n * (1 - φ' ^ (n + 1) * x) / lucasDenominator φ φ' (n + 1) x := by
        rw [hleft, mul_div_mul_right _ _ hlast]
      have hterm_right :
          lucasFactorial P n / lucasDenominator φ φ' n (φ' * x) =
            lucasFactorial P n * (1 - φ ^ (n + 1) * x) / lucasDenominator φ φ' (n + 1) x := by
        rw [hright, mul_div_mul_right _ _ hfirst]
      have hendpoints : (1 - φ' ^ (n + 1) * x) - (1 - φ ^ (n + 1) * x) =
          lucasBracket P (n + 1) * ((φ - φ') * x) := by
        rw [show (1 - φ' ^ (n + 1) * x) - (1 - φ ^ (n + 1) * x) =
          (φ ^ (n + 1) - φ' ^ (n + 1)) * x by ring, ← lucasBracket_closed_form P φ φ' hsum hprod]
        ring
      rw [hterm_left, hterm_right, ← sub_div, ← mul_sub, hendpoints, div_div, ← mul_assoc,
        mul_div_mul_right _ _ (mul_ne_zero (sub_ne_zero.mpr hne) hx₀)]

end MetaMathlibExt
