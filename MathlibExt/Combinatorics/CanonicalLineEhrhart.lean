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
import Mathlib.Algebra.Ring.Parity
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

end

end MetaMathlibExt
