/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.FieldTheory.Minpoly.Basic

/-!
# Real cyclotomic polynomial — support definition
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Real cyclotomic polynomial.** For a natural number $n$, the real cyclotomic polynomial
$\psi_n \in \mathbb{Z}[X]$ is the minimal polynomial over $\mathbb{Z}$ of the complex number
$\zeta + \zeta^{-1}$, where $\zeta = e^{2\pi i/n}$; for $n \ge 1$ this number is $2\cos(2\pi/n)$.

The definition covers every $n$ (for $n = 0$ the exponent $2\pi i/n$ is read as $0$, so
$\zeta = 1$), but results about $\psi_n$ assume $n > 2$.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of
Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19
(2016), source lines 83-90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455
normalized no-final-newline span SHA-256
e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039 -/
public noncomputable def realCyclotomicPolynomial (n : ℕ) : Polynomial ℤ :=
  minpoly ℤ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) +
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)))⁻¹)

end MetaMathlibExt
