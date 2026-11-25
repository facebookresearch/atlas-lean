/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

open scoped UpperHalfPlane

namespace MathlibExt.NumberTheory.SingularModulus

/-- **Modular $j$-function.** For $\tau$ in the upper half-plane $\mathbb{H}$,
$$j(\tau) = \frac{E_4(\tau)^3}{\Delta(\tau)},$$
where $E_4$ is the normalized Eisenstein series of weight $4$ (constant term $1$) and
$\Delta = \eta^{24}$ is the modular discriminant, with $q$-expansion
$q \prod_{n \ge 1} (1 - q^n)^{24}$. This is the usual normalization
$j(\tau) = q^{-1} + 744 + 196884\,q + \cdots$, $q = e^{2\pi i \tau}$, with $j(i) = 1728$. -/
@[expose] public noncomputable def jFunction (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

/-- **Imaginary quadratic order of discriminant $\Delta$.** For an integer $\Delta < 0$ with
$\Delta \equiv 0, 1 \pmod 4$, $\mathcal{O}_\Delta$ is the subring
$$\mathcal{O}_\Delta = \mathbb{Z}\Bigl[\tfrac{\Delta + \sqrt{\Delta}}{2}\Bigr] \subset \mathbb{C},
\qquad \sqrt{\Delta} = i\sqrt{|\Delta|}.$$
It is the unique order of discriminant $\Delta$ in the imaginary quadratic field
$\mathbb{Q}(\sqrt{\Delta})$, and its generator is a root of
$X^2 - \Delta X + (\Delta^2 - \Delta)/4$. -/
@[expose] public noncomputable def imagQuadOrder (Δ : ℤ) : Subalgebra ℤ ℂ :=
  Algebra.adjoin ℤ {((Δ : ℂ) + Complex.I * (Real.sqrt (-(Δ : ℝ)) : ℂ)) / 2}

/-- **Class number of discriminant $\Delta$.** $h(\Delta)$ is the order of the class group of the
imaginary quadratic order $\mathcal{O}_\Delta$ of discriminant $\Delta$: invertible (equivalently,
proper) fractional $\mathcal{O}_\Delta$-ideals modulo principal ones. It equals the number of
$\mathrm{SL}_2(\mathbb{Z})$-classes of primitive positive definite binary quadratic forms of
discriminant $\Delta$. -/
@[expose] public noncomputable def classNumber (Δ : ℤ) : ℕ :=
  Nat.card (ClassGroup (imagQuadOrder Δ))

/-- **Degree of a singular modulus.** Let $\tau \in \mathbb{H}$ be imaginary quadratic, with
primitive quadratic equation $a\tau^2 + b\tau + c = 0$, where $a, b, c \in \mathbb{Z}$ and
$\gcd(a, b, c) = 1$, and let $\Delta = b^2 - 4ac$ be the discriminant of the singular modulus
$j(\tau)$. Then
$$[\mathbb{Q}(j(\tau)) : \mathbb{Q}] = h(\Delta),$$
the class number of the imaginary quadratic order of discriminant $\Delta$. In particular $j(\tau)$
is algebraic.

Since $\tau$ is not real, the equation is genuinely quadratic, $\Delta < 0$ and
$\Delta \equiv 0, 1 \pmod 4$.

Source: Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in
$\mathbb{C}^n$*, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641,
[§2·1, pp. 612–613](https://doi.org/10.1017/S0305004125101825): the discriminant of a singular
modulus is defined on p. 612, and the degree formula is stated on p. 613. -/
public theorem_wanted finrank_adjoin_jFunction_eq_classNumber (τ : ℍ) (a b c : ℤ)
    (hgcd : Int.gcd (Int.gcd a b) c = 1)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + (c : ℂ) = 0) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {jFunction τ}) = classNumber (b ^ 2 - 4 * a * c)

end MathlibExt.NumberTheory.SingularModulus
