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
public import WantedExt.NumberTheory.QuadraticForms.KroneckerFormSumsWanted

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

/-- **Degree of a singular modulus.** Let $\tau \in \mathbb{H}$ be imaginary quadratic, with
primitive quadratic equation $a\tau^2 + b\tau + c = 0$, where $a, b, c \in \mathbb{Z}$ and
$\gcd(a, b, c) = 1$, and let $\Delta = b^2 - 4ac$ be the discriminant of the singular modulus
$j(\tau)$. Then
$$[\mathbb{Q}(j(\tau)) : \mathbb{Q}] = h(\Delta),$$
the class number of discriminant $\Delta$. In particular $j(\tau)$ is algebraic.

Since $\tau$ is not real, the equation is genuinely quadratic, $\Delta < 0$ and
$\Delta \equiv 0, 1 \pmod 4$. Fowler defines $h(\Delta)$ as the class number of the imaginary
quadratic order of discriminant $\Delta$. It is stated here as `MetaMathlibExt.gaussClassNumber`,
the number of reduced primitive positive definite binary quadratic forms of discriminant
$\Delta$: every class of primitive positive definite forms contains exactly one reduced form, and
these form classes correspond to the proper ideal classes of the order of discriminant $\Delta$
(D. A. Cox, *Primes of the Form $x^2 + ny^2$*, Wiley, §§2 and 7).

Source: Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in
$\mathbb{C}^n$*, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641,
[§2·1, pp. 612–613](https://doi.org/10.1017/S0305004125101825): the discriminant of a singular
modulus is defined on p. 612, and the degree formula is stated on p. 613. -/
public theorem_wanted finrank_adjoin_jFunction_eq_gaussClassNumber (τ : ℍ) (a b c : ℤ)
    (hgcd : Int.gcd (Int.gcd a b) c = 1)
    (hτ : (a : ℂ) * (τ : ℂ) ^ 2 + (b : ℂ) * (τ : ℂ) + (c : ℂ) = 0) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {jFunction τ}) =
      MetaMathlibExt.gaussClassNumber (b ^ 2 - 4 * a * c)

end MathlibExt.NumberTheory.SingularModulus
