/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Partial zeta functions of an imaginary quadratic field as Epstein zeta functions
-/

open scoped nonZeroDivisors
open NumberField

namespace MetaMathlibExt

/-- Let $K$ be a quadratic number field of discriminant $D < 0$, embedded in $\mathbb{C}$,
and let $w$ be its number of roots of unity. For every ideal class $A$ there is a fractional
ideal $\mathfrak{b}$ in $A^{-1}$ whose image is $\mathbb{Z} + \mathbb{Z}z$, with
$\operatorname{Im} z > 0$. Every such representative satisfies
$2\operatorname{Im} z = N(\mathfrak{b})\sqrt{|D|}$, where $N$ is the absolute ideal norm.
For $\operatorname{Re} s > 1$, the partial zeta series with terms $N(\mathfrak{a})^{-s}$
over nonzero integral ideals in $A$ and the Epstein series over nonzero integer pairs are
summable and satisfy

$$\zeta_K(s,A)=\frac{1}{w}\left(\frac{2}{\sqrt{|D|}}\right)^s Z(z,s),\qquad
Z(z,s)=\sum_{(m,n)\ne(0,0)}\frac{(\operatorname{Im}z)^s}{|m+nz|^{2s}}.$$

In the same half-plane, the Dedekind zeta function is the sum of the partial zeta functions,
or equivalently the same prefactor times the sum of the Epstein zeta functions for any choice
of these representatives.

Source: C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan,
TIFR Lectures on Mathematics 23, Chapter 2, §1, pp. 64 and 67.
<https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf> -/
public theorem_wanted partialZeta_eq_epsteinZeta {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hD : discr K < 0) (σ : K →+* ℂ) :
    let C := ClassGroup (𝓞 K)
    let B := FractionalIdeal (𝓞 K)⁰ K
    let IsRep := fun (A : C) (b : Bˣ) (z : ℂ) ↦
      ClassGroup.mk K b = A⁻¹ ∧ 0 < z.im ∧
        (((b : B) : Submodule (𝓞 K) K).restrictScalars ℤ).map σ.toIntAlgHom.toLinearMap =
          Submodule.span ℤ ({1, z} : Set ℂ)
    let d := Real.sqrt |(discr K : ℝ)|
    let factor := fun (s : ℂ) ↦
      (1 / (Units.torsionOrder K : ℂ)) * ((2 / d : ℝ) : ℂ) ^ s
    let idealTerm := fun (A : C) (s : ℂ) (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = A}) ↦
      (Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℂ) ^ (-s)
    let epsteinTerm := fun (z s : ℂ) (p : {p : ℤ × ℤ // p ≠ (0, 0)}) ↦
      (z.im : ℂ) ^ s / (‖(p.1.1 : ℂ) + (p.1.2 : ℂ) * z‖ : ℂ) ^ (2 * s)
    let partialZeta := fun (A : C) (s : ℂ) ↦ ∑' I, idealTerm A s I
    let epsteinZeta := fun (z s : ℂ) ↦ ∑' p, epsteinTerm z s p
    (∀ A, ∃ b z, IsRep A b z) ∧
    (∀ A b z, IsRep A b z →
      2 * z.im = (FractionalIdeal.absNorm (b : B) : ℝ) * d ∧
      ∀ s, 1 < s.re →
        Summable (epsteinTerm z s) ∧ partialZeta A s = factor s * epsteinZeta z s) ∧
    ∀ s, 1 < s.re →
      (∀ A, Summable (idealTerm A s)) ∧
      dedekindZeta K s = (∑ A, partialZeta A s) ∧
      ∀ (b : C → Bˣ) (z : C → ℂ), (∀ A, IsRep A (b A) (z A)) →
        dedekindZeta K s = factor s * ∑ A, epsteinZeta (z A) s

end MetaMathlibExt
