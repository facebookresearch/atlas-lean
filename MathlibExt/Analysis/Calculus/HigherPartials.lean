/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Higher partial derivatives

This file relates coordinate partial derivatives to Fréchet derivatives and proves that mixed
second partial derivatives of a twice continuously differentiable real function commute.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Partial derivative along a coordinate axis.** For $f : \mathbb{R}^n \to \mathbb{R}$ and a
coordinate index $i$, let $e_i$ be the $i$-th standard basis vector. The partial derivative
$\partial_i f : \mathbb{R}^n \to \mathbb{R}$ sends $x$ to the derivative at $t = 0$ of
$t \mapsto f(x + t e_i)$, taken to be $0$ when this function is not differentiable at $0$.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entries `partial derivatives` and
`k-th order partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9;
stable ref https://en.wikipedia.org/wiki/Partial_derivative. -/
noncomputable def partialDeriv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    (Fin n → ℝ) → ℝ :=
  fun x => deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0

/-- **Partial derivative as the derivative of a coordinate slice.** For
$f : \mathbb{R}^n \to \mathbb{R}$, a coordinate index $i$ and a point $x \in \mathbb{R}^n$, let
$e_i$ be the $i$-th standard basis vector. The partial derivative of $f$ along the $i$-th
coordinate axis at $x$ equals the derivative at $t = 0$ of the one-variable function
$t \mapsto f(x + t e_i)$, taken to be $0$ when that function is not differentiable at $0$.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9. -/
theorem partialDeriv_spec {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) :
    partialDeriv f i x =
      deriv (fun t : ℝ => f (x + t • Pi.single i (1 : ℝ))) 0 := rfl

private theorem partialDeriv_hasDerivAt_axis {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => x + t • Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) 0 := by
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (Pi.single i (1 : ℝ))).const_add x

/-- **Partial derivative as a Fréchet derivative.** Let $f : \mathbb{R}^n \to \mathbb{R}$ be
differentiable at a point $x$, and let $e_i$ be the $i$-th standard basis vector of
$\mathbb{R}^n$. Then the partial derivative of $f$ along the $i$-th coordinate axis at $x$ equals
$Df(x)\,e_i$, the Fréchet derivative of $f$ at $x$ applied to $e_i$.

Proves `Wanted` entry `partialDeriv_eq_fderiv_apply`.

The proof differentiates $f$ along the line $t \mapsto x + t e_i$ by the chain rule.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
-/
theorem partialDeriv_eq_fderiv_apply {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hf : DifferentiableAt ℝ f x) :
    partialDeriv f i x = fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x)
      (x + (0 : ℝ) • Pi.single i (1 : ℝ)) := by
    simpa using hf.hasFDerivAt
  simpa only [partialDeriv, Function.comp_def] using
    (hf'.comp_hasDerivAt 0 (partialDeriv_hasDerivAt_axis i x)).deriv

/-- **Partial derivative function of a differentiable function.** Let
$f : \mathbb{R}^n \to \mathbb{R}$ be differentiable and let $e_i$ be the $i$-th standard basis
vector of $\mathbb{R}^n$. Then the partial derivative $\partial_i f$ of $f$ along the $i$-th
coordinate axis is the function $x \mapsto Df(x)\,e_i$, where $Df(x)$ is the Fréchet derivative
of $f$ at $x$. -/
theorem partialDeriv_eq_fderiv_apply_of_differentiable {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (hf : Differentiable ℝ f) :
    partialDeriv f i = fun x => fderiv ℝ f x (Pi.single i (1 : ℝ)) := by
  funext x
  exact partialDeriv_eq_fderiv_apply f i x (hf x)

private theorem partialDeriv_fderiv_apply_differentiable {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (i : Fin n) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fun x => fderiv ℝ f x (Pi.single i (1 : ℝ))) := by
  apply Differentiable.clm_apply
  · exact (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  · exact differentiable_const _

private theorem partialDeriv_fderiv_apply_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i j : Fin n) (x : Fin n → ℝ) (hf : ContDiff ℝ 2 f) :
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))) x
        (Pi.single j (1 : ℝ)) =
      fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have hderiv :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).hasFDerivAt.comp
      x hfd.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using
      congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ))) hderiv

/-- **Mixed partial derivatives via the second Fréchet derivative.** Let
$f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable, write $e_k$ for the $k$-th
standard basis vector of $\mathbb{R}^n$ and $\partial_k g$ for the partial derivative of a
function $g$ along the $k$-th coordinate axis, and let $Df$ be the Fréchet derivative of $f$,
a map from $\mathbb{R}^n$ to the linear maps $\mathbb{R}^n \to \mathbb{R}$. Then for all coordinate
indices $i, j$ and every $x \in \mathbb{R}^n$,
$\partial_j (\partial_i f)(x) = \big(D(Df)(x)\,e_j\big)\,e_i$, where $D(Df)(x)$ is the Fréchet
derivative of $Df$ at $x$. -/
theorem partialDeriv_partialDeriv_eq_fderiv_fderiv {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (i j : Fin n) (x : Fin n → ℝ) (hf : ContDiff ℝ 2 f) :
    partialDeriv (partialDeriv f i) j x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) := by
  calc
    partialDeriv (partialDeriv f i) j x =
        partialDeriv (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))) j x := by
      rw [partialDeriv_eq_fderiv_apply_of_differentiable f i
        (hf.differentiable (by norm_num))]
    _ = fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))) x
        (Pi.single j (1 : ℝ)) :=
      partialDeriv_eq_fderiv_apply _ j x (partialDeriv_fderiv_apply_differentiable f i hf x)
    _ = fderiv ℝ (fderiv ℝ f) x (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ)) :=
      partialDeriv_fderiv_apply_eq f i j x hf

/-- **Symmetry of mixed partial derivatives (Clairaut's theorem).** For a function
$g : \mathbb{R}^n \to \mathbb{R}$, write $\partial_i g$ for its partial derivative along the
$i$-th coordinate axis. If $f : \mathbb{R}^n \to \mathbb{R}$ is twice continuously
differentiable, then for all coordinate indices $i, j$ and every point $x \in \mathbb{R}^n$,
$\partial_j (\partial_i f)(x) = \partial_i (\partial_j f)(x)$.

Proves `Wanted` entry `iterated_partialDeriv_commute`.

The proof writes both mixed partials as values of the second Fréchet derivative of $f$ at $x$
and applies Schwarz's theorem on the symmetry of second derivatives.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential calculus`, entry `k-th order partial derivatives` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.41 (pp. 235–236).
-/
theorem iterated_partialDeriv_commute {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i j : Fin n) (x : Fin n → ℝ) (hf : ContDiff ℝ 2 f) :
    partialDeriv (partialDeriv f i) j x =
      partialDeriv (partialDeriv f j) i x := by
  rw [partialDeriv_partialDeriv_eq_fderiv_fderiv f i j x hf,
    partialDeriv_partialDeriv_eq_fderiv_fderiv f j i x hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

end MetaMathlibExt
