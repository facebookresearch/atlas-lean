/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

/-!
# Jacobi theta product

This file defines the product-side Jacobi theta function

`j(x; q) = (x; q)∞ (q / x; q)∞ (q; q)∞`

in terms of `MetaMathlibExt.QPochhammer.qPochhammerInf`.

The definition threads the convergence evidence `‖q‖ < 1` required by
`qPochhammerInf`. In particular, division by zero uses the
totalized field operation on `ℂ`. Analytic applications should additionally
impose `x ≠ 0`; no convergence or triple-product identity is asserted here.

## References

* [M. Dospolova, E. Kochetkova, and E. T. Mortenson, *A new Andrews--Crandall-type
  identity and the number of integer solutions to x² + 2y² + 2z² = n*][dospolova2023]
* [E. T. Mortenson, *Short proofs of Ramanujan-like identities for the eighth order mock
  theta function V₀(q)*][mortenson2023]
* [N. Borozenets and E. T. Mortenson, *On string functions of the generalized parafermionic
  theories, mock theta functions, and false theta functions*][borozenets2024]

[dospolova2023]: https://arxiv.org/abs/2307.05244
[mortenson2023]: https://arxiv.org/abs/2308.16144
[borozenets2024]: https://arxiv.org/abs/2409.14834
-/

@[expose] public section

namespace MetaMathlibExt.QPochhammer

/-- **Jacobi theta function, product form.** For complex numbers $x$ and $q$ with $|q| < 1$,

$$j(x; q) = (x; q)_\infty \, (q/x; q)_\infty \, (q; q)_\infty,$$

where $(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ is the infinite $q$-Pochhammer symbol.
Division by zero is read as $q/0 = 0$, so $j(0; q) = (q; q)_\infty$. -/
noncomputable def jacobiThetaProduct (x q : ℂ) (hq : ‖q‖ < 1) : ℂ :=
  qPochhammerInf x q hq * qPochhammerInf (q / x) q hq * qPochhammerInf q q hq

/-- **Symmetry of the Jacobi theta product under $x \mapsto q/x$.** Write
$(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ for the infinite $q$-Pochhammer symbol and
$j(x; q) = (x; q)_\infty \, (q/x; q)_\infty \, (q; q)_\infty$ for the product-form Jacobi theta
function. For all complex numbers $x$ and $q$ with $0 < |q| < 1$, $j(q/x; q) = j(x; q)$.
This includes $x = 0$, where $q/0$ is read as $0$. -/
theorem jacobiThetaProduct_symm (x q : ℂ) (hq : ‖q‖ < 1) (h0 : q ≠ 0) :
    jacobiThetaProduct (q / x) q hq = jacobiThetaProduct x q hq := by
  unfold jacobiThetaProduct
  rw [div_div_cancel₀ h0, mul_comm (qPochhammerInf (q / x) q hq) (qPochhammerInf x q hq)]

/-- **Jacobi theta product with vanishing first argument.** Write
$(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ for the infinite $q$-Pochhammer symbol and
$j(x; q) = (x; q)_\infty \, (q/x; q)_\infty \, (q; q)_\infty$ for the product-form Jacobi theta
function. For every complex number $q$ with $|q| < 1$, $j(0; q) = (q; q)_\infty$.
Here $q/0$ is read as $0$, so the first two factors of $j(0; q)$ both equal $(0; q)_\infty = 1$. -/
@[simp]
theorem jacobiThetaProduct_zero_left (q : ℂ) (hq : ‖q‖ < 1) :
    jacobiThetaProduct 0 q hq = qPochhammerInf q q hq := by
  simp [jacobiThetaProduct]

/-- **Jacobi theta product at nome zero.** Write $(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$
for the infinite $q$-Pochhammer symbol and
$j(x; q) = (x; q)_\infty \, (q/x; q)_\infty \, (q; q)_\infty$ for the product-form Jacobi theta
function, where $|q| < 1$. For every complex number $x$, $j(x; 0) = (x; 0)_\infty$: since
$0/x = 0$ (also for $x = 0$, reading $0/0$ as $0$), the last two factors of $j(x; 0)$ both equal
$(0; 0)_\infty = 1$. -/
@[simp]
theorem jacobiThetaProduct_zero_right (x : ℂ) :
    jacobiThetaProduct x 0 (by simp) = qPochhammerInf x 0 (by simp) := by
  simp [jacobiThetaProduct]

end MetaMathlibExt.QPochhammer
