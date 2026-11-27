/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

/-!
# Shanks cubic polynomial

This module formalizes the Shanks cubic polynomials (SCPs).
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Shanks cubic polynomial.** For an element $h$ of a ring $R$, the Shanks cubic polynomial is
$$x^3 - h x^2 - (h + 3) x - 1 \in R[x].$$

The source writes this polynomial as $\rho(h, -1, x)$.

Source concept `shanks cubic polynomial` (`jis_sem_d420b3546a20fc62825bd4f4`),
statement `jis_1715bdf9bc6d7be3f67907da` from source `jis_source_86699979507d539990484515`. -/
noncomputable def shanksCubicPolynomial {R : Type*} [Ring R] (h : R) : Polynomial R :=
  Polynomial.X ^ 3 - Polynomial.C h * Polynomial.X ^ 2 -
    Polynomial.C (h + 3) * Polynomial.X - 1

end MetaMathlibExt
