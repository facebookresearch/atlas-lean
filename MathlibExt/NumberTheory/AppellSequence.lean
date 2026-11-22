/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative

namespace MetaMathlibExt

@[expose] public section

/-- **Appell sequence.** Let $R$ be a field of characteristic zero. A sequence of polynomials
$(p_n)_{n \ge 0}$ over $R$ is an Appell sequence when, for every $n$, the polynomial $p_n$ has
degree exactly $n$ (in particular $p_n \ne 0$) and the formal derivative of $p_{n+1}$ equals
$(n + 1)\, p_n$.

Source: Provenance: jis_sem_73bec790e3c604ecfcaea4c0, jis_ec459310b2112700a98743da,
jis_f46aabe68ad72f828ff4cf84. -/
def IsAppellSequence {R : Type*} [Field R] [CharZero R] (p : ℕ → Polynomial R) : Prop :=
  (∀ n, Polynomial.degree (p n) = ↑n) ∧
    ∀ n, Polynomial.derivative (p (n + 1)) = Polynomial.C ((n + 1 : ℕ) : R) * p n

end

end MetaMathlibExt
