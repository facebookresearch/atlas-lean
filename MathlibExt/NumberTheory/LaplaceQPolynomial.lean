/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative

namespace MetaMathlibExt

variable {R : Type*} [Semiring R]

@[expose] public section

/-- **Laplace Q-polynomial families.** Let $R$ be a semiring and let $(P_k)_{k \ge 0}$ and
$(Q_k)_{k \ge 0}$ be sequences of polynomials in $R[X]$. The sequence $(Q_k)$ is a Laplace
Q-polynomial family companion to $(P_k)$ when $Q_0 = 1$ and, for every natural number $k \ge 1$,
$$Q_k = P_k + Q_{k-1}' \quad \text{and} \quad Q_{k+1} = X Q_k + (k + 1) Q_{k-1},$$
where $Q_{k-1}'$ denotes the formal derivative of $Q_{k-1}$.

Source: Parent concept jis_term_175f40eafad3fd8ef053fd1c, semantic child
jis_sem_ec10d6c739532b64eed644f6, statement jis_aea8ce5c6ff12cefd7773f08,
source SHA-256 1af295f0b6783f5333bea0a3a39b8eed4d23380a65b9a9f7cf5092c3abf14998.
Frozen source https://cs.uwaterloo.ca/journals/JIS/VOL19/Kreinin/kreinin4.tex,
bytes/chars 13284..13748, lines 306..315. -/
public def IsLaplaceQFamily (P Q : ℕ → Polynomial R) : Prop :=
  Q 0 = 1 ∧
    ∀ k : ℕ, 1 ≤ k →
      Q k = P k + Polynomial.derivative (Q (k - 1)) ∧
        Q (k + 1) = Polynomial.X * Q k + (k + 1) • Q (k - 1)

end

end MetaMathlibExt
