/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Coefficient of the formal-sequence recurrence.** For elements $a$, $b$, $c$ of a field $F$,
the coefficient of the formal-sequence recurrence determined by the seed triplet $(a, b, c)$ is
$\alpha = \frac{ab + bc + ca}{b^2} - 1$.

Division by zero is read as $0$, so $\alpha = -1$ when $b = 0$.

Source: statement `jis_50a05fd3a5b6b4a1865a61bb`, concept `jis_sem_1ce947826a0dceb6fde5b7f2`, in
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`;
raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`. -/
public def formalAlpha {F : Type*} [Field F] (a b c : F) : F :=
  (a * b + b * c + c * a) / b ^ 2 - 1

/-- **Constant term of the formal-sequence recurrence.** For elements $a$, $b$, $c$ of a field
$F$, the constant term of the formal-sequence recurrence determined by the seed triplet
$(a, b, c)$ is $\beta = \frac{b^2 - ac}{b}$.

Division by zero is read as $0$, so $\beta = 0$ when $b = 0$.

Source: statement `jis_50a05fd3a5b6b4a1865a61bb`, concept `jis_sem_1ce947826a0dceb6fde5b7f2`, in
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`;
raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`. -/
public def formalBeta {F : Type*} [Field F] (a b c : F) : F :=
  (b ^ 2 - a * c) / b

/-- **Formal sequence from a seed triplet.** Let $F$ be a field and $a, b, c \in F$. A sequence
$u : \mathbb{N} \to F$ is a formal sequence with seed triplet $(a, b, c)$ when $b \neq 0$,
$u_0 = a$, $u_1 = b$, $u_2 = c$, and for every $n \ge 0$
$$u_{n+2} = \alpha u_{n+1} - u_n + \beta,$$
where $\alpha = \frac{ab + bc + ca}{b^2} - 1$ and $\beta = \frac{b^2 - ac}{b}$ are the
coefficient and the constant term of the formal-sequence recurrence.

Source: statement `jis_50a05fd3a5b6b4a1865a61bb`, concept `jis_sem_1ce947826a0dceb6fde5b7f2`, in
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`;
raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`. -/
public def IsFormalSequence {F : Type*} [Field F]
    (u : ℕ → F) (a b c : F) : Prop :=
  b ≠ 0 ∧ u 0 = a ∧ u 1 = b ∧ u 2 = c ∧
    ∀ n : ℕ, u (n + 2) =
      formalAlpha a b c * u (n + 1) - u n + formalBeta a b c

end MetaMathlibExt
