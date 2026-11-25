/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.Combinatorics.Enumerative.NarayanaNumber

/-!
# Narayana polynomials with zero constant term

This module extends the Narayana-number API with the polynomial normalization
used by the cited Journal of Integer Sequences sources.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Narayana polynomial coefficients.** The Narayana polynomial coefficients are the natural
numbers $a(n, k)$, for natural numbers $n$ and $k$, given by $a(0, 0) = 1$, $a(0, k) = 0$ for
$k \ge 1$, $a(n, 0) = 0$ for $n \ge 1$, and $a(n, k) = N(n, k)$ for $n, k \ge 1$, where $N(n, k)$
is the Narayana number. So row zero is $1$ and every positive row has zero constant term.

Source: concept `jis_sem_06bee1249c32868dc6d7f8d6`; source statements
`jis_6e879284923110cb216e6b7f`, `jis_fe161627e1c6dd385c4aac22`,
`jis_dc822bf3838116b320b91d53`, and `jis_8759141f567e62dd523678c2`. -/
def narayanaPolynomialCoeff : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => narayana ⟨n + 1, Nat.succ_pos n⟩ ⟨k + 1, Nat.succ_pos k⟩

/-- **Narayana polynomial coefficients at positive indices.** For all natural numbers $n$ and
$k$, the Narayana polynomial coefficient in row $n + 1$ and degree $k + 1$ equals the Narayana
number $N(n + 1, k + 1)$.

This holds by definition. -/
theorem narayanaPolynomialCoeff_succ_succ (n k : ℕ) :
    narayanaPolynomialCoeff (n + 1) (k + 1) =
      narayana ⟨n + 1, Nat.succ_pos n⟩ ⟨k + 1, Nat.succ_pos k⟩ :=
  rfl

/-- **Narayana polynomials.** For a semiring $R$ and a natural number $n$, the $n$-th Narayana
polynomial is
$$N_n(X) = \sum_{k=0}^{n} a(n, k)\, X^k \in R[X],$$
where $a(n, k)$ is the Narayana polynomial coefficient, taken in $R$. Since $a(0, 0) = 1$ and,
for $n \ge 1$, $a(n, 0) = 0$ and $a(n, k)$ is the Narayana number $N(n, k)$ for $k \ge 1$, the
first polynomials are $N_0 = 1$, $N_1 = X$, $N_2 = X^2 + X$ and $N_3 = X^3 + 3X^2 + X$.

Source: concept `jis_sem_06bee1249c32868dc6d7f8d6`. -/
noncomputable def narayanaPolynomial (R : Type*) [Semiring R] (n : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (narayanaPolynomialCoeff n k : R) * Polynomial.X ^ k

end

end MetaMathlibExt
