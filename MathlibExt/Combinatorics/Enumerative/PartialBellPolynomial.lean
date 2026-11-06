/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Pi

/-!
# Partial Bell polynomials

The definition follows Miloud Mihoubi, *Some Congruences for the Partial Bell
Polynomials*, Journal of Integer Sequences 12 (2009), Article 09.4.1.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose]
public section

/-- **Partial Bell polynomial.** Let $R$ be a commutative semiring, let $n, k \in \mathbb{N}$
and let $x_1, x_2, \dots$ be a sequence in $R$. The partial Bell polynomial $B_{n,k}(x)$ is
the sum, over all tuples $(m_1, \dots, m_{n+1})$ of natural numbers with
$\sum_j j\, m_j = n$ and $\sum_j m_j = k$, of
$$\frac{n!}{\prod_j m_j!\,(j!)^{m_j}} \prod_j x_j^{m_j},$$
where the quotient is a natural number, mapped into $R$.

Source: Mihoubi, *Some Congruences for the Partial Bell Polynomials*, J. Integer Seq. 12
(2009), Article 09.4.1; concept `jis_sem_a0ee8baeec8938655a1c8c9a`.
-/
def partialBellPolynomial {R : Type*} [CommSemiring R]
    (n k : ℕ) (x : ℕ → R) : R :=
  ∑ m ∈ (Fintype.piFinset fun _ : Fin (n + 1) => Finset.range (n + 1)).filter
      (fun m => (∑ i, (i.val + 1) * m i = n) ∧ ∑ i, m i = k),
    (↑(n.factorial / ∏ i, (m i).factorial * (i.val + 1).factorial ^ m i) : R) *
      ∏ i, x (i.val + 1) ^ m i

end

end MetaMathlibExt
