/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.JacobiStirlingFirstKind

namespace MetaMathlibExt

@[expose] public section

/-- **Generating polynomial of the Legendre–Stirling numbers of the first kind.** For a natural
number $n$, this is the polynomial $\prod_{i=0}^{n-1} \bigl(X - i(i+1)\bigr)$ with integer
coefficients; for $n = 0$ it is the empty product $1$.

Source: Concept `jis_sem_f66a64ccd0402d409b050315`, source equation `e:JacobiStirling1` /
`e:LeStirling` (statements `jis_01122ed9cc65cc42cecf4da1`,
`jis_073a5750ee8a25ebbba42d0c`). -/
noncomputable def legendreStirlingFirstPoly (n : ℕ) : Polynomial ℤ :=
  jacobiStirlingFirstPoly n (1 : ℤ)

/-- **Legendre–Stirling numbers of the first kind.** For natural numbers $n$ and $k$, the
Legendre–Stirling number of the first kind $J(n, k; 1)$ is the coefficient of $x^k$ in the
integer polynomial $\prod_{i=0}^{n-1} \bigl(x - i(i+1)\bigr)$, which is $1$ when $n = 0$. These
are the Jacobi–Stirling numbers of the first kind $J(n, k; \zeta)$ at $\zeta = 1$.

Source: Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
noncomputable def legendreStirlingFirst (n k : ℕ) : ℤ :=
  jacobiStirlingFirst n k (1 : ℤ)

/-- **Initial row of the Legendre–Stirling numbers of the first kind.** For every natural number
$k$, the Legendre–Stirling number of the first kind $J(0, k; 1)$ equals $1$ if $k = 0$ and $0$
otherwise.

Source: Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_zero (k : ℕ) :
    legendreStirlingFirst 0 k = if k = 0 then 1 else 0 := by
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_initial_row (R := ℤ) k (1 : ℤ)

/-- **Recurrence for the Legendre–Stirling numbers of the first kind.** For all natural numbers
$n$ and $k$, the Legendre–Stirling numbers of the first kind satisfy
$J(n + 1, k + 1; 1) = J(n, k; 1) - n(n + 1) \, J(n, k + 1; 1)$.

Source: Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_succ (n k : ℕ) :
    legendreStirlingFirst (n + 1) (k + 1) =
      legendreStirlingFirst n k -
        (n : ℤ) * ((n + 1 : ℕ) : ℤ) * legendreStirlingFirst n (k + 1) := by
  simpa [legendreStirlingFirst, Nat.cast_add, Nat.cast_one] using
    jacobiStirlingFirst_recurrence (R := ℤ) n k (1 : ℤ)

/-- **Legendre–Stirling numbers of the first kind vanish above the diagonal.** For all natural
numbers $n < k$, the Legendre–Stirling number of the first kind $J(n, k; 1)$ is $0$.

Source: Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_eq_zero_of_lt :
    ∀ (n k : ℕ), n < k → legendreStirlingFirst n k = 0 := by
  intro n k h
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_support (R := ℤ) n k (1 : ℤ) h

/-- **Diagonal Legendre–Stirling numbers of the first kind.** For every natural number $n$, the
Legendre–Stirling number of the first kind $J(n, n; 1)$ equals $1$.

Source: Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`). -/
theorem legendreStirlingFirst_diag : ∀ (n : ℕ), legendreStirlingFirst n n = 1 := by
  intro n
  simpa [legendreStirlingFirst] using
    jacobiStirlingFirst_diagonal (R := ℤ) n (1 : ℤ)

end

end MetaMathlibExt
