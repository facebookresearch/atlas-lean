/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Ordinary Riordan Pascal-like matrix

Provenance: concept `jis_sem_d14a1d74e61f27c561413829`; source statements
`jis_55826aed9bbc43db2e540fc8`, `jis_a1500757725c00536c86ba35`,
`jis_ac99ac2ae8aedbaafe1c53e3`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ordinary Riordan Pascal-like triangle.** For natural numbers $n, k$ and an integer $r$,
the entry $T(n, k; r)$ is the integer
$$T(n, k; r) = \sum_{j=0}^{k} \binom{k}{j} \binom{\max(n - j, 0)}{k} r^j.$$

This is the entry formula of the ordinary Riordan array
$\bigl(1/(1 - x),\ x(1 + rx)/(1 - x)\bigr)$, denoted $T(r)$. Terms with $j > n - k$ vanish,
because then $\max(n - j, 0) < k$. For $r = 0$ this is Pascal's triangle and for $r = 1$ the
Delannoy triangle. -/
public def ordinaryRiordanPascalLikeMatrix (n k : ℕ) (r : ℤ) : ℤ :=
  Finset.sum (Finset.range (k + 1)) fun j =>
    (k.choose j : ℤ) * ((n - j).choose k : ℤ) * r ^ j

/-- **Entry formula for the ordinary Riordan Pascal-like triangle.** For natural numbers
$n, k$ and an integer $r$, the ordinary Riordan Pascal-like matrix entry $T(n, k; r)$ equals
$\sum_{j=0}^{k} \binom{k}{j} \binom{\max(n - j, 0)}{k} r^j$; this holds by definition. -/
public theorem ordinaryRiordanPascalLikeMatrix_def (n k : ℕ) (r : ℤ) :
    ordinaryRiordanPascalLikeMatrix n k r =
      Finset.sum (Finset.range (k + 1)) fun j =>
        (k.choose j : ℤ) * ((n - j).choose k : ℤ) * r ^ j :=
  rfl

end

end MetaMathlibExt
