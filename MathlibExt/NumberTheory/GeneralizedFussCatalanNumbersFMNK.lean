/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic

/-!
# Generalized Fuss–Catalan numbers

This file defines the generalized Fuss–Catalan numbers, also called Raney numbers.

Provenance: JIS semantic concept `jis_sem_69c4f50c7aa0eee05d643c54`, statement
`jis_059ca809c2428bd341da0fee`, from
<https://cs.uwaterloo.ca/journals/JIS/VOL21/He/he61.tex>, SHA-256
`c73d8bdaba1725e18630db49af924a0cb5433b6b00878e556c2c9fdb7e2ae320`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Fuss–Catalan number.** For natural numbers $m$, $n$ and $k$, the generalized
Fuss–Catalan number $F_m(n, k)$ is the quotient of $k \binom{mn + k}{n}$ by $mn + k$ in
natural-number division, rounded down, with division by $0$ giving $0$.

The source considers $m \ge 2$ and $n, k \ge 1$. The definition is totalized over natural numbers.
-/
def generalizedFussCatalanNumber (m n k : ℕ) : ℕ :=
  k * Nat.choose (m * n + k) n / (m * n + k)

/-- **Formula for the generalized Fuss–Catalan number.** For all natural numbers $m$, $n$ and $k$,
the generalized Fuss–Catalan number $F_m(n, k)$ equals the quotient of $k \binom{mn + k}{n}$ by
$mn + k$ in natural-number division, rounded down, with division by $0$ giving $0$. -/
theorem generalizedFussCatalanNumber_eq (m n k : ℕ) :
    generalizedFussCatalanNumber m n k =
      k * Nat.choose (m * n + k) n / (m * n + k) :=
  rfl

/-- **Generalized Fuss–Catalan numbers at $n = 1$.** For all natural numbers $m$ and $k$, the
generalized Fuss–Catalan number $F_m(1, k)$ equals $k$.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL21/He/he61.tex>, case (c) of the source theorem.
-/
theorem generalizedFussCatalanNumber_one (m k : ℕ) :
    generalizedFussCatalanNumber m 1 k = k := by
  unfold generalizedFussCatalanNumber
  have hmk : m * 1 + k = m + k := by omega
  rw [hmk, Nat.choose_one_right]
  by_cases h : m + k = 0
  · have hk : k = 0 := by omega
    simp [hk]
  · have hpos : 0 < m + k := by omega
    exact Nat.mul_div_cancel k hpos

end

end MetaMathlibExt
