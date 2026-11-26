/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.KJacobsthal
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Catalan's identity for the companion $k$-Jacobsthal numbers

We prove `companionKJacobsthal_catalan`, Catalan's identity for the companion $k$-Jacobsthal
numbers $\mathcal{J}_{k,m}(a, b)$ in terms of the $k$-Jacobsthal numbers $J_{k,m} = U_m(k, -2)$;
the theorem's docstring states the identity. The source states it for positive $k$, $n$ and $r$
and nonnegative $a$ and $b$. The Lean statement also allows $k = 0$, $r = 0$ and $n = r$ and any
integers $a$ and $b$; its hypothesis $r \le n$ makes the lower index $n - r$ exist. The proof
applies the generalized Catalan identity for Horadam sequences,
`horadam_generalized_catalan_identity`, twice: once to the companion sequence and once to it and
its shift.

Statements from Weerayuth Nilsrakoo and Achariya Nilsrakoo, "An Integral Representation of
k-Jacobsthal and k-Jacobsthal-Lucas Numbers", *INTEGERS* 25 (2025), Article A74
(<https://math.colgate.edu/~integers/z74/z74.pdf>).
-/

namespace MetaMathlibExt

@[expose] public section

-- The recurrence of the `k`-Jacobsthal numbers with the parameters unfolded.
private theorem lucasU_kJacobsthal_add_two (k m : ℕ) :
    lucasU (kJacobsthalParams k) (m + 2) =
      (k : ℤ) * lucasU (kJacobsthalParams k) (m + 1) +
        2 * lucasU (kJacobsthalParams k) m := by
  rw [lucasU_add_two]
  change (k : ℤ) * _ - (-2 : ℤ) * _ = _
  ring

/-- **Catalan's identity for the companion $k$-Jacobsthal numbers.** Let $k$ be a natural number,
$a, b$ integers, $\mathcal{J}_{k,m} = \mathcal{J}_{k,m}(a, b)$ the companion $k$-Jacobsthal numbers
and $J_{k,m} = U_m(k, -2)$ the $k$-Jacobsthal numbers. For all natural numbers $r \le n$,
$$
\mathcal{J}_{k,n-r}\,\mathcal{J}_{k,n+r} - \mathcal{J}_{k,n}^2 =
\bigl(a^2 (k^2 + 8) - (2b - ak)^2\bigr)\,(-2)^{n-r-2}\,J_{k,r}^2
$$
in $\mathbb{Q}$, where $(-2)^{n-r-2}$ is an integer power.

With $\Delta_k = \sqrt{k^2 + 8}$, the first factor on the right equals
$(2b - ak + a\Delta_k)(ak - 2b + a\Delta_k)$, the form in which the source states it.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 11 (`integers-2025-A74-thm-11`). -/
public theorem companionKJacobsthal_catalan (k : ℕ) (a b : ℤ) (n r : ℕ) (hrn : r ≤ n) :
    ((companionKJacobsthal k a b (n - r) * companionKJacobsthal k a b (n + r) -
        companionKJacobsthal k a b n ^ 2 : ℤ) : ℚ) =
      ((a ^ 2 * ((k : ℤ) ^ 2 + 8) - (2 * b - a * k) ^ 2 : ℤ) : ℚ) *
        (-2 : ℚ) ^ ((n : ℤ) - r - 2) * (lucasU (kJacobsthalParams k) r : ℚ) ^ 2
    := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have hC := companionKJacobsthal_add_two k a b
  have hU := lucasU_kJacobsthal_add_two k
  have hU0 : lucasU (kJacobsthalParams k) 0 = 0 := by simp [lucasU]
  have hU1 : lucasU (kJacobsthalParams k) 1 = 1 := by simp [lucasU]
  have hC0 : companionKJacobsthal k a b 0 = a := by simp [companionKJacobsthal]
  have hC1 : companionKJacobsthal k a b 1 = b := by simp [companionKJacobsthal]
  -- Catalan's identity at the indices `(j, r, r)`, and the companion against its shift at
  -- `(0, r, 0)`, which evaluates the coefficient `b C(r) - a C(r + 1)`.
  have h1 := horadam_generalized_catalan_identity (k : ℤ) 2 (companionKJacobsthal k a b)
    (companionKJacobsthal k a b) (lucasU (kJacobsthalParams k)) hC hC hU hU0 hU1 j r r
  have h2 := horadam_generalized_catalan_identity (k : ℤ) 2 (companionKJacobsthal k a b)
    (fun m => companionKJacobsthal k a b (m + 1)) (lucasU (kJacobsthalParams k)) hC
    (fun m => hC (m + 1)) hU hU0 hU1 0 r 0
  simp only [zero_add, add_zero, pow_zero, one_mul, hC0, hC1, Nat.reduceAdd,
    companionKJacobsthal_two] at h2
  rw [hC0, hC1, show j + r + r = j + 2 * r by ring] at h1
  have key : 4 * (companionKJacobsthal k a b j * companionKJacobsthal k a b (j + 2 * r) -
      companionKJacobsthal k a b (j + r) ^ 2) =
      (a ^ 2 * ((k : ℤ) ^ 2 + 8) - (2 * b - a * k) ^ 2) * (-2 : ℤ) ^ j *
        lucasU (kJacobsthalParams k) r ^ 2 := by
    linear_combination (-4) * h1 - 4 * (-2 : ℤ) ^ j * lucasU (kJacobsthalParams k) r * h2
  have n1 : r + j - r = j := by omega
  have n2 : r + j + r = j + 2 * r := by omega
  have n3 : r + j = j + r := by omega
  rw [n1, n2, n3]
  have ne : ((j + r : ℕ) : ℤ) - (r : ℤ) - 2 = (j : ℤ) - 2 := by
    rw [Nat.cast_add]
    ring
  rw [ne]
  have hz : (-2 : ℚ) ^ ((j : ℤ) - 2) = (-2 : ℚ) ^ j / 4 := by
    have hne : (-2 : ℚ) ≠ 0 := by norm_num
    have h4 : (-2 : ℚ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    have e : (j : ℤ) - 2 = (j : ℤ) + (-2) := by ring
    rw [e, zpow_add₀ hne, h4, zpow_natCast]
    ring
  rw [hz]
  have keyQ : (4 : ℚ) * ((companionKJacobsthal k a b j *
      companionKJacobsthal k a b (j + 2 * r) - companionKJacobsthal k a b (j + r) ^ 2 : ℤ) : ℚ) =
      ((a ^ 2 * ((k : ℤ) ^ 2 + 8) - (2 * b - a * k) ^ 2 : ℤ) : ℚ) * (-2 : ℚ) ^ j *
        ((lucasU (kJacobsthalParams k) r : ℤ) : ℚ) ^ 2 := by
    exact_mod_cast key
  linear_combination (1 / 4 : ℚ) * keyQ

end

end MetaMathlibExt
