/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.KJacobsthal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Catalan's identity for the companion $k$-Jacobsthal numbers

We prove `companionKJacobsthal_catalan`: for the companion $k$-Jacobsthal numbers
$mathcal{J}_{k,m}(a, b)$ and the $k$-Jacobsthal numbers $J_{k,m} = U_m(k, -2)$,
$mathcal{J}_{k,n-r},mathcal{J}_{k,n+r} - mathcal{J}_{k,n}^2$ equals
$bigl(a^2 (k^2 + 8) - (2b - ak)^2bigr),(-2)^{n-r-2},J_{k,r}^2$ in $mathbb{Q}$
when $r le n$. The proof goes through doubling formulas for the $k$-Jacobsthal numbers,
the expansion of the companion numbers in those, and a simultaneous induction proving
Catalan's identity together with a cross identity.

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

-- Doubling formulas for the `k`-Jacobsthal numbers.
private theorem lucasU_kJacobsthal_double (k r : ℕ) :
    lucasU (kJacobsthalParams k) (2 * r) =
        2 * lucasU (kJacobsthalParams k) r * lucasU (kJacobsthalParams k) (r + 1) -
          (k : ℤ) * lucasU (kJacobsthalParams k) r ^ 2 ∧
      lucasU (kJacobsthalParams k) (2 * r + 1) =
        lucasU (kJacobsthalParams k) (r + 1) ^ 2 +
          2 * lucasU (kJacobsthalParams k) r ^ 2 := by
  induction r with
  | zero => constructor <;> simp [lucasU]
  | succ r ih =>
    obtain ⟨ihe, iho⟩ := ih
    have h1 := lucasU_kJacobsthal_add_two k (2 * r)
    have h2 := lucasU_kJacobsthal_add_two k (2 * r + 1)
    have h3 := lucasU_kJacobsthal_add_two k r
    have e1 : 2 * (r + 1) = 2 * r + 2 := by omega
    have e2 : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
    have e3 : r + 1 + 1 = r + 2 := by omega
    have e4 : (2 * r + 1) + 1 = 2 * r + 2 := by omega
    rw [e4] at h2
    constructor
    · rw [e1, e3]
      linear_combination h1 + (k : ℤ) * iho + 2 * ihe -
        2 * lucasU (kJacobsthalParams k) (r + 1) * h3
    · rw [e2, e3]
      linear_combination h2 + (k : ℤ) * h1 + (2 + (k : ℤ) ^ 2) * iho +
        2 * (k : ℤ) * ihe -
        (lucasU (kJacobsthalParams k) (r + 2) + (k : ℤ) * lucasU (kJacobsthalParams k) (r + 1) +
          2 * lucasU (kJacobsthalParams k) r) * h3

-- The companion numbers as a combination of `k`-Jacobsthal numbers.
private theorem companionKJacobsthal_eq (k : ℕ) (a b : ℤ) (m : ℕ) :
    companionKJacobsthal k a b m =
      a * lucasU (kJacobsthalParams k) (m + 1) +
        (b - a * k) * lucasU (kJacobsthalParams k) m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [companionKJacobsthal, lucasU]
  | one =>
    have e : (1 : ℕ) + 1 = 2 := rfl
    have g1 : companionKJacobsthal k a b 1 = b := rfl
    have u1 : lucasU (kJacobsthalParams k) 1 = 1 := rfl
    rw [e, lucasU_kJacobsthalParams_two, g1, u1]
    ring
  | more m ihm ihm1 =>
    rw [companionKJacobsthal_add_two]
    have hU1 := lucasU_kJacobsthal_add_two k (m + 1)
    have hU2 := lucasU_kJacobsthal_add_two k m
    have e : m + 2 + 1 = (m + 1) + 2 := by omega
    rw [e]
    linear_combination (k : ℤ) * ihm1 + 2 * ihm - a * hU1 - (b - a * k) * hU2

-- Catalan's identity and a cross identity for the `k`-Jacobsthal numbers.
private theorem lucasU_kJacobsthal_catalan_cross (k r j : ℕ) :
    (lucasU (kJacobsthalParams k) j * lucasU (kJacobsthalParams k) (j + 2 * r) -
        lucasU (kJacobsthalParams k) (j + r) ^ 2 =
      -(-2 : ℤ) ^ j * lucasU (kJacobsthalParams k) r ^ 2) ∧
      (lucasU (kJacobsthalParams k) (j + 1) * lucasU (kJacobsthalParams k) (j + 2 * r) +
          lucasU (kJacobsthalParams k) j * lucasU (kJacobsthalParams k) (j + 2 * r + 1) -
          2 * lucasU (kJacobsthalParams k) (j + r) * lucasU (kJacobsthalParams k) (j + r + 1) =
        -(k : ℤ) * (-2 : ℤ) ^ j * lucasU (kJacobsthalParams k) r ^ 2) := by
  have hU0 : lucasU (kJacobsthalParams k) 0 = 0 := rfl
  have hU1 : lucasU (kJacobsthalParams k) 1 = 1 := rfl
  have hU2 := lucasU_kJacobsthalParams_two k
  induction j using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.zero_add]
    constructor
    · rw [hU0, pow_zero]
      ring
    · have hd := (lucasU_kJacobsthal_double k r).1
      rw [hU0, hU1, pow_zero]
      linear_combination hd
  | one =>
    constructor
    · have e1 : 1 + 2 * r = 2 * r + 1 := by omega
      have e2 : 1 + r = r + 1 := by omega
      rw [e1, e2, hU1, pow_one]
      have hd := (lucasU_kJacobsthal_double k r).2
      linear_combination hd
    · have e3 : 1 + 2 * r + 1 = 2 * r + 2 := by omega
      have e1 : 1 + 2 * r = 2 * r + 1 := by omega
      have e4 : 1 + r + 1 = r + 2 := by omega
      have e2 : 1 + r = r + 1 := by omega
      have e5 : (1 : ℕ) + 1 = 2 := rfl
      rw [e3, e1, e4, e2, e5, hU2, hU1, pow_one]
      have hd1 := (lucasU_kJacobsthal_double k r).2
      have hd0 := (lucasU_kJacobsthal_double k (r + 1)).1
      have e6 : 2 * (r + 1) = 2 * r + 2 := by omega
      have e7 : r + 1 + 1 = r + 2 := by omega
      rw [e6, e7] at hd0
      linear_combination (k : ℤ) * hd1 + hd0
  | more j ih0 ih1 =>
    obtain ⟨hF0, hGc0⟩ := ih0
    obtain ⟨hF1, hGc1⟩ := ih1
    have rA := lucasU_kJacobsthal_add_two k j
    have rB := lucasU_kJacobsthal_add_two k (j + 2 * r)
    have rC := lucasU_kJacobsthal_add_two k (j + r)
    have rA' := lucasU_kJacobsthal_add_two k (j + 1)
    have rB' := lucasU_kJacobsthal_add_two k (j + 1 + 2 * r)
    have rC' := lucasU_kJacobsthal_add_two k (j + 1 + r)
    have hq1 : (-2 : ℤ) ^ (j + 1) = (-2 : ℤ) ^ j * -2 := pow_succ _ _
    have hq2 : (-2 : ℤ) ^ (j + 2) = 4 * (-2 : ℤ) ^ j := by
      rw [pow_succ, pow_succ]
      ring
    have hqa : (-2 : ℤ) ^ (j + 2) = (-2 : ℤ) ^ (j + 1) * -2 := pow_succ _ _
    have hF2 : lucasU (kJacobsthalParams k) (j + 2) *
          lucasU (kJacobsthalParams k) (j + 2 + 2 * r) -
          lucasU (kJacobsthalParams k) (j + 2 + r) ^ 2 =
        -(-2 : ℤ) ^ (j + 2) * lucasU (kJacobsthalParams k) r ^ 2 := by
      have eB : j + 2 + 2 * r = j + 2 * r + 2 := by omega
      have eC : j + 2 + r = j + r + 2 := by omega
      have eB1 : j + 1 + 2 * r = j + 2 * r + 1 := by omega
      have eC1 : j + 1 + r = j + r + 1 := by omega
      rw [eB, eC]
      rw [eB1, eC1] at hF1
      linear_combination ((k : ℤ) * lucasU (kJacobsthalParams k) (j + 2 * r + 1) +
          2 * lucasU (kJacobsthalParams k) (j + 2 * r)) * rA +
        lucasU (kJacobsthalParams k) (j + 2) * rB -
        (lucasU (kJacobsthalParams k) (j + r + 2) +
          (k : ℤ) * lucasU (kJacobsthalParams k) (j + r + 1) +
          2 * lucasU (kJacobsthalParams k) (j + r)) * rC +
        (k : ℤ) ^ 2 * hF1 + 4 * hF0 + 2 * (k : ℤ) * hGc0 +
        lucasU (kJacobsthalParams k) r ^ 2 * hq2 -
        (k : ℤ) ^ 2 * lucasU (kJacobsthalParams k) r ^ 2 * hq1
    refine ⟨hF2, ?_⟩
    have gA : j + 2 + 1 = (j + 1) + 2 := by omega
    have gB : j + 2 + 2 * r + 1 = (j + 1 + 2 * r) + 2 := by omega
    have gC : j + 2 + r + 1 = (j + 1 + r) + 2 := by omega
    have mA : (j + 1) + 1 = j + 2 := by omega
    have mB : (j + 1 + 2 * r) + 1 = (j + 2) + 2 * r := by omega
    have mC : (j + 1 + r) + 1 = (j + 2) + r := by omega
    have y1 : (j + 1) + 1 = j + 2 := by omega
    have y2 : (j + 1) + 2 * r + 1 = (j + 2) + 2 * r := by omega
    have y3 : (j + 1) + r + 1 = (j + 2) + r := by omega
    rw [gA, gB, gC]
    rw [mA] at rA'
    rw [mB] at rB'
    rw [mC] at rC'
    rw [y1, y2, y3] at hGc1
    linear_combination lucasU (kJacobsthalParams k) (j + 2 + 2 * r) * rA' +
      lucasU (kJacobsthalParams k) (j + 2) * rB' -
      2 * lucasU (kJacobsthalParams k) (j + 2 + r) * rC' +
      2 * (k : ℤ) * hF2 + 2 * hGc1 -
      (k : ℤ) * lucasU (kJacobsthalParams k) r ^ 2 * hqa

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
  have hG (m : ℕ) : companionKJacobsthal k a b m =
      a * lucasU (kJacobsthalParams k) (m + 1) +
        (b - a * k) * lucasU (kJacobsthalParams k) m :=
    companionKJacobsthal_eq k a b m
  obtain ⟨hF0, hGc0⟩ := lucasU_kJacobsthal_catalan_cross k r j
  obtain ⟨hF1, -⟩ := lucasU_kJacobsthal_catalan_cross k r (j + 1)
  have hq : (-2 : ℤ) ^ (j + 1) = (-2 : ℤ) ^ j * -2 := pow_succ _ _
  have key : 4 * (companionKJacobsthal k a b j * companionKJacobsthal k a b (j + 2 * r) -
      companionKJacobsthal k a b (j + r) ^ 2) =
      (a ^ 2 * ((k : ℤ) ^ 2 + 8) - (2 * b - a * k) ^ 2) * (-2 : ℤ) ^ j *
        lucasU (kJacobsthalParams k) r ^ 2 := by
    simp only [hG]
    have e1 : (j + 1) + 2 * r = j + 2 * r + 1 := by omega
    have e2 : (j + 1) + r = j + r + 1 := by omega
    rw [e1, e2] at hF1
    linear_combination 4 * a ^ 2 * hF1 + 4 * a * (b - a * k) * hGc0 +
      4 * (b - a * k) ^ 2 * hF0 - 4 * a ^ 2 * lucasU (kJacobsthalParams k) r ^ 2 * hq
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
