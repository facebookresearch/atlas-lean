/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integral representations of k-Jacobsthal and k-Jacobsthal-Lucas numbers

Statements from Weerayuth Nilsrakoo and Achariya Nilsrakoo, "An Integral Representation of
k-Jacobsthal and k-Jacobsthal-Lucas Numbers", *INTEGERS* 25 (2025), Article A74
(<https://math.colgate.edu/~integers/z74/z74.pdf>).

The `k`-Jacobsthal numbers `J_{k,n}` (`0, 1`, `J_{k,n} = k J_{k,n-1} + 2 J_{k,n-2}`) and the
`k`-Jacobsthal-Lucas numbers `j_{k,n}` (`2, k`, same recurrence) are the Lucas sequences
`lucasU` and `lucasV` with parameters `(P, Q) = (k, -2)` (`kJacobsthalParams k`).
`Δ_k = √(k² + 8)` and `σ_k = (k + Δ_k)/2`. The companion numbers `𝒥_{k,n}(a, b)` (`a, b`,
same recurrence) are `companionKJacobsthal k a b`. Integrals are interval integrals over
`[-1, 1]`; the exponent `n - 1` is an integer power. At `n = 0` the integrands without a
prefactor `n` are the paper's `(…)(…)^{-1}`, a.e. constant. The statements with a prefactor
`n` (Theorem 1, Theorem 2 (i), Corollary 1, Corollary 2 (i)) hold at `n = 0` only because that
prefactor is `0`: their integrand is `(…)^{-1}`, which in Theorem 1 and Corollary 1 can have a
pole in `[-1, 1]` (`k = ℓ = 1` gives `(1 + 3x)^{-1}`), where `intervalIntegral` returns `0`.

Corollary 6 is not formalized: as printed it is false (see the source audit table).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.LucasSequence

namespace MetaMathlibExt

@[expose] public section


/-- The Lucas-sequence parameters `(P, Q) = (k, -2)` of the `k`-Jacobsthal numbers
`J_{k,n} = U_n(k, -2)` and the `k`-Jacobsthal-Lucas numbers `j_{k,n} = V_n(k, -2)`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 1, recurrences (1) and (2). -/
def kJacobsthalParams (k : ℕ) : LucasSequenceParams where
  p := k
  q := -2
  q_ne_zero := by decide

/-- `J_{k,2} = k`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
proof of Theorem 2. -/
theorem lucasU_kJacobsthalParams_two (k : ℕ) : lucasU (kJacobsthalParams k) 2 = k := by
  simp [lucasU, kJacobsthalParams]

/-- `j_{k,2} = k² + 4`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
proof of Theorem 2. -/
theorem lucasV_kJacobsthalParams_two (k : ℕ) :
    lucasV (kJacobsthalParams k) 2 = (k : ℤ) ^ 2 + 4 := by
  simp [lucasV, kJacobsthalParams]
  ring

/-- The companion `k`-Jacobsthal numbers `𝒥_{k,n}(a, b)`: `𝒥_{k,0} = a`, `𝒥_{k,1} = b`,
`𝒥_{k,n} = k 𝒥_{k,n-1} + 2 𝒥_{k,n-2}`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4. -/
def companionKJacobsthal (k : ℕ) (a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n + 2 => k * companionKJacobsthal k a b (n + 1) + 2 * companionKJacobsthal k a b n

/-- The companion recurrence `𝒥_{k,n+2} = k 𝒥_{k,n+1} + 2 𝒥_{k,n}`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4. -/
theorem companionKJacobsthal_add_two (k : ℕ) (a b : ℤ) (n : ℕ) :
    companionKJacobsthal k a b (n + 2) =
      k * companionKJacobsthal k a b (n + 1) + 2 * companionKJacobsthal k a b n :=
  rfl

/-- `𝒥_{k,2} = bk + 2a`, as listed in the paper.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4, list of the first companion numbers. -/
theorem companionKJacobsthal_two (k : ℕ) (a b : ℤ) :
    companionKJacobsthal k a b 2 = b * k + 2 * a := by
  simp [companionKJacobsthal]
  ring

/-- With `(a, b) = (0, 1)` the companion numbers are the `k`-Jacobsthal numbers.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4, special cases of the companion numbers. -/
theorem companionKJacobsthal_zero_one (k n : ℕ) :
    companionKJacobsthal k 0 1 n = lucasU (kJacobsthalParams k) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      rw [companionKJacobsthal_add_two, ih1, ih2, lucasU_add_two]
      simp [kJacobsthalParams]

/-- `J[k, n]` is the real cast of `J_{k,n} = lucasU (kJacobsthalParams k) n`. -/
local notation "J[" k ", " n "]" => (lucasU (kJacobsthalParams k) n : ℝ)
/-- `jL[k, n]` is the real cast of `j_{k,n} = lucasV (kJacobsthalParams k) n`. -/
local notation "jL[" k ", " n "]" => (lucasV (kJacobsthalParams k) n : ℝ)
/-- `Δ[k] = √(k² + 8)`. -/
local notation "Δ[" k "]" => Real.sqrt ((k : ℝ) ^ 2 + 8)

/-- Binet-type identities: `j_{k,n} + Δ_k J_{k,n} = 2σ_kⁿ`,
`j_{k,n} - Δ_k J_{k,n} = 2(-2)ⁿ/σ_kⁿ`, and `j_{k,n}² - Δ_k² J_{k,n}² = (-2)^{n+2}`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Lemma 1 (`integers-2025-A74-lem-1`). -/
public theorem_wanted kJacobsthal_binet_identities (k n : ℕ) :
    jL[k, n] + Δ[k] * J[k, n] = 2 * ((k + Δ[k]) / 2) ^ n ∧
      jL[k, n] - Δ[k] * J[k, n] = 2 * (-2) ^ n / ((k + Δ[k]) / 2) ^ n ∧
      lucasV (kJacobsthalParams k) n ^ 2 - ((k : ℤ) ^ 2 + 8) * lucasU (kJacobsthalParams k) n ^ 2 =
        (-2) ^ (n + 2)

/-- Addition formulas: `2J_{k,m+n} = J_{k,m} j_{k,n} + J_{k,n} j_{k,m}` and
`2j_{k,m+n} = j_{k,m} j_{k,n} + Δ_k² J_{k,m} J_{k,n}`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Lemma 2 (`integers-2025-A74-lem-2`). -/
public theorem_wanted kJacobsthal_add_formulas (k m n : ℕ) :
    2 * lucasU (kJacobsthalParams k) (m + n) =
        lucasU (kJacobsthalParams k) m * lucasV (kJacobsthalParams k) n +
          lucasU (kJacobsthalParams k) n * lucasV (kJacobsthalParams k) m ∧
      2 * lucasV (kJacobsthalParams k) (m + n) =
        lucasV (kJacobsthalParams k) m * lucasV (kJacobsthalParams k) n +
          ((k : ℤ) ^ 2 + 8) * lucasU (kJacobsthalParams k) m * lucasU (kJacobsthalParams k) n

/-- `J_{k,ℓn} = (n J_{k,ℓ} / 2ⁿ) ∫_{-1}^{1} (j_{k,ℓ} + Δ_k J_{k,ℓ} x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 1 (`integers-2025-A74-thm-1`). -/
public theorem_wanted lucasU_kJacobsthal_mul_eq_integral (k ℓ n : ℕ) :
    (lucasU (kJacobsthalParams k) (ℓ * n) : ℝ) =
      n * J[k, ℓ] / 2 ^ n *
        ∫ x in (-1 : ℝ)..1, (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)

/-- `J_{k,2n} = (kn/2ⁿ) ∫_{-1}^{1} (k² + 4 + kΔ_k x)^{n-1} dx` and
`J_{k,2n+1} = 2^{-(n+1)} ∫_{-1}^{1} (nk² + k² + 4 + k(n+1)Δ_k x)(k² + 4 + kΔ_k x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 2 (`integers-2025-A74-thm-2`). -/
public theorem_wanted lucasU_kJacobsthal_even_odd_eq_integral (k n : ℕ) :
    (lucasU (kJacobsthalParams k) (2 * n) : ℝ) =
        k * n / 2 ^ n * ∫ x in (-1 : ℝ)..1, ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1) ∧
      (lucasU (kJacobsthalParams k) (2 * n + 1) : ℝ) =
        1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
          (n * (k : ℝ) ^ 2 + k ^ 2 + 4 + k * (n + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1)

/-- `j_{k,ℓn} = 2^{-n} ∫_{-1}^{1} (j_{k,ℓ} + (n+1)Δ_k J_{k,ℓ} x)(j_{k,ℓ} + Δ_k J_{k,ℓ} x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 3 (`integers-2025-A74-thm-3`). -/
public theorem_wanted lucasV_kJacobsthal_mul_eq_integral (k ℓ n : ℕ) :
    (lucasV (kJacobsthalParams k) (ℓ * n) : ℝ) =
      1 / 2 ^ n * ∫ x in (-1 : ℝ)..1,
        (jL[k, ℓ] + (n + 1) * Δ[k] * J[k, ℓ] * x) * (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)

/-- `j_{k,2n} = 2^{-n} ∫_{-1}^{1} (k² + 4 + k(n+1)Δ_k x)(k² + 4 + kΔ_k x)^{n-1} dx` and
`j_{k,2n+1} = (k/2^{n+1}) ∫_{-1}^{1} (nΔ_k² + k² + 4 + k(n+1)Δ_k x)(k² + 4 + kΔ_k x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 6 (`integers-2025-A74-thm-6`). -/
public theorem_wanted lucasV_kJacobsthal_even_odd_eq_integral (k n : ℕ) :
    (lucasV (kJacobsthalParams k) (2 * n) : ℝ) =
        1 / 2 ^ n * ∫ x in (-1 : ℝ)..1,
          ((k : ℝ) ^ 2 + 4 + k * (n + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1) ∧
      (lucasV (kJacobsthalParams k) (2 * n + 1) : ℝ) =
        k / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
          (n * ((k : ℝ) ^ 2 + 8) + k ^ 2 + 4 + k * (n + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1)

/-- Jacobsthal case `k = 1`: `J_{ℓn} = (n J_ℓ/2ⁿ) ∫_{-1}^{1} (j_ℓ + 3J_ℓ x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 1 (`integers-2025-A74-cor-1`). -/
public theorem_wanted jacobsthal_mul_eq_integral (ℓ n : ℕ) :
    (lucasU (kJacobsthalParams 1) (ℓ * n) : ℝ) =
      n * J[1, ℓ] / 2 ^ n * ∫ x in (-1 : ℝ)..1, (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

/-- Jacobsthal case `k = 1`: `J_{2n} = (n/2ⁿ) ∫_{-1}^{1} (5 + 3x)^{n-1} dx` and
`J_{2n+1} = 2^{-(n+1)} ∫_{-1}^{1} (n + 5 + 3(n+1)x)(5 + 3x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 2 (`integers-2025-A74-cor-2`). -/
public theorem_wanted jacobsthal_even_odd_eq_integral (n : ℕ) :
    (lucasU (kJacobsthalParams 1) (2 * n) : ℝ) =
        n / 2 ^ n * ∫ x in (-1 : ℝ)..1, (5 + 3 * x) ^ ((n : ℤ) - 1) ∧
      (lucasU (kJacobsthalParams 1) (2 * n + 1) : ℝ) =
        1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
          (n + 5 + 3 * (n + 1) * x) * (5 + 3 * x) ^ ((n : ℤ) - 1)

/-- Jacobsthal-Lucas case `k = 1`:
`j_{ℓn} = 2^{-n} ∫_{-1}^{1} (j_ℓ + 3(n+1)J_ℓ x)(j_ℓ + 3J_ℓ x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 3 (`integers-2025-A74-cor-3`). -/
public theorem_wanted jacobsthalLucas_mul_eq_integral (ℓ n : ℕ) :
    (lucasV (kJacobsthalParams 1) (ℓ * n) : ℝ) =
      1 / 2 ^ n * ∫ x in (-1 : ℝ)..1,
        (jL[1, ℓ] + 3 * (n + 1) * J[1, ℓ] * x) * (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

/-- Jacobsthal case `k = 1`: `J_{ℓn+r} = 2^{-(n+1)} ∫_{-1}^{1}
(nJ_ℓ j_r + J_r j_ℓ + 3(n+1)J_ℓ J_r x)(j_ℓ + 3J_ℓ x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 4 (`integers-2025-A74-cor-4`). -/
public theorem_wanted jacobsthal_mul_add_eq_integral (ℓ n r : ℕ) :
    (lucasU (kJacobsthalParams 1) (ℓ * n + r) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (n * J[1, ℓ] * jL[1, r] + J[1, r] * jL[1, ℓ] +
            3 * (n + 1) * J[1, ℓ] * J[1, r] * x) * (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

/-- Jacobsthal-Lucas case `k = 1`: `j_{ℓn+r} = 2^{-(n+1)} ∫_{-1}^{1}
(9nJ_ℓ J_r + j_ℓ j_r + 3(n+1)J_ℓ j_r x)(j_ℓ + 3J_ℓ x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Corollary 5 (`integers-2025-A74-cor-5`). -/
public theorem_wanted jacobsthalLucas_mul_add_eq_integral (ℓ n r : ℕ) :
    (lucasV (kJacobsthalParams 1) (ℓ * n + r) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (9 * n * J[1, ℓ] * J[1, r] + jL[1, ℓ] * jL[1, r] +
            3 * (n + 1) * J[1, ℓ] * jL[1, r] * x) * (jL[1, ℓ] + 3 * J[1, ℓ] * x) ^ ((n : ℤ) - 1)

/-- `J_{k,n+1}/J_{k,n} → σ_k = (k + Δ_k)/2` as `n → ∞`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 8 (`integers-2025-A74-thm-8`). -/
public theorem_wanted tendsto_lucasU_kJacobsthal_ratio (k : ℕ) (hk : 0 < k) :
    Filter.Tendsto
      (fun n : ℕ => (lucasU (kJacobsthalParams k) (n + 1) : ℝ) / lucasU (kJacobsthalParams k) n)
      Filter.atTop (nhds ((k + Δ[k]) / 2))

/-- `𝒥_{k,n} = (a/2) j_{k,n} + ((2b - ak)/2) J_{k,n}`, stated after clearing the denominator 2.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 9 (`integers-2025-A74-thm-9`). -/
public theorem_wanted two_mul_companionKJacobsthal (k : ℕ) (a b : ℤ) (n : ℕ) :
    2 * companionKJacobsthal k a b n =
      a * lucasV (kJacobsthalParams k) n + (2 * b - a * k) * lucasU (kJacobsthalParams k) n

/-- The generating function `∑ 𝒥_{k,n} xⁿ = (a + (b - ak)x)/(1 - kx - 2x²)`, stated after clearing
the denominator in `ℤ[[x]]`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 10 (`integers-2025-A74-thm-10`). -/
public theorem_wanted companionKJacobsthal_generatingFunction (k : ℕ) (a b : ℤ) :
    PowerSeries.mk (companionKJacobsthal k a b) *
        (1 - PowerSeries.C (k : ℤ) * PowerSeries.X - PowerSeries.C 2 * PowerSeries.X ^ 2) =
      PowerSeries.C a + PowerSeries.C (b - a * k) * PowerSeries.X

/-- Catalan's identity: for `r ≤ n`,
`𝒥_{k,n-r} 𝒥_{k,n+r} - 𝒥_{k,n}² = (2b - ak + aΔ_k)(ak - 2b + aΔ_k)(-2)^{n-r-2} J_{k,r}²`, with
`(2b - ak + aΔ_k)(ak - 2b + aΔ_k) = a²Δ_k² - (2b - ak)²` and `(-2)^{n-r-2}` an integer power in
`ℚ`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 11 (`integers-2025-A74-thm-11`). -/
public theorem_wanted companionKJacobsthal_catalan (k : ℕ) (a b : ℤ) (n r : ℕ) (hrn : r ≤ n) :
    ((companionKJacobsthal k a b (n - r) * companionKJacobsthal k a b (n + r) -
        companionKJacobsthal k a b n ^ 2 : ℤ) : ℚ) =
      ((a ^ 2 * ((k : ℤ) ^ 2 + 8) - (2 * b - a * k) ^ 2 : ℤ) : ℚ) *
        (-2 : ℚ) ^ ((n : ℤ) - r - 2) * (lucasU (kJacobsthalParams k) r : ℚ) ^ 2

/-- `𝒥_{k,ℓn} = 2^{-(n+1)} ∫_{-1}^{1} (a j_{k,ℓ} + (2b - ak) n J_{k,ℓ} + a(n+1)Δ_k J_{k,ℓ} x)
(j_{k,ℓ} + Δ_k J_{k,ℓ} x)^{n-1} dx`.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 12 (`integers-2025-A74-thm-12`). -/
public theorem_wanted companionKJacobsthal_mul_eq_integral (k ℓ n : ℕ) (a b : ℤ) :
    (companionKJacobsthal k a b (ℓ * n) : ℝ) =
      1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
        (a * jL[k, ℓ] + (2 * b - a * k) * n * J[k, ℓ] +
            a * (n + 1) * Δ[k] * J[k, ℓ] * x) * (jL[k, ℓ] + Δ[k] * J[k, ℓ] * x) ^ ((n : ℤ) - 1)

end

end MetaMathlibExt
