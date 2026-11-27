/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EisensteinRamanujanCongruence

open PowerSeries
open scoped PowerSeries.WithPiTopology

-- At weight 12 the weight-zero factor is 1, giving the Ramanujan congruence modulo 691.
example (n : ℕ) (hn : 1 ≤ n) :
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    (((ArithmeticFunction.sigma 11 n : ℚ) - coeff n Δ) / 691).den.Coprime 691 := by
  intro Δ
  have h := (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_one 12 (by decide)).2 n hn
  have hB : (-bernoulli 12 / (2 * 12)).num.natAbs = 691 := by decide +kernel
  have hunit : PowerSeries.mk (fun j => if j = 0 then (1 : ℚ) else 0) = 1 := by
    ext j
    simp [coeff_one]
  simpa [show n ≠ 0 by omega, hunit, hB, Nat.sup_divisors_id, Δ] using h

private def sigma₀ (w n : ℕ) : ℚ :=
  if w = 0 then (if n = 0 then 1 else 0)
  else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)

private noncomputable def delta : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24

private noncomputable def b (k i n : ℕ) : ℚ :=
  coeff n (delta ^ i * PowerSeries.mk (sigma₀ (k - 12 * i))) / sigma₀ (k - 12 * i) 0

private def modulus (k : ℕ) : ℕ :=
  let Nw (w : ℕ) := if w ≤ 2 then 1 else (sigma₀ w 0).num.natAbs
  ((Nat.divisors (Nw k)).filter fun d =>
    ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id

private def gamma₂ (k : ℕ) : ℚ := 2 ^ (k - 1) + 25 - 1 / sigma₀ (k - 12) 0

private def gamma₃ (k : ℕ) : ℚ :=
  3 ^ (k - 1) + 2 ^ (k - 1) * 48 + 949 - (2 ^ (k - 13) + 25) / sigma₀ (k - 12) 0 -
    (2 ^ (k - 1) + 25) / sigma₀ (k - 24) 0 + 1 / (sigma₀ (k - 12) 0 * sigma₀ (k - 24) 0)

-- At the weight-zero endpoint the third basis element is just Δ³, even at n = 0.
example (n : ℕ) :
    ((sigma₀ 36 n - (b 36 1 n + gamma₂ 36 * b 36 2 n + gamma₃ 36 * coeff n (delta ^ 3))) /
      modulus 36).den.Coprime (modulus 36) := by
  have h := (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_three 36 (by decide)).1 n
  change ((sigma₀ 36 n - (b 36 1 n + gamma₂ 36 * b 36 2 n + gamma₃ 36 * b 36 3 n)) /
    modulus 36).den.Coprime (modulus 36) at h
  have hunit : PowerSeries.mk (sigma₀ 0) = 1 := by
    ext j
    simp [sigma₀, coeff_one]
  rwa [show b 36 3 n = coeff n (delta ^ 3) by
    change coeff n (delta ^ 3 * PowerSeries.mk (sigma₀ 0)) / sigma₀ 0 0 = _
    simp [hunit, show sigma₀ 0 0 = 1 by decide]] at h

-- The weight-50 case reaches the weight-14 endpoint. Use a coefficient beyond the three
-- coefficients that determined γ₂ and γ₃.
example :
    ((sigma₀ 50 4 - (b 50 1 4 + gamma₂ 50 * b 50 2 4 + gamma₃ 50 * b 50 3 4)) /
      modulus 50).den.Coprime (modulus 50) :=
  (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_three 50 (by decide)).2 4 (by decide)
