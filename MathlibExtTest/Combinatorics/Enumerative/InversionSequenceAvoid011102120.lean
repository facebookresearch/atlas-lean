/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.InversionSequenceAvoid011102120

open PowerSeries

namespace MetaMathlibExt.invSeqAvoidGF_011_102_120

local notation "B₀" => ({![0, 1, 1], ![1, 0, 2], ![1, 2, 0]} : Set (Fin 3 → ℕ))

/-- The identity `(1 - 2x)² F = x(1 - x)²`, read off at the coefficient of `xⁿ`. -/
private theorem coeff_identity (n : ℕ) :
    coeff n (invSeqAvoidGF B₀) - 4 * (if 1 ≤ n then coeff (n - 1) (invSeqAvoidGF B₀) else 0) +
        4 * (if 2 ≤ n then coeff (n - 2) (invSeqAvoidGF B₀) else 0) =
      (if n = 1 then 1 else 0) - 2 * (if n = 2 then 1 else 0) + (if n = 3 then 1 else 0) := by
  have h := congrArg (coeff n) invSeqAvoidGF_011_102_120
  have hL : (1 - 2 * X) ^ 2 * invSeqAvoidGF B₀ = invSeqAvoidGF B₀ -
      C (4 : ℚ) * (X ^ 1 * invSeqAvoidGF B₀) + C (4 : ℚ) * (X ^ 2 * invSeqAvoidGF B₀) := by
    rw [map_ofNat]
    ring
  have hR : (X : ℚ⟦X⟧) * (1 - X) ^ 2 = X ^ 1 - C (2 : ℚ) * X ^ 2 + X ^ 3 := by
    rw [map_ofNat]
    ring
  rw [hL, hR] at h
  simpa only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow] using h

private theorem count_cast (n : ℕ) :
    coeff (n + 1) (invSeqAvoidGF B₀) = (invSeqAvoidCount B₀ (n + 1) : ℚ) :=
  (coeff_invSeqAvoidGF B₀ n).2

-- The theorem determines the second and third counts from the first.
example : invSeqAvoidCount B₀ 2 = 2 := by
  have h := coeff_identity 2
  have h1 : (invSeqAvoidCount B₀ 1 : ℚ) = 1 := by rw [invSeqAvoidCount_one, Nat.cast_one]
  simp only [count_cast, (coeff_invSeqAvoidGF B₀ 0).1] at h
  norm_num at h
  exact_mod_cast (by linarith : (invSeqAvoidCount B₀ 2 : ℚ) = 2)

example : invSeqAvoidCount B₀ 3 = 5 := by
  have h2 := coeff_identity 2
  have h3 := coeff_identity 3
  have h1 : (invSeqAvoidCount B₀ 1 : ℚ) = 1 := by rw [invSeqAvoidCount_one, Nat.cast_one]
  simp only [count_cast, (coeff_invSeqAvoidGF B₀ 0).1] at h2 h3
  norm_num at h2 h3
  exact_mod_cast (by linarith : (invSeqAvoidCount B₀ 3 : ℚ) = 5)

-- From length four on, the counts satisfy `|I_{n+4}| = 4 |I_{n+3}| - 4 |I_{n+2}|`.
example (n : ℕ) :
    (invSeqAvoidCount B₀ (n + 4) : ℚ) =
      4 * invSeqAvoidCount B₀ (n + 3) - 4 * invSeqAvoidCount B₀ (n + 2) := by
  have h := coeff_identity (n + 4)
  simp only [show n + 4 - 1 = n + 2 + 1 by omega, show n + 4 - 2 = n + 1 + 1 by omega,
    show n + 4 = n + 3 + 1 by omega, count_cast] at h
  norm_num at h
  linarith

-- `0 1 1` is an occurrence of `011`, so it is not counted.
example : InvSeqContainsPattern (![0, 1, 1] : Fin 3 → ℕ) ![0, 1, 1] :=
  ⟨OrderEmbedding.ofStrictMono id strictMono_id, by decide⟩

end MetaMathlibExt.invSeqAvoidGF_011_102_120
