/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 1: for all `α, n ≥ 0`, the overpartition function `p̄` satisfies
`p̄(3^{8α+7} (24n + 5)) ≡ p̄(3^{8α+7} (24n + 13)) ≡ 0 (mod 512)`. `p̄(m)` is the standard
number of overpartitions of `m`, `Nat.card (Nat.Overpartition m)`. The record's flattened
`38α+7` is read as the exponent `3^{8α+7}` and its `p` as `p̄`, the function in the title. The
paper's proof works inside the progression `8n + 7` (from `p̄(8n + 7)` to `p̄(24n + 15)` and
`p̄(24(3n + 2) + 15)`), which contains both arguments under this reading but not under the
other parse `(24α + 7)(24n + 5)` (`35 ≡ 3 mod 8`; `p̄(35) ≡ 304 mod 512`). At `α = 0` the
reading is checked exactly for `n ≤ 3`, while the neighbouring residues `24n + 1, 7, 17` and
the smaller power `3^6` give nonzero residues mod 512.

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Theorem 1 (`integers-2025-A76-thm-1`). -/
public theorem_wanted overpartition_three_pow_congr_zero_mod_512 (α n : ℕ) :
    512 ∣ Nat.card (Nat.Overpartition (3 ^ (8 * α + 7) * (24 * n + 5))) ∧
      512 ∣ Nat.card (Nat.Overpartition (3 ^ (8 * α + 7) * (24 * n + 13)))

/-- Lemma 1, identity (10): For `‖q‖ < 1`, with `E(q^k) = (q^k; q^k)_∞`
(`QPochhammer.qPochhammerInf (q ^ k) (q ^ k)`, written `E k`; `E 0 = 1` is unused),
`E(q⁶)³ E(q⁹)⁶ / (E(q³)³ E(q¹⁸)³) = E(q⁶)⁸ E(q⁹) / (E(q³)⁴ E(q¹⁸)²) - q³ E(q¹⁸)⁶ / E(q⁹)³`.

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Lemma 1, identity (10) (`integers-2025-A76-lem-1`). Identity (9) of the same
lemma is `ramanujanPsi_three_dissection` (`OverpartitionSpt2CongruencesWanted`). -/
public theorem_wanted eulerFunction_six_cube_nine_six_div_eq (q : ℂ) (hq : ‖q‖ < 1) :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      QPochhammer.qPochhammerInf (q ^ k) (q ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hk)
    E 6 ^ 3 * E 9 ^ 6 / (E 3 ^ 3 * E 18 ^ 3) =
      E 6 ^ 8 * E 9 / (E 3 ^ 4 * E 18 ^ 2) - q ^ 3 * (E 18 ^ 6 / E 9 ^ 3)

/-- Lemma 1, identity (11): For `‖q‖ < 1`, with `E(q^k) = (q^k; q^k)_∞`
(`QPochhammer.qPochhammerInf (q ^ k) (q ^ k)`, written `E k`; `E 0 = 1` is unused),
`E(q) / E(q²)² = E(q³)² E(q⁹)³ / E(q⁶)⁶ - q E(q³)³ E(q¹⁸)³ / E(q⁶)⁷
  + q² E(q³)⁴ E(q¹⁸)⁶ / (E(q⁶)⁸ E(q⁹)³)`.

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Lemma 1, identity (11) (`integers-2025-A76-lem-1`). -/
public theorem_wanted eulerFunction_one_div_two_sq_eq (q : ℂ) (hq : ‖q‖ < 1) :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      QPochhammer.qPochhammerInf (q ^ k) (q ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hk)
    E 1 / E 2 ^ 2 =
      E 3 ^ 2 * E 9 ^ 3 / E 6 ^ 6 - q * (E 3 ^ 3 * E 18 ^ 3 / E 6 ^ 7) +
        q ^ 2 * (E 3 ^ 4 * E 18 ^ 6 / (E 6 ^ 8 * E 9 ^ 3))

end

end MetaMathlibExt
