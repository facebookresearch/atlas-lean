/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.InversionSequenceAvoidSeven
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MetaMathlibExt PowerSeries

private abbrev B₁ : Finset (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]}

private abbrev B₂ : Finset (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}

private abbrev B₃ : Finset (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}

private instance (x y z : ℕ) (p : Fin 3 → ℕ) : Decidable (InvSeqPatternSameOrder x y z p) :=
  decidable_of_iff _ invSeqPatternSameOrder_iff.symm

private instance {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) :
    Decidable (InvSeqContainsPattern e p) :=
  decidable_of_iff _ (invSeqContainsPattern_iff_exists_indices e p).symm

-- Enumerate all bounded words and test three-index occurrences directly, without the GF identity
-- or the characterization used in its proof. Every inversion sequence of length n has entries < n.
private def countByEnumeration (B : Finset (Fin 3 → ℕ)) (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin n)).filter fun e =>
    (∀ i, e i ≤ i) ∧ ∀ p ∈ B, ¬ InvSeqContainsPattern (fun i => (e i : ℕ)) p).card

-- Extract the first nontrivial coefficients from the public identity.
private theorem initialCoefficients (B : Set (Fin 3 → ℕ))
    (h : (1 - X) * (1 - 2 * X) ^ 2 * invSeqAvoidGF B =
      X * (1 - 2 * X) ^ 2 + X ^ 2 * (1 - X) ^ 2) :
    coeff 2 (invSeqAvoidGF B) = 2 ∧ coeff 3 (invSeqAvoidGF B) = 4 ∧
      coeff 4 (invSeqAvoidGF B) = 9 := by
  let F := invSeqAvoidGF B
  have h' : F - C (5 : ℚ) * (X ^ 1 * F) + C (8 : ℚ) * (X ^ 2 * F) -
      C (4 : ℚ) * (X ^ 3 * F) = X ^ 1 - C (3 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 3 + X ^ 4 := by
    convert h using 1 <;> simp only [F, map_ofNat] <;> ring
  have h0 : coeff 0 F = 0 := (coeff_invSeqAvoidGF B 0).1
  have h1 : coeff 1 F = 1 := by
    rw [(coeff_invSeqAvoidGF B 0).2, invSeqAvoidCount_one, Nat.cast_one]
  have h2 : coeff 2 F = 2 := by
    have he := congrArg (coeff 2) h'
    norm_num [coeff_X_pow_mul', coeff_X_pow, coeff_X, h0, h1] at he
    linarith
  have h3 : coeff 3 F = 4 := by
    have he := congrArg (coeff 3) h'
    norm_num [coeff_X_pow_mul', coeff_X_pow, coeff_X, h0, h1, h2] at he
    linarith
  have h4 : coeff 4 F = 9 := by
    have he := congrArg (coeff 4) h'
    norm_num [coeff_X_pow_mul', coeff_X_pow, coeff_X, h1, h2, h3] at he
    linarith
  exact ⟨h2, h3, h4⟩

-- Length two is below the length of a forbidden pattern.
example : countByEnumeration B₁ 2 = 2 ∧ coeff 2 (invSeqAvoidGF B₁) = 2 := by
  refine ⟨by decide, (initialCoefficients B₁ (invSeqAvoidGF_010_011_102_201_210_seven B₁ ?_)).1⟩
  left
  simp [B₁]

-- Length three is the first length at which avoidance can remove sequences.
example : countByEnumeration B₂ 3 = 4 ∧ coeff 3 (invSeqAvoidGF B₂) = 4 := by
  refine ⟨by decide, (initialCoefficients B₂ (invSeqAvoidGF_010_011_102_201_210_seven B₂ ?_)).2.1⟩
  right; left
  simp [B₂]

-- At length four the enumeration includes sequences that descend only into the last position.
example : countByEnumeration B₃ 4 = 9 ∧ coeff 4 (invSeqAvoidGF B₃) = 9 := by
  refine ⟨by decide, (initialCoefficients B₃ (invSeqAvoidGF_010_011_102_201_210_seven B₃ ?_)).2.2⟩
  right; right
  simp [B₃]
