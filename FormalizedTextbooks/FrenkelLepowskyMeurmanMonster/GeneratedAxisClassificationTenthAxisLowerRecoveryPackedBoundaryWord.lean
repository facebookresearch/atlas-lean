/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedFourier

/-! Ungated source packing algebra. No source label permutation is replaced by a catalogue. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Encode the actual signed integer in one complete nine-bit radix digit. -/
def generatedTenthPackedBoundaryResidue (z : ℤ) : ℕ := (z % 512).toNat

/-- Pack all sixteen actual source coefficients, in their original output-slot order. -/
def generatedTenthPackedBoundaryWord (v : Fin 16 → ℤ) : ℕ :=
  Nat.ofDigits 512 (List.ofFn fun i => generatedTenthPackedBoundaryResidue (v i))

private theorem residue_lt (z : ℤ) : generatedTenthPackedBoundaryResidue z < 512 := by
  have h0 := Int.emod_nonneg z (by norm_num : (512 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 512)
  unfold generatedTenthPackedBoundaryResidue
  omega

private theorem natural_digit {n : ℕ} (v : Fin n → ℕ) (hv : ∀ i, v i < 512)
    (i : Fin n) : Nat.ofDigits 512 (List.ofFn v) / 512 ^ i.val % 512 = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [List.ofFn_succ, Nat.ofDigits]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, pow_zero, Nat.div_one]
      change (v 0 + 512 * Nat.ofDigits 512 (List.ofFn fun k => v k.succ)) % 512 = v 0
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
        Nat.add_zero, Nat.mod_mod]
      exact Nat.mod_eq_of_lt (hv 0)
    · have hd : (v 0 + 512 * Nat.ofDigits 512 (List.ofFn fun k => v k.succ)) / 512 =
          Nat.ofDigits 512 (List.ofFn fun k => v k.succ) := by
        rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (hv 0), zero_add]
      change (v 0 + 512 * Nat.ofDigits 512 (List.ofFn fun k => v k.succ)) /
        512 ^ (j.val + 1) % 512 = v j.succ
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hd]
      exact ih (fun k => v k.succ) (fun k => hv k.succ) j

/-- Every packed source word has the full sixteen-slot finite width, without a source bound. -/
theorem generatedTenth_packed_boundary_word_lt (v : Fin 16 → ℤ) :
    generatedTenthPackedBoundaryWord v < 512 ^ 16 := by
  unfold generatedTenthPackedBoundaryWord
  have h := Nat.ofDigits_lt_base_pow_length
    (l := List.ofFn fun i => generatedTenthPackedBoundaryResidue (v i))
    (by norm_num : 1 < (512 : ℕ)) (fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact residue_lt (v i))
  simpa using h

/-- Balanced decoding preserves the actual source coefficient under its genuine small bound. -/
theorem generatedTenth_packed_boundary_word_digit (v : Fin 16 → ℤ)
    (hv : ∀ i, |v i| ≤ 176) (i : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedTenthPackedBoundaryWord v) i = v i := by
  have hd := natural_digit (fun j => generatedTenthPackedBoundaryResidue (v j))
    (fun j => residue_lt (v j)) i
  have h0 := Int.emod_nonneg (v i) (by norm_num : (512 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos (v i) (by norm_num : (0 : ℤ) < 512)
  have h2 := abs_le.mp (hv i)
  unfold generatedRootEightPackedSignedDigit generatedTenthPackedBoundaryWord
  rw [hd]
  unfold generatedTenthPackedBoundaryResidue
  dsimp only
  split_ifs <;> omega

/-- A computable complete-word small bound replaces a separately supplied scalar catalogue. -/
def generatedTenthPackedBoundaryAbsMax (w : ℕ) : ℕ :=
  Finset.univ.sup fun i : Fin 16 => (generatedRootEightPackedSignedDigit w i).natAbs

/-- The word maximum bounds every original signed slot. -/
theorem generatedTenth_packed_boundary_abs_max (w M : ℕ)
    (h : generatedTenthPackedBoundaryAbsMax w ≤ M) (i : Fin 16) :
    |generatedRootEightPackedSignedDigit w i| ≤ (M : ℤ) := by
  have hi : (generatedRootEightPackedSignedDigit w i).natAbs ≤ M :=
    (Finset.le_sup (Finset.mem_univ i)).trans h
  have hc : ((generatedRootEightPackedSignedDigit w i).natAbs : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast hi
  simpa only [Int.natCast_natAbs] using hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
