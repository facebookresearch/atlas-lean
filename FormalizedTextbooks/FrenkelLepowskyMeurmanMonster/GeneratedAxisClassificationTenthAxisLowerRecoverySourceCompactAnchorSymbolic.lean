/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBlockFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinEncoding

/-! Symbolic source Hadamard-prefix transport, with every original sign and XOR address.
These proof bodies are uncompiled drafts; no4096-coordinate certificate enumeration is used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem bit_power_bound (b : Fin 12) : 2 ^ b.val < 4096 := by
  simpa only [show 2 ^ 12 = 4096 by norm_num] using
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) b.isLt

private theorem mod_power_zero_iff_bits (n r : ℕ) :
    n % 2 ^ r = 0 ↔ ∀ i, i < r → n.testBit i = false := by
  constructor
  · intro h i hi
    have ht := Nat.testBit_mod_two_pow n r i
    rw [h] at ht
    simpa only [hi, decide_true, Bool.true_and, Nat.zero_testBit] using ht.symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < r
    · simp only [hi, decide_true, Bool.true_and, h i hi, Nat.zero_testBit]
    · simp only [hi, decide_false, Bool.false_and, Nat.zero_testBit]

private theorem mod_power_succ_zero (n r : ℕ) :
    n % 2 ^ (r + 1) = 0 ↔ n % 2 ^ r = 0 ∧ n.testBit r = false := by
  constructor
  · intro h
    have hb := (mod_power_zero_iff_bits n (r + 1)).mp h
    exact ⟨(mod_power_zero_iff_bits n r).mpr (fun i hi => hb i (by omega)),
      hb r (by omega)⟩
  · rintro ⟨h, hr⟩
    apply (mod_power_zero_iff_bits n (r + 1)).mpr
    intro i hi
    by_cases hir : i < r
    · exact (mod_power_zero_iff_bits n r).mp h i hir
    · have he : i = r := by omega
      simpa only [he] using hr

private theorem xor_low_residue (n r : ℕ) :
    (Nat.xor n (2 ^ r)) % 2 ^ r = n % 2 ^ r := by
  rw [Nat.xor_eq, Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]

private theorem xor_selected_bit (n r : ℕ) :
    (Nat.xor n (2 ^ r)).testBit r = !(n.testBit r) := by
  rw [Nat.xor_eq, Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases n.testBit r <;> rfl

private theorem xor_high_prefix_zero (n r : ℕ) :
    (Nat.xor n (2 ^ r)) % 2 ^ (r + 1) = 0 ↔
      n % 2 ^ r = 0 ∧ n.testBit r = true := by
  rw [mod_power_succ_zero, xor_low_residue, xor_selected_bit]
  cases n.testBit r <;> simp

private theorem xor_label_bound (k : Fin 4096) (b : Fin 12) :
    Nat.xor k.val (2 ^ b.val) < 4096 := by
  have h := Nat.xor_lt_two_pow (n := 12) k.isLt (bit_power_bound b)
  simpa only [Nat.xor_eq, show 2 ^ 12 = 4096 by norm_num] using h

/-- One full original Fourier bit releases exactly its selected prefix constraint.
The original negative row sign is retained; it multiplies a zero input on that row. -/
theorem generatedTenth_source_compact_fourier_prefix (b : Fin 12) (a : ℤ)
    (k : Fin 4096) :
    generatedNinthLowerSpinTensorFourierInteger b
        (fun n => if n.val % 2 ^ (b.val + 1) = 0 then a else 0) k =
      if k.val % 2 ^ b.val = 0 then a else 0 := by
  have hx := xor_label_bound k b
  unfold generatedNinthLowerSpinTensorFourierInteger
  dsimp only
  simp only [Nat.mod_eq_of_lt hx]
  have hp := mod_power_succ_zero k.val b.val
  have hq := xor_high_prefix_zero k.val b.val
  simp only [hp, hq]
  by_cases hm : k.val % 2 ^ b.val = 0
  · cases k.val.testBit b.val <;> simp [hm]
  · cases k.val.testBit b.val <;> simp [hm]

/-- The complete original integer Hadamard numerator is the exact signed XOR formula.
This identifies genuine Golay coordinates; it does not posit a cached address action. -/
theorem generatedTenth_source_compact_hadamard_fourier (b : Fin 12)
    (u : NortonUIntegerVector) (k : Fin 4096) :
    generatedNinthLowerSpinHadamardInteger b u k =
      generatedNinthLowerSpinTensorFourierInteger b u k := by
  let e : Fin 4096 := ⟨2 ^ b.val, bit_power_bound b⟩
  have he : golayLabelCoefficients e = Pi.single b 1 := by
    funext j
    change (if (2 ^ b.val).testBit j.val then (1 : ZMod 2) else 0) =
      (Pi.single b 1 : SpinIndex) j
    rw [Nat.testBit_two_pow]
    by_cases hj : j = b
    · subst j
      simp only [decide_true, ite_true, Pi.single_eq_same]
    · have hv : b.val ≠ j.val := by
        intro h
        apply hj
        exact Fin.ext h.symm
      simp only [hv, decide_false, Bool.false_eq_true, ite_false, Pi.single_apply, hj]
  have hxor := generatedSixth_spin_label_xor k e
  rw [he] at hxor
  have hl : nortonUIntegerLabel (golayLabelCoefficients k + Pi.single b 1) =
      generatedSixthSpinLabelXor k e := by
    rw [← hxor, nortonUIntegerLabel_coeff]
  have hf : generatedSixthSpinLabelXor k e =
      (⟨(Nat.xor k.val (2 ^ b.val)) % 4096, Nat.mod_lt _ (by norm_num)⟩ : Fin 4096) := by
    apply Fin.ext
    change Nat.xor k.val (2 ^ b.val) = (Nat.xor k.val (2 ^ b.val)) % 4096
    exact (Nat.mod_eq_of_lt (xor_label_bound k b)).symm
  have hs : nortonUIntegerSign (golayLabelCoefficients k b) =
      if k.val.testBit b.val then (-1 : ℤ) else 1 := by
    unfold nortonUIntegerSign golayLabelCoefficients
    cases hb : k.val.testBit b.val <;> norm_num [hb]
  unfold generatedNinthLowerSpinHadamardInteger generatedNinthLowerSpinTensorFourierInteger
  dsimp only
  rw [hs, hl, hf]

/-- Two genuine consecutive Hadamard bits release both low-prefix constraints.
The higher bit acts first, with its actual cross-address and central row sign. -/
theorem generatedTenth_source_compact_hadamard_pair_prefix (r : ℕ) (hr : r + 1 < 12)
    (a : ℤ) (k : Fin 4096) :
    generatedNinthLowerSpinHadamardInteger ⟨r, by omega⟩
      (generatedNinthLowerSpinHadamardInteger ⟨r + 1, hr⟩
        (fun n => if n.val % 2 ^ (r + 2) = 0 then a else 0)) k =
      if k.val % 2 ^ r = 0 then a else 0 := by
  have high : generatedNinthLowerSpinHadamardInteger ⟨r + 1, hr⟩
      (fun n => if n.val % 2 ^ (r + 2) = 0 then a else 0) =
      (fun n => if n.val % 2 ^ (r + 1) = 0 then a else 0) := by
    funext n
    rw [generatedTenth_source_compact_hadamard_fourier]
    exact generatedTenth_source_compact_fourier_prefix ⟨r + 1, hr⟩ a n
  rw [high, generatedTenth_source_compact_hadamard_fourier]
  exact generatedTenth_source_compact_fourier_prefix ⟨r, by omega⟩ a k

/-- Every original paired source-prefix condition follows symbolically, for all4096 labels.
Only six small exponent/amplitude identities are reduced; no finite source vector is enumerated. -/
theorem generatedTenth_source_compact_anchor_pair_condition_symbolic (p : Fin 6) :
    generatedTenthSourceCompactAnchorPairCondition p := by
  let r : ℕ := 10 - 2 * p.val
  have hr : r + 1 < 12 := by dsimp only [r]; omega
  have hi : r + 1 = 11 - 2 * p.val := by dsimp only [r]; omega
  have hin : 4 ^ (6 - p.val) = 2 ^ (r + 2) := by
    fin_cases p <;> norm_num [r]
  have hout : 4 ^ (6 - (p.val + 1)) = 2 ^ r := by
    fin_cases p <;> norm_num [r]
  have ha : ((64 / 2 ^ p.val : ℕ) : ℤ) =
      2 * ((64 / 2 ^ (p.val + 1) : ℕ) : ℤ) := by
    fin_cases p <;> norm_num
  intro k
  change generatedNinthLowerSpinHadamardInteger ⟨r, by omega⟩
      (generatedNinthLowerSpinHadamardInteger ⟨11 - 2 * p.val, by omega⟩
        (fun n => if n.val % 4 ^ (6 - p.val) = 0
          then ((64 / 2 ^ p.val : ℕ) : ℤ) else 0)) k =
    2 * (if k.val % 4 ^ (6 - (p.val + 1)) = 0
      then ((64 / 2 ^ (p.val + 1) : ℕ) : ℤ) else 0)
  have hbit : (⟨11 - 2 * p.val, by omega⟩ : Fin 12) = ⟨r + 1, hr⟩ :=
    Fin.ext hi.symm
  rw [hin, hout, hbit]
  rw [generatedTenth_source_compact_hadamard_pair_prefix r hr, ha]
  split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
