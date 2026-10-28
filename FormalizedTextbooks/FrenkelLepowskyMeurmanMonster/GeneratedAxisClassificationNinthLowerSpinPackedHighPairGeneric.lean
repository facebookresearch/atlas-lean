/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

/-! Original high Fourier bits act on full packed words and retain every signed slot. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A complete eight-bit word prefix with its original four-bit signed slot. -/
def generatedNinthLowerSpinPackedPrefixIndex (a : Fin 256) (i : Fin 16) : Fin 4096 :=
  ⟨a.val * 16 + i.val, by omega⟩

/-- A genuine high Fourier bit in the original twelve-bit source label. -/
def generatedNinthLowerSpinPackedHighBit (k : Fin 8) : Fin 12 :=
  ⟨k.val + 4, by omega⟩

/-- The complete original word prefix after toggling one high Fourier bit. -/
def generatedNinthLowerSpinPackedPrefixXor (k : Fin 8) (a : Fin 256) : Fin 256 :=
  ⟨a.val ^^^ (2 ^ k.val), by
    have h : 2 ^ k.val < 256 := by
      simpa only [show 2 ^ 8 = 256 by decide] using
        Nat.pow_lt_pow_right (by decide : 1 < 2) k.isLt
    change a.val ^^^ (2 ^ k.val) < 2 ^ 8
    exact Nat.xor_lt_two_pow a.isLt h⟩

/-- All four actual source words of one high Fourier pair. -/
def generatedNinthLowerSpinPackedHighSources (w : Fin 256 → ℕ)
    (k l : Fin 8) (a : Fin 256) : Fin 4 → ℕ :=
  ![w a, w (generatedNinthLowerSpinPackedPrefixXor l a),
    w (generatedNinthLowerSpinPackedPrefixXor k a),
    w (generatedNinthLowerSpinPackedPrefixXor l
      (generatedNinthLowerSpinPackedPrefixXor k a))]

/-- The complete original paired Fourier signs. -/
def generatedNinthLowerSpinPackedHighCoefficients (k l : Fin 8) (a : Fin 256) : Fin 4 → ℤ :=
  let sk : ℤ := if a.val.testBit k.val then -1 else 1
  let sl : ℤ := if a.val.testBit l.val then -1 else 1
  ![sk * sl, sk, sl, 1]

private theorem prefix_xor (k : Fin 8) (a : Fin 256) (i : Fin 16) :
    (⟨(Nat.xor (generatedNinthLowerSpinPackedPrefixIndex a i).val
        (2 ^ (generatedNinthLowerSpinPackedHighBit k).val)) % 4096,
      Nat.mod_lt _ (by decide)⟩ : Fin 4096) =
      generatedNinthLowerSpinPackedPrefixIndex (generatedNinthLowerSpinPackedPrefixXor k a) i := by
  apply Fin.ext
  have hpow : 2 ^ (k.val + 4) = 2 ^ k.val * 16 := by rw [pow_add]; norm_num
  have hlow : 2 ^ k.val * 16 % 16 = 0 := by omega
  have hdiv : 2 ^ k.val * 16 / 16 = 2 ^ k.val := by omega
  have hn : a.val * 16 + i.val < 4096 := by omega
  have hbit : 2 ^ (k.val + 4) < 4096 := by
    simpa only [show 2 ^ 12 = 4096 by decide] using
      Nat.pow_lt_pow_right (by decide : 1 < 2) (show k.val + 4 < 12 by omega)
  have hx : Nat.xor (a.val * 16 + i.val) (2 ^ (k.val + 4)) < 4096 := by
    change Nat.xor (a.val * 16 + i.val) (2 ^ (k.val + 4)) < 2 ^ 12
    exact Nat.xor_lt_two_pow hn hbit
  have ha : (a.val * 16 + i.val) / 16 = a.val := by omega
  have hi : (a.val * 16 + i.val) % 16 = i.val := by omega
  have hd := Nat.xor_div_two_pow (a := a.val * 16 + i.val)
    (b := 2 ^ (k.val + 4)) (n := 4)
  have hm := Nat.xor_mod_two_pow (a := a.val * 16 + i.val)
    (b := 2 ^ (k.val + 4)) (n := 4)
  change Nat.xor (a.val * 16 + i.val) (2 ^ (k.val + 4)) / 16 = _ at hd
  change Nat.xor (a.val * 16 + i.val) (2 ^ (k.val + 4)) % 16 = _ at hm
  rw [ha, hpow, hdiv] at hd
  rw [hi, hpow, hlow, Nat.xor_zero] at hm
  rw [← hpow] at hd hm
  have hr := Nat.mod_add_div (Nat.xor (a.val * 16 + i.val) (2 ^ (k.val + 4))) 16
  rw [hd, hm] at hr
  dsimp only [generatedNinthLowerSpinPackedPrefixIndex,
    generatedNinthLowerSpinPackedHighBit, generatedNinthLowerSpinPackedPrefixXor]
  rw [Nat.mod_eq_of_lt hx]
  omega

private theorem prefix_testBit (k : Fin 8) (a : Fin 256) (i : Fin 16) :
    (generatedNinthLowerSpinPackedPrefixIndex a i).val.testBit
      (generatedNinthLowerSpinPackedHighBit k).val = a.val.testBit k.val := by
  have ha : (a.val * 16 + i.val) / 16 = a.val := by omega
  have h := Nat.testBit_add (a.val * 16 + i.val) k.val 4
  change (a.val * 16 + i.val).testBit (k.val + 4) = a.val.testBit k.val
  simpa only [show 2 ^ 4 = 16 by decide, ha] using h

private theorem prefix_xor_testBit (k l : Fin 8) (hkl : k ≠ l) (a : Fin 256) :
    (generatedNinthLowerSpinPackedPrefixXor k a).val.testBit l.val = a.val.testBit l.val := by
  have hval : k.val ≠ l.val := by intro h; apply hkl; exact Fin.ext h
  change (a.val ^^^ 2 ^ k.val).testBit l.val = a.val.testBit l.val
  rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne hval]
  cases a.val.testBit l.val <;> rfl

private theorem fourier_prefix (k : Fin 8) (v : NortonUIntegerVector)
    (a : Fin 256) (i : Fin 16) :
    generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit k) v
      (generatedNinthLowerSpinPackedPrefixIndex a i) =
        (if a.val.testBit k.val then (-1 : ℤ) else 1) *
          v (generatedNinthLowerSpinPackedPrefixIndex a i) +
            v (generatedNinthLowerSpinPackedPrefixIndex
              (generatedNinthLowerSpinPackedPrefixXor k a) i) := by
  unfold generatedNinthLowerSpinTensorFourierInteger
  rw [prefix_testBit, prefix_xor]

/-- A complete packed source coordinate is exactly its original signed nine-bit digit. -/
theorem generatedNinth_lower_spin_packed_prefix_coordinate
    (w : Fin 16 → Fin 16 → ℕ) (a : Fin 256) (i : Fin 16) :
    generatedNinthLowerSpinTensorPackedCoordinate w
      (generatedNinthLowerSpinPackedPrefixIndex a i) =
        generatedRootEightPackedSignedDigit
          (w ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩) i := by
  have hrow : (a.val * 16 + i.val) / 256 = a.val / 16 := by omega
  have hword : (a.val * 16 + i.val) / 16 % 16 = a.val % 16 := by omega
  have hslot : (a.val * 16 + i.val) % 16 = i.val := by omega
  have hp : 512 ^ i.val = 2 ^ (9 * i.val) := by rw [pow_mul]; norm_num
  dsimp only [generatedNinthLowerSpinTensorPackedCoordinate,
    generatedNinthLowerSpinPackedPrefixIndex, generatedNinthLowerSpinTensorDecode,
    generatedRootEightPackedSignedDigit]
  simp only [hrow, hword, hslot, hp]

/-- The actual high Fourier pair equals its four full original signed source digits. -/
theorem generatedNinth_lower_spin_packed_high_pair_expansion
    (w : Fin 16 → Fin 16 → ℕ) (k l : Fin 8) (hkl : k ≠ l)
    (a : Fin 256) (i : Fin 16) :
    generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit k)
      (generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit l)
        (generatedNinthLowerSpinTensorPackedCoordinate w))
          (generatedNinthLowerSpinPackedPrefixIndex a i) =
      ∑ z : Fin 4, generatedNinthLowerSpinPackedHighCoefficients k l a z *
        generatedRootEightPackedSignedDigit
          (generatedNinthLowerSpinPackedHighSources
            (fun b => w ⟨b.val / 16, by omega⟩
              ⟨b.val % 16, Nat.mod_lt _ (by decide)⟩) k l a z) i := by
  rw [fourier_prefix, fourier_prefix, fourier_prefix]
  rw [prefix_xor_testBit k l hkl]
  simp only [generatedNinth_lower_spin_packed_prefix_coordinate]
  simp [generatedNinthLowerSpinPackedHighCoefficients,
    generatedNinthLowerSpinPackedHighSources, Fin.sum_univ_succ]
  split_ifs <;> ring

/-- Complete word-slot equations imply all original 4096 actual Fourier coordinates. -/
theorem generatedNinth_lower_spin_packed_high_pair_of_coordinates
    (w t : Fin 16 → Fin 16 → ℕ) (k l : Fin 8) (hkl : k ≠ l)
    (h : ∀ a : Fin 256, ∀ i : Fin 16,
      (∑ z : Fin 4, generatedNinthLowerSpinPackedHighCoefficients k l a z *
        generatedRootEightPackedSignedDigit
          (generatedNinthLowerSpinPackedHighSources
            (fun b => w ⟨b.val / 16, by omega⟩
              ⟨b.val % 16, Nat.mod_lt _ (by decide)⟩) k l a z) i) =
        2 * generatedRootEightPackedSignedDigit
          (t ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩) i) :
    ∀ n : Fin 4096,
      generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit k)
        (generatedNinthLowerSpinTensorFourierInteger (generatedNinthLowerSpinPackedHighBit l)
          (generatedNinthLowerSpinTensorPackedCoordinate w)) n =
        2 * generatedNinthLowerSpinTensorPackedCoordinate t n := by
  intro n
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have hn : generatedNinthLowerSpinPackedPrefixIndex a i = n := by
    apply Fin.ext
    dsimp [generatedNinthLowerSpinPackedPrefixIndex, a, i]
    omega
  rw [← hn, generatedNinth_lower_spin_packed_high_pair_expansion w k l hkl,
    generatedNinth_lower_spin_packed_prefix_coordinate]
  exact h a i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
