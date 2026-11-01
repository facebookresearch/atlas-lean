/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPacked

/-! # Fast evaluation of mask data and preferred masks

Kernel-fast replacements, with equality proofs, for the evaluators of
`GeneratedAxisGlobalIdentShortMask`/`ShortSparse`: table readers by shifts instead of division by
powers of two, the binary column map by a byte spread table, a bitwise selection and an
exclusive-or fold over packed fields (instead of 24-step list loops), and the central bit by the
identity `phase(v) = ⟨R v, v⟩`.  Equalities: `QMaskP.stepP_eq`, `shortMaskF_eq`,
`shortCheckF_eq`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-! ## Exclusive-or over ranges and folds -/

/-- Exclusive or of `f 0, …, f (n-1)`. -/
def xorRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => xorRange f n ^^^ f n

theorem xorRange_xor (f g : ℕ → ℕ) : ∀ n,
    xorRange (fun i => f i ^^^ g i) n = xorRange f n ^^^ xorRange g n
  | 0 => by simp [xorRange]
  | n + 1 => by
    simp only [xorRange, xorRange_xor f g n]
    ac_rfl

theorem xorRange_add (f : ℕ → ℕ) (m : ℕ) : ∀ n,
    xorRange f (m + n) = xorRange f m ^^^ xorRange (fun i => f (m + i)) n
  | 0 => by simp [xorRange]
  | n + 1 => by
    rw [← Nat.add_assoc, xorRange, xorRange_add f m n, xorRange, Nat.xor_assoc]

theorem xorRange_succ' (f : ℕ → ℕ) : ∀ n,
    xorRange f (n + 1) = f 0 ^^^ xorRange (fun i => f (i + 1)) n
  | 0 => by simp [xorRange]
  | n + 1 => by rw [xorRange, xorRange_succ' f n, xorRange, Nat.xor_assoc]

theorem xorRange_congr (f g : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, f i = g i) :
    xorRange f n = xorRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem xorRange_zero (n : ℕ) : xorRange (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorRange, ih]

/-- Fields below the modulus are unchanged by reduction. -/
theorem fld_mod (w X n i : ℕ) (hi : i < n) : fld w (X % 2 ^ (w * n)) i = fld w X i := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, testBit_fld, Nat.testBit_mod_two_pow]
  by_cases hb : b < w
  · have : w * i + b < w * n := by
      have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left w hi
      rw [Nat.mul_succ] at this
      omega
    simp [hb, this]
  · simp [hb]

/-- Masking by a block of ones is reduction. -/
theorem and_ones_eq_mod (X s : ℕ) : X &&& ((1 <<< s) - 1) = X % 2 ^ s := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]

/-- Halving exclusive-or fold of `2^K` fields of width `w`. -/
def xorFoldF (w : ℕ) : ℕ → ℕ → ℕ
  | 0, X => X &&& ((1 <<< w) - 1)
  | K + 1, X => xorFoldF w K ((X ^^^ (X >>> (w * 2 ^ K))) &&& ((1 <<< (w * 2 ^ K)) - 1))

/-- The fold is the exclusive or of all `2^K` fields. -/
theorem xorFoldF_spec (w : ℕ) : ∀ (K X : ℕ), xorFoldF w K X = xorRange (fld w X) (2 ^ K)
  | 0, X => by
    simp only [xorFoldF, and_ones_eq_mod, pow_zero, xorRange, Nat.zero_xor]
    rw [fld_zero_right]
  | K + 1, X => by
    rw [xorFoldF, xorFoldF_spec w K, and_ones_eq_mod]
    have h2 : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by ring
    rw [h2, xorRange_add, ← xorRange_xor]
    apply xorRange_congr
    intro i hi
    rw [fld_mod w _ (2 ^ K) i hi, fld_xor, fld_shiftRight, Nat.add_comm i (2 ^ K)]

/-- List mask sums are exclusive ors over ranges. -/
theorem maskSum_ofFn (n : ℕ) (f : Fin n → ℕ) :
    monsterCo1GeometryBinaryMaskSum (List.ofFn f) =
      xorRange (fun i => if h : i < n then f ⟨i, h⟩ else 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, monsterCo1GeometryBinaryMaskSum, ih, Nat.xor_eq, xorRange_succ']
    simp only [Nat.zero_lt_succ, ↓reduceDIte, Fin.zero_eta]
    congr 1
    apply xorRange_congr
    intro i hi
    have hi'' : i + 1 < n + 1 := by omega
    simp only [hi, hi'', ↓reduceDIte]
    rfl

/-- Spread masks of all bytes: entry `x` has field `k` (24 bits) full iff bit `k` of `x`. -/
def identSpreadTable : ℕ :=
    0x000000000000000000ffffff000000000000000000000000000000000000000000000000 |||
    (0x000000000000000000000000000000000000ffffff000000000000000000000000000000 <<< 288) |||
    (0x000000ffffff000000000000000000000000000000000000000000000000ffffffffffff <<< 576) |||
    (0x000000000000000000000000000000ffffff000000ffffff000000000000000000000000 <<< 864) |||
    (0x000000ffffffffffffffffff000000000000000000000000000000ffffffffffff000000 <<< 1152) |||
    (0x000000000000000000000000ffffff000000000000000000000000000000000000000000 <<< 1440) |||
    (0xffffff000000ffffff000000000000000000000000000000ffffff000000000000ffffff <<< 1728) |||
    (0x000000000000000000000000ffffff000000ffffffffffff000000000000000000000000 <<< 2016) |||
    (0xffffffffffff000000ffffff000000000000000000000000ffffffffffff000000000000 <<< 2304) |||
    (0x000000000000000000000000ffffffffffffffffff000000000000000000000000000000 <<< 2592) |||
    (0x000000000000000000000000000000000000000000000000ffffffffffffffffffffffff <<< 2880) |||
    (0x000000000000000000ffffff000000000000000000ffffff000000000000000000ffffff <<< 3168) |||
    (0x000000000000ffffffffffff000000000000000000ffffff000000000000ffffff000000 <<< 3456) |||
    (0x000000000000000000ffffff000000ffffff000000000000000000000000000000ffffff <<< 3744) |||
    (0x000000ffffffffffff000000000000000000000000ffffff000000ffffff000000ffffff <<< 4032) |||
    (0x000000000000000000ffffff000000ffffffffffffffffff000000000000000000ffffff <<< 4320) |||
    (0xffffff000000000000ffffff000000000000000000ffffffffffff000000000000000000 <<< 4608) |||
    (0x000000000000000000ffffffffffff000000ffffff000000000000000000000000ffffff <<< 4896) |||
    (0xffffffffffff000000000000000000000000000000ffffffffffff000000ffffffffffff <<< 5184) |||
    (0x000000000000000000ffffffffffffffffff000000ffffff000000000000000000ffffff <<< 5472) |||
    (0xffffffffffffffffffffffff000000000000000000ffffffffffffffffffffffff000000 <<< 5760) |||
    (0x000000000000ffffff000000000000000000000000000000000000000000000000ffffff <<< 6048) |||
    (0x000000000000ffffff000000000000000000ffffff000000000000000000000000ffffff <<< 6336) |||
    (0x000000000000ffffff000000000000000000ffffffffffff000000000000ffffff000000 <<< 6624) |||
    (0x000000ffffff000000ffffff000000000000ffffff000000000000ffffff000000000000 <<< 6912) |||
    (0x000000000000ffffff000000000000ffffffffffff000000000000000000ffffff000000 <<< 7200) |||
    (0xffffff000000000000000000000000000000ffffff000000000000ffffffffffffffffff <<< 7488) |||
    (0x000000000000ffffff000000ffffff000000000000ffffff000000000000ffffff000000 <<< 7776) |||
    (0xffffff000000ffffffffffff000000000000ffffff000000ffffff000000ffffff000000 <<< 8064) |||
    (0x000000000000ffffff000000ffffffffffff000000000000000000000000ffffff000000 <<< 8352) |||
    (0xffffffffffffffffff000000000000000000ffffff000000ffffffffffff000000ffffff <<< 8640) |||
    (0x000000000000ffffff000000ffffffffffffffffffffffff000000000000ffffff000000 <<< 8928) |||
    (0x000000000000000000ffffff000000000000ffffffffffff000000000000000000000000 <<< 9216) |||
    (0x000000000000ffffffffffff000000000000ffffff000000000000000000ffffffffffff <<< 9504) |||
    (0x000000ffffff000000000000000000000000ffffffffffff000000000000ffffffffffff <<< 9792) |||
    (0x000000000000ffffffffffff000000ffffff000000ffffff000000000000ffffffffffff <<< 10080) |||
    (0x000000ffffffffffffffffff000000000000ffffffffffff000000ffffffffffff000000 <<< 10368) |||
    (0x000000000000ffffffffffffffffff000000000000000000000000000000ffffffffffff <<< 10656) |||
    (0xffffff000000ffffff000000000000000000ffffffffffffffffff000000000000ffffff <<< 10944) |||
    (0x000000000000ffffffffffffffffff000000ffffffffffff000000000000ffffffffffff <<< 11232) |||
    (0xffffffffffff000000ffffff000000000000ffffffffffffffffffffffff000000000000 <<< 11520) |||
    (0x000000000000ffffffffffffffffffffffffffffff000000000000000000ffffffffffff <<< 11808) |||
    (0x000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffff <<< 12096) |||
    (0x000000ffffff000000000000000000000000000000ffffff000000ffffff000000000000 <<< 12384) |||
    (0x000000000000ffffffffffff000000ffffff000000000000000000000000ffffff000000 <<< 12672) |||
    (0x000000ffffff000000000000000000ffffff000000000000000000ffffff000000000000 <<< 12960) |||
    (0x000000ffffffffffff000000000000ffffff000000000000000000ffffff000000ffffff <<< 13248) |||
    (0x000000ffffff000000000000000000ffffffffffffffffff000000ffffff000000000000 <<< 13536) |||
    (0xffffff000000000000ffffff000000ffffff000000000000ffffff000000000000000000 <<< 13824) |||
    (0x000000ffffff000000000000ffffff000000ffffff000000000000ffffff000000000000 <<< 14112) |||
    (0xffffffffffff000000000000000000ffffff000000000000ffffff000000ffffffffffff <<< 14400) |||
    (0x000000ffffff000000000000ffffffffffff000000ffffff000000ffffff000000000000 <<< 14688) |||
    (0xffffffffffffffffffffffff000000ffffff000000000000ffffffffffffffffff000000 <<< 14976) |||
    (0x000000ffffff000000ffffff000000000000000000000000000000ffffff000000000000 <<< 15264) |||
    (0x000000000000ffffff000000000000ffffff000000ffffff000000000000000000ffffff <<< 15552) |||
    (0x000000ffffff000000ffffff000000000000ffffffffffff000000ffffff000000ffffff <<< 15840) |||
    (0x000000ffffff000000ffffff000000ffffff000000ffffff000000ffffff000000000000 <<< 16128) |||
    (0x000000ffffff000000ffffff000000ffffffffffff000000000000ffffff000000ffffff <<< 16416) |||
    (0xffffff000000000000000000000000ffffff000000ffffff000000ffffffffffffffffff <<< 16704) |||
    (0x000000ffffff000000ffffffffffff000000000000ffffff000000ffffff000000ffffff <<< 16992) |||
    (0xffffff000000ffffffffffff000000ffffff000000ffffffffffff000000ffffff000000 <<< 17280) |||
    (0x000000ffffff000000ffffffffffffffffff000000000000000000ffffff000000ffffff <<< 17568) |||
    (0xffffffffffffffffff000000000000ffffff000000ffffffffffffffffff000000ffffff <<< 17856) |||
    (0x000000ffffff000000ffffffffffffffffffffffffffffff000000ffffff000000ffffff <<< 18144) |||
    (0x000000000000000000ffffff000000ffffffffffff000000000000000000000000000000 <<< 18432) |||
    (0x000000ffffffffffff000000000000000000ffffff000000000000ffffffffffff000000 <<< 18720) |||
    (0x000000ffffff000000000000000000ffffffffffff000000000000000000ffffffffffff <<< 19008) |||
    (0x000000ffffffffffff000000000000ffffff000000ffffff000000ffffffffffff000000 <<< 19296) |||
    (0x000000ffffffffffffffffff000000ffffffffffff000000000000ffffffffffff000000 <<< 19584) |||
    (0x000000ffffffffffff000000ffffff000000000000000000000000ffffffffffff000000 <<< 19872) |||
    (0xffffff000000ffffff000000000000ffffffffffff000000ffffff000000000000ffffff <<< 20160) |||
    (0x000000ffffffffffff000000ffffff000000ffffffffffff000000ffffffffffff000000 <<< 20448) |||
    (0xffffffffffff000000ffffff000000ffffffffffff000000ffffffffffff000000000000 <<< 20736) |||
    (0x000000ffffffffffff000000ffffffffffffffffff000000000000ffffffffffff000000 <<< 21024) |||
    (0x000000000000000000000000000000ffffffffffff000000ffffffffffffffffffffffff <<< 21312) |||
    (0x000000ffffffffffffffffff000000000000000000ffffff000000ffffffffffffffffff <<< 21600) |||
    (0x000000000000ffffffffffff000000ffffffffffffffffff000000000000ffffff000000 <<< 21888) |||
    (0x000000ffffffffffffffffff000000ffffff000000000000000000ffffffffffffffffff <<< 22176) |||
    (0x000000ffffffffffff000000000000ffffffffffffffffff000000ffffff000000ffffff <<< 22464) |||
    (0x000000ffffffffffffffffff000000ffffffffffffffffff000000ffffffffffffffffff <<< 22752) |||
    (0xffffff000000000000ffffff000000ffffffffffffffffffffffff000000000000000000 <<< 23040) |||
    (0x000000ffffffffffffffffffffffff000000ffffff000000000000ffffffffffffffffff <<< 23328) |||
    (0xffffffffffff000000000000000000ffffffffffffffffffffffff000000ffffffffffff <<< 23616) |||
    (0x000000ffffffffffffffffffffffffffffff000000ffffff000000ffffffffffffffffff <<< 23904) |||
    (0xffffffffffffffffffffffff000000ffffffffffffffffffffffffffffffffffff000000 <<< 24192) |||
    (0xffffff000000000000000000000000000000000000000000000000ffffffffffffffffff <<< 24480) |||
    (0x000000000000ffffff000000ffffff000000000000000000000000000000000000ffffff <<< 24768) |||
    (0xffffff000000000000000000000000000000ffffffffffffffffff000000000000000000 <<< 25056) |||
    (0x000000ffffff000000ffffffffffff000000000000000000000000ffffff000000000000 <<< 25344) |||
    (0xffffff000000000000000000000000ffffffffffff000000ffffff000000000000000000 <<< 25632) |||
    (0xffffff000000000000000000ffffff000000000000000000000000ffffffffffffffffff <<< 25920) |||
    (0xffffff000000000000000000ffffff000000000000ffffffffffff000000000000000000 <<< 26208) |||
    (0xffffff000000ffffffffffffffffff000000000000000000ffffff000000ffffff000000 <<< 26496) |||
    (0xffffff000000000000000000ffffffffffff000000000000ffffff000000000000000000 <<< 26784) |||
    (0xffffffffffffffffff000000ffffff000000000000000000ffffffffffff000000ffffff <<< 27072) |||
    (0xffffff000000000000000000ffffffffffffffffffffffffffffff000000000000000000 <<< 27360) |||
    (0x000000000000000000ffffffffffff000000000000ffffff000000000000000000000000 <<< 27648) |||
    (0xffffff000000000000ffffff000000000000ffffff000000ffffff000000000000ffffff <<< 27936) |||
    (0x000000ffffff000000000000ffffff000000000000ffffff000000000000ffffffffffff <<< 28224) |||
    (0xffffff000000000000ffffff000000ffffff000000ffffffffffff000000000000ffffff <<< 28512) |||
    (0x000000ffffffffffffffffffffffff000000000000ffffff000000ffffffffffff000000 <<< 28800) |||
    (0xffffff000000000000ffffffffffff000000000000000000ffffff000000000000ffffff <<< 29088) |||
    (0xffffff000000ffffff000000ffffff000000000000ffffffffffff000000000000ffffff <<< 29376) |||
    (0xffffff000000000000ffffffffffff000000ffffffffffffffffff000000000000ffffff <<< 29664) |||
    (0xffffffffffff000000ffffffffffff000000000000ffffffffffffffffff000000000000 <<< 29952) |||
    (0xffffff000000000000ffffffffffffffffffffffff000000ffffff000000000000ffffff <<< 30240) |||
    (0x000000000000000000000000ffffff000000000000ffffffffffffffffffffffffffffff <<< 30528) |||
    (0xffffff000000ffffff000000000000000000000000ffffffffffff000000ffffff000000 <<< 30816) |||
    (0x000000000000ffffffffffffffffff000000ffffff000000000000000000ffffff000000 <<< 31104) |||
    (0xffffff000000ffffff000000000000ffffff000000000000ffffff000000ffffff000000 <<< 31392) |||
    (0x000000ffffffffffff000000ffffff000000ffffff000000000000ffffff000000ffffff <<< 31680) |||
    (0xffffff000000ffffff000000000000ffffffffffffffffffffffff000000ffffff000000 <<< 31968) |||
    (0xffffff000000000000ffffffffffff000000ffffff000000ffffff000000000000000000 <<< 32256) |||
    (0xffffff000000ffffff000000ffffff000000ffffff000000ffffff000000ffffff000000 <<< 32544) |||
    (0xffffffffffff000000000000ffffff000000ffffff000000ffffff000000ffffffffffff <<< 32832) |||
    (0xffffff000000ffffff000000ffffffffffff000000ffffffffffff000000ffffff000000 <<< 33120) |||
    (0xffffffffffffffffffffffffffffff000000ffffff000000ffffffffffffffffff000000 <<< 33408) |||
    (0xffffff000000ffffffffffff000000000000000000000000ffffff000000ffffff000000 <<< 33696) |||
    (0x000000000000ffffff000000ffffff000000ffffffffffff000000000000000000ffffff <<< 33984) |||
    (0xffffff000000ffffffffffff000000000000ffffffffffffffffff000000ffffffffffff <<< 34272) |||
    (0x000000ffffff000000ffffffffffff000000ffffffffffff000000ffffff000000000000 <<< 34560) |||
    (0xffffff000000ffffffffffff000000ffffffffffff000000ffffff000000ffffffffffff <<< 34848) |||
    (0xffffff000000000000000000ffffff000000ffffffffffff000000ffffffffffffffffff <<< 35136) |||
    (0xffffff000000ffffffffffffffffff000000000000ffffffffffff000000ffffffffffff <<< 35424) |||
    (0xffffff000000ffffffffffffffffff000000ffffffffffffffffff000000ffffff000000 <<< 35712) |||
    (0xffffff000000ffffffffffffffffffffffff000000000000ffffff000000ffffffffffff <<< 36000) |||
    (0xffffffffffffffffff000000ffffff000000ffffffffffffffffffffffff000000ffffff <<< 36288) |||
    (0xffffff000000ffffffffffffffffffffffffffffffffffffffffff000000ffffffffffff <<< 36576) |||
    (0x000000000000000000ffffffffffffffffff000000000000000000000000000000000000 <<< 36864) |||
    (0xffffffffffff000000000000000000000000ffffff000000ffffffffffff000000000000 <<< 37152) |||
    (0x000000ffffff000000000000ffffffffffff000000000000000000000000ffffffffffff <<< 37440) |||
    (0xffffffffffff000000000000000000ffffff000000ffffffffffffffffff000000000000 <<< 37728) |||
    (0x000000ffffffffffffffffffffffffffffff000000000000000000ffffffffffff000000 <<< 38016) |||
    (0xffffffffffff000000000000ffffff000000000000000000ffffffffffff000000000000 <<< 38304) |||
    (0xffffff000000ffffff000000ffffffffffff000000000000ffffff000000000000ffffff <<< 38592) |||
    (0xffffffffffff000000000000ffffff000000ffffffffffffffffffffffff000000000000 <<< 38880) |||
    (0xffffffffffff000000ffffffffffffffffff000000000000ffffffffffff000000000000 <<< 39168) |||
    (0xffffffffffff000000000000ffffffffffffffffff000000ffffffffffff000000000000 <<< 39456) |||
    (0x000000000000000000000000ffffffffffff000000000000ffffffffffffffffffffffff <<< 39744) |||
    (0xffffffffffff000000ffffff000000000000000000ffffffffffffffffff000000ffffff <<< 40032) |||
    (0x000000000000ffffffffffffffffffffffff000000ffffff000000000000ffffff000000 <<< 40320) |||
    (0xffffffffffff000000ffffff000000ffffff000000000000ffffffffffff000000ffffff <<< 40608) |||
    (0x000000ffffffffffff000000ffffffffffff000000ffffff000000ffffff000000ffffff <<< 40896) |||
    (0xffffffffffff000000ffffff000000ffffffffffffffffffffffffffffff000000ffffff <<< 41184) |||
    (0xffffff000000000000ffffffffffffffffff000000ffffffffffff000000000000000000 <<< 41472) |||
    (0xffffffffffff000000ffffffffffff000000ffffff000000ffffffffffff000000ffffff <<< 41760) |||
    (0xffffffffffff000000000000ffffffffffff000000ffffffffffff000000ffffffffffff <<< 42048) |||
    (0xffffffffffff000000ffffffffffffffffff000000ffffffffffffffffff000000ffffff <<< 42336) |||
    (0xffffffffffffffffffffffffffffffffffff000000ffffffffffffffffffffffff000000 <<< 42624) |||
    (0xffffffffffffffffff000000000000000000000000000000ffffffffffff000000ffffff <<< 42912) |||
    (0x000000000000ffffff000000ffffffffffffffffff000000000000000000000000ffffff <<< 43200) |||
    (0xffffffffffffffffff000000000000000000ffffffffffffffffffffffffffffff000000 <<< 43488) |||
    (0x000000ffffff000000ffffffffffffffffffffffff000000000000ffffff000000000000 <<< 43776) |||
    (0xffffffffffffffffff000000000000ffffffffffff000000ffffffffffffffffff000000 <<< 44064) |||
    (0xffffff000000000000000000ffffffffffffffffff000000000000ffffffffffffffffff <<< 44352) |||
    (0xffffffffffffffffff000000ffffff000000000000ffffffffffffffffffffffff000000 <<< 44640) |||
    (0xffffff000000ffffffffffffffffffffffffffffff000000ffffff000000ffffff000000 <<< 44928) |||
    (0xffffffffffffffffff000000ffffffffffff000000000000ffffffffffffffffff000000 <<< 45216) |||
    (0xffffffffffffffffff000000ffffffffffffffffff000000ffffffffffff000000ffffff <<< 45504) |||
    (0xffffffffffffffffff000000ffffffffffffffffffffffffffffffffffffffffff000000 <<< 45792) |||
    (0x000000000000000000ffffffffffffffffffffffffffffff000000000000000000000000 <<< 46080) |||
    (0xffffffffffffffffffffffff000000000000ffffff000000ffffffffffffffffffffffff <<< 46368) |||
    (0x000000ffffff000000000000ffffffffffffffffffffffff000000000000ffffffffffff <<< 46656) |||
    (0xffffffffffffffffffffffff000000ffffff000000ffffffffffffffffffffffffffffff <<< 46944) |||
    (0x000000ffffffffffffffffffffffffffffffffffffffffff000000ffffffffffff000000 <<< 47232) |||
    (0xffffffffffffffffffffffffffffff000000000000000000ffffffffffffffffffffffff <<< 47520) |||
    (0xffffff000000ffffff000000ffffffffffffffffffffffffffffff000000000000ffffff <<< 47808) |||
    (0xffffffffffffffffffffffffffffff000000ffffffffffffffffffffffffffffffffffff <<< 48096) |||
    (0xffffffffffff000000ffffffffffffffffffffffffffffffffffffffffff000000000000 <<< 48384) |||
    (0xffffffffffffffffffffffffffffffffffffffffff000000ffffffffffffffffffffffff <<< 48672) |||
    (0xffffffffffffffffffffffffffffffffffffffffffffffff <<< 48960)

/-- The cocode columns of the 24 coordinates, in 24-bit fields. -/
def identCocodeColsP : ℕ :=
    0x00083e00081e00082e000c0e0008cf00084f00088f000c0f000f00000d00000e00000800 |||
    (0x9b7000ad7000b67000c07000a7b000b9b0009eb000c0b000bfd00095d000aad000c0d <<< 288)

/-! ## Spread table and selection -/

/-- Fields of a number below `2^(w n)` vanish from index `n` on. -/
theorem fld_eq_zero_of_lt (w P n i : ℕ) (hP : P < 2 ^ (w * n)) (hi : n ≤ i) : fld w P i = 0 := by
  unfold fld
  have : P / 2 ^ (w * i) = 0 := by
    apply Nat.div_eq_of_lt
    calc P < 2 ^ (w * n) := hP
      _ ≤ 2 ^ (w * i) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hi)
  rw [this, Nat.zero_mod]

/-- The spread mask of a byte: eight 24-bit fields. -/
def spreadByteF (x : ℕ) : ℕ := (identSpreadTable >>> (192 * x)) &&& ((1 <<< 192) - 1)

/-- Spread masks fit in eight fields. -/
theorem spreadByteF_lt (x : ℕ) : spreadByteF x < 2 ^ (24 * 8) := by
  unfold spreadByteF
  rw [and_ones_eq_mod]
  exact Nat.mod_lt _ (by positivity)

set_option maxRecDepth 100000 in
/-- The spread table: field `k` of entry `x` is full exactly when bit `k` of `x` is set. -/
theorem spreadByteF_spec : ∀ x : Fin 256, ∀ k : Fin 8,
    fld 24 (spreadByteF x.val) k.val = if x.val.testBit k.val then 2 ^ 24 - 1 else 0 := by
  decide +kernel

/-- All fields of a spread byte. -/
theorem fld_spreadByteF (x : ℕ) (hx : x < 256) (j : ℕ) :
    fld 24 (spreadByteF x) j = if j < 8 ∧ x.testBit j then 2 ^ 24 - 1 else 0 := by
  by_cases hj : j < 8
  · rw [spreadByteF_spec ⟨x, hx⟩ ⟨j, hj⟩]
    simp [hj]
  · rw [fld_eq_zero_of_lt 24 _ 8 j (spreadByteF_lt x) (by omega)]
    simp [hj]

/-- The spread mask of a 24-bit selection. -/
def spreadV (v : ℕ) : ℕ :=
  spreadByteF (v &&& 255) ||| (spreadByteF ((v >>> 8) &&& 255) <<< (24 * 8)) |||
    (spreadByteF ((v >>> 16) &&& 255) <<< (24 * 16))

/-- Fields of the spread mask. -/
theorem fld_spreadV (v i : ℕ) :
    fld 24 (spreadV v) i = if i < 24 ∧ v.testBit i then 2 ^ 24 - 1 else 0 := by
  have hb : ∀ s, (v >>> s) &&& 255 < 256 := fun s =>
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hbit : ∀ s j, j < 8 → ((v >>> s) &&& 255).testBit j = v.testBit (s + j) := by
    intro s j hj
    rw [Nat.testBit_and, Nat.testBit_shiftRight]
    have : (255 : ℕ).testBit j = true := by
      have h255 : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
      rw [h255, Nat.testBit_two_pow_sub_one]
      simp [hj]
    rw [this, Bool.and_true]
  have h0 : v &&& 255 = (v >>> 0) &&& 255 := by simp
  unfold spreadV
  rw [fld_lor, fld_lor, fld_shiftLeft, fld_shiftLeft, h0,
    fld_spreadByteF _ (hb 0), fld_spreadByteF _ (hb 8), fld_spreadByteF _ (hb 16)]
  by_cases h1 : i < 8
  · have : ¬ 8 ≤ i := by omega
    have : ¬ 16 ≤ i := by omega
    simp only [true_and, hbit 0 i h1, Nat.zero_add, show i < 24 by omega, *, ↓reduceIte,
      Nat.or_zero]
  · by_cases h2 : i < 16
    · have h8 : 8 ≤ i := by omega
      have : ¬ 16 ≤ i := by omega
      have hi8 : i - 8 < 8 := by omega
      simp only [false_and, ↓reduceIte, true_and, hbit 8 (i - 8) hi8,
        show 8 + (i - 8) = i by omega, show i < 24 by omega, *, Nat.zero_or, Nat.or_zero]
    · by_cases h3 : i < 24
      · have h8 : 8 ≤ i := by omega
        have h16 : 16 ≤ i := by omega
        have hi8 : ¬ i - 8 < 8 := by omega
        have hi16 : i - 16 < 8 := by omega
        simp only [h1, false_and, ↓reduceIte, h8, hi8, h16, hi16, true_and,
          hbit 16 (i - 16) hi16, show 16 + (i - 16) = i by omega, h3, Nat.zero_or]
      · have h8 : 8 ≤ i := by omega
        have h16 : 16 ≤ i := by omega
        have hi8 : ¬ i - 8 < 8 := by omega
        have hi16 : ¬ i - 16 < 8 := by omega
        simp only [h1, false_and, ↓reduceIte, h8, hi8, h16, hi16, h3, Nat.zero_or]

/-- Exclusive or of the packed columns selected by the bits of `v`. -/
def selXorF (C v : ℕ) : ℕ := xorFoldF 24 5 (C &&& spreadV v)

/-- Fields of a number without bits from position `576` on vanish from index `24` on. -/
theorem fld_zero_of_shift (C i : ℕ) (hC : C >>> 576 = 0) (hi : 24 ≤ i) : fld 24 C i = 0 := by
  unfold fld
  have h0 : C / 2 ^ (24 * i) = 0 := by
    have h1 : 24 * i = 576 + (24 * i - 576) := by omega
    rw [Nat.shiftRight_eq_div_pow] at hC
    rw [h1, pow_add, ← Nat.div_div_eq_div_mul, hC, Nat.zero_div]
  rw [h0, Nat.zero_mod]

/-- Selection is the exclusive or of the selected fields (columns below `24`). -/
theorem selXorF_spec (C v : ℕ) (hC : C >>> 576 = 0) :
    selXorF C v = xorRange (fun i => if v.testBit i then fld 24 C i else 0) 24 := by
  unfold selXorF
  rw [xorFoldF_spec]
  have h32 : (2 : ℕ) ^ 5 = 24 + 8 := by norm_num
  rw [h32, xorRange_add]
  have hz : xorRange (fun i => fld 24 (C &&& spreadV v) (24 + i)) 8 = 0 := by
    rw [xorRange_congr _ (fun _ => 0) 8 (fun i _ => by
      rw [fld_land, fld_zero_of_shift C (24 + i) hC (by omega), Nat.zero_and])]
    exact xorRange_zero 8
  rw [hz, Nat.xor_zero]
  apply xorRange_congr
  intro i hi
  rw [fld_land, fld_spreadV]
  by_cases hv : v.testBit i
  · simp only [hi, hv, and_self, ↓reduceIte]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt 24 C i)
  · simp [hv]

/-- Selection computes the binary column map. -/
theorem selXorF_eq (C v : ℕ) (hC : C >>> 576 = 0) :
    selXorF C v = generatedAxisGlobalQMaskVector (fun i => fld 24 C i.val) v := by
  rw [selXorF_spec C v hC, generatedAxisGlobalQMaskVector, maskSum_ofFn]
  apply xorRange_congr
  intro i hi
  simp [hi]

/-! ## Packed mask data -/

/-- Mask data with packed columns and rows (24-bit fields). -/
structure QMaskP where
  /-- Packed binary columns. -/
  colsP : ℕ
  /-- Packed correction rows. -/
  rowsP : ℕ
  /-- Central coefficients. -/
  coeff : ℕ

/-- The mask data of packed mask data. -/
def QMaskP.toData (d : QMaskP) : QMaskData :=
  ⟨fun i => fld 24 d.colsP i.val, fun i => fld 24 d.rowsP i.val, d.coeff⟩

/-- Packed data fit in 24 fields. -/
def QMaskP.ok (d : QMaskP) : Bool := (d.colsP >>> 576 == 0) && (d.rowsP >>> 576 == 0)

/-- The fast evaluation step of packed mask data. -/
def QMaskP.stepP (d : QMaskP) (p : ℕ × Bool) : ℕ × Bool :=
  (selXorF d.colsP p.1,
    xor p.2 ((identDot24 (selXorF d.rowsP p.1 ^^^ d.coeff) p.1).testBit 0))

/-- Boolean casts are injective. -/
theorem golayBooleanCast_inj (a b : Bool) (h : golayBooleanCast a = golayBooleanCast b) :
    a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

/-- Decoded binary column map. -/
theorem decode_qmaskVector (cols : Fin 24 → ℕ) (v : ℕ) (k : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalQMaskVector cols v) k =
      ∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode (n := 24) v i *
        monsterCo1GeometryBinaryMaskDecode (cols i) k := by
  unfold generatedAxisGlobalQMaskVector
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply, monsterCo1GeometryBinaryMaskDecode]
  split_ifs <;> simp_all

/-- The central bit is the dot product of the selected rows plus coefficients with the mask. -/
theorem identQCentral_bit (rows : Fin 24 → ℕ) (coeff v : ℕ) :
    (identQCentral rows coeff v).testBit 0 =
      (identDot24 (generatedAxisGlobalQMaskVector rows v ^^^ coeff) v).testBit 0 := by
  apply golayBooleanCast_inj
  rw [identQCentral_eq, identDot24_eq]
  unfold generatedAxisGlobalQMaskCentral
  rw [Nat.xor_eq, Nat.testBit_xor, golayBooleanCast_xor_eq]
  have hp := generatedAxisGlobalQMaskPhase_polynomial rows v
  have hc := monsterCo1GeometryBinaryMaskDot_decode 24 coeff v
  have hd := monsterCo1GeometryBinaryMaskDot_decode 24
    (generatedAxisGlobalQMaskVector rows v ^^^ coeff) v
  change golayBooleanCast _ = _ at hp hc hd
  rw [hp, hc, hd]
  have hx : ∀ k : Fin 24, monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalQMaskVector rows v ^^^ coeff) k =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalQMaskVector rows v) k +
        monsterCo1GeometryBinaryMaskDecode (n := 24) coeff k := by
    intro k
    have := congrFun (monsterCo1GeometryBinaryMaskDecode_xor (n := 24)
      (generatedAxisGlobalQMaskVector rows v) coeff) k
    simpa [Nat.xor_eq] using this
  simp_rw [hx, decode_qmaskVector, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ rfl
  rw [Finset.sum_comm]

/-- The fast step is the step of the unpacked data. -/
theorem QMaskP.stepP_eq (d : QMaskP) (hd : d.ok = true) (p : ℕ × Bool) :
    d.stepP p = d.toData.step p := by
  simp only [QMaskP.ok, Bool.and_eq_true, beq_iff_eq] at hd
  unfold QMaskP.stepP QMaskData.step
  rw [selXorF_eq _ _ hd.1, selXorF_eq _ _ hd.2, identQCentral_bit]
  rfl

/-- Evaluate a word of packed mask data (the head letter acts last). -/
def qmWordP : List QMaskP → ℕ × Bool → ℕ × Bool
  | [], p => p
  | d :: ds, p => d.stepP (qmWordP ds p)

/-- The packed word evaluation is the word evaluation of the unpacked data. -/
theorem qmWordP_eq (ds : List QMaskP) (hds : ds.all QMaskP.ok = true) (p : ℕ × Bool) :
    qmWordP ds p = qmWord (ds.map QMaskP.toData) p := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hds
    simp only [qmWordP, qmWord, List.map_cons, ih hds.2, QMaskP.stepP_eq d hds.1]

/-! ## Fast table readers -/

/-- Shift-and-mask reading is division and reduction. -/
theorem shift_and_eq (T k w : ℕ) : (T >>> k) &&& (2 ^ w - 1) = T / 2 ^ k % 2 ^ w := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-- Fast octad code reader. -/
def octCodeF (o : ℕ) : ℕ := (identOctCodeTable >>> (12 * o)) &&& 4095

/-- Fast octad theta reader. -/
def octThetaF (o : ℕ) : ℕ := (identOctThetaTable >>> (12 * o)) &&& 4095

/-- Fast octad coordinate reader. -/
def octCoordF (o k : ℕ) : ℕ := (identOctCoordBlock o >>> (5 * (8 * (o % 256) + k))) &&& 31

/-- Fast even mask reader. -/
def evenMaskF (e : ℕ) : ℕ := (identEvenTable >>> (8 * e)) &&& 127

/-- Fast octad Ω bit reader. -/
def octOmegaF (e : ℕ) : ℕ := (identEvenTable >>> (8 * e + 7)) &&& 1

/-- Fast odd theta reader. -/
def oddThetaF (d : ℕ) : ℕ := (identOddBlock d >>> (40 * (d % 256))) &&& 4095

/-- Fast odd codeword reader. -/
def oddCodeF (d : ℕ) : ℕ := (identOddBlock d >>> (40 * (d % 256) + 12)) &&& 16777215

/-- Fast odd weight flag reader. -/
def oddFlagF (d : ℕ) : ℕ := (identOddBlock d >>> (40 * (d % 256) + 36)) &&& 1

/-- Fast first pair coordinate reader. -/
def pairFstF (p : ℕ) : ℕ := (identPairTable >>> (10 * p)) &&& 31

/-- Fast second pair coordinate reader. -/
def pairSndF (p : ℕ) : ℕ := (identPairTable >>> (10 * p + 5)) &&& 31

/-- Fast cocode column reader. -/
def cocodeColF (i : ℕ) : ℕ := (identCocodeColsP >>> (24 * i)) &&& 4095

theorem octCodeF_eq (o : ℕ) : octCodeF o = identOctCode o := by
  unfold octCodeF identOctCode
  rw [show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, shift_and_eq]
  norm_num

theorem octThetaF_eq (o : ℕ) : octThetaF o = identOctTheta o := by
  unfold octThetaF identOctTheta
  rw [show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, shift_and_eq]
  norm_num

theorem octCoordF_eq (o k : ℕ) : octCoordF o k = identOctCoord o k := by
  unfold octCoordF identOctCoord
  rw [show (31 : ℕ) = 2 ^ 5 - 1 by norm_num, shift_and_eq]
  norm_num

theorem evenMaskF_eq (e : ℕ) : evenMaskF e = identEvenMask e := by
  unfold evenMaskF identEvenMask
  rw [show (127 : ℕ) = 2 ^ 7 - 1 by norm_num, shift_and_eq]
  norm_num

theorem octOmegaF_eq (e : ℕ) : octOmegaF e = identOctOmegaBit e := by
  unfold octOmegaF identOctOmegaBit
  rw [show (1 : ℕ) = 2 ^ 1 - 1 by norm_num, shift_and_eq]
  norm_num

theorem oddThetaF_eq (d : ℕ) : oddThetaF d = identOddTheta d := by
  unfold oddThetaF identOddTheta
  rw [show (4095 : ℕ) = 2 ^ 12 - 1 by norm_num, shift_and_eq]
  norm_num

theorem oddCodeF_eq (d : ℕ) : oddCodeF d = identOddCode d := by
  unfold oddCodeF identOddCode
  rw [show (16777215 : ℕ) = 2 ^ 24 - 1 by norm_num, shift_and_eq]

theorem oddFlagF_eq (d : ℕ) : oddFlagF d = identOddWeightFlag d := by
  unfold oddFlagF identOddWeightFlag
  rw [show (1 : ℕ) = 2 ^ 1 - 1 by norm_num, shift_and_eq]
  norm_num

theorem pairFstF_eq (p : ℕ) : pairFstF p = identPairFst p := by
  unfold pairFstF identPairFst
  rw [show (31 : ℕ) = 2 ^ 5 - 1 by norm_num, shift_and_eq]
  norm_num

theorem pairSndF_eq (p : ℕ) : pairSndF p = identPairSnd p := by
  unfold pairSndF identPairSnd
  rw [show (31 : ℕ) = 2 ^ 5 - 1 by norm_num, shift_and_eq]
  norm_num

set_option maxRecDepth 100000 in
/-- The packed cocode columns are the cocode columns. -/
theorem cocodeColF_spec : ∀ i : Fin 24,
    cocodeColF i.val = generatedAxisGlobalCocodeColumnMask i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The fields of the packed cocode columns are the cocode columns. -/
theorem fld_identCocodeColsP : ∀ i : Fin 24,
    fld 24 identCocodeColsP i.val = generatedAxisGlobalCocodeColumnMask i := by
  decide +kernel

/-- The packed cocode columns fit in 24 fields. -/
theorem identCocodeColsP_shift : identCocodeColsP >>> 576 = 0 := by
  decide +kernel

/-- The cocode mask by selection. -/
theorem selXorF_cocode (v : ℕ) : selXorF identCocodeColsP v = generatedAxisGlobalCocodeMask v := by
  rw [selXorF_eq _ _ identCocodeColsP_shift]
  unfold generatedAxisGlobalQMaskVector generatedAxisGlobalCocodeMask
  simp only [fld_identCocodeColsP]

/-! ## Fast preferred masks -/

/-- Fast negative coordinates of a signed octad label. -/
def octNegF (o e : ℕ) : ℕ :=
  (List.finRange 8).foldr (fun (k : Fin 8) (m : ℕ) =>
    (if (evenMaskF e).testBit k.val then 2 ^ (octCoordF o k.val % 24) else 0) ||| m) 0

theorem octNegF_eq (o : Fin 759) (e : Fin 64) : octNegF o.val e.val = identOctNegMask o e := by
  unfold octNegF identOctNegMask identOctCoordFin
  simp only [evenMaskF_eq, octCoordF_eq]

/-- The fast preferred mask of a flat short label. -/
def shortMaskF (j : ℕ) : ℕ :=
  if j < 552 then
    generatedAxisGlobalSourceMaskJoin (if j / 276 % 2 = 0 then 0 else 2048)
      (cocodeColF (pairFstF (j % 276) % 24) ^^^ cocodeColF (pairSndF (j % 276) % 24))
  else if j < 49128 then
    generatedAxisGlobalSourceMaskJoin
      (octCodeF ((j - 552) / 64 % 759) ^^^ 2048 * octOmegaF ((j - 552) % 64))
      (octThetaF ((j - 552) / 64 % 759) ^^^
        selXorF identCocodeColsP (octNegF ((j - 552) / 64 % 759) ((j - 552) % 64)))
  else
    generatedAxisGlobalSourceMaskJoin
      ((j - 49128) / 24 % 2048 ^^^ 2048 * (oddFlagF ((j - 49128) / 24 % 2048) ^^^
        ((oddCodeF ((j - 49128) / 24 % 2048) >>> ((j - 49128) % 24)) &&& 1)))
      (oddThetaF ((j - 49128) / 24 % 2048) ^^^ cocodeColF ((j - 49128) % 24))

/-- The Ω mask of a sum of two bits. -/
theorem omegaMask_bits (f b : ℕ) (hf : f < 2) (hb : b < 2) :
    generatedAxisGlobalOmegaMask ((if f = 0 then 0 else 1) + (if b = 1 then 1 else 0)) =
      2048 * (f ^^^ b) := by
  interval_cases f <;> interval_cases b <;> decide

/-- The fast preferred mask is the preferred mask. -/
theorem shortMaskF_eq (j : ℕ) : shortMaskF j = shortMaskFlat j := by
  unfold shortMaskF shortMaskFlat
  by_cases h1 : j < 552
  · have hd : shortDecode j = Sum.inl (⟨j / 276 % 2, Nat.mod_lt _ (by decide)⟩,
        ⟨j % 276, Nat.mod_lt _ (by decide)⟩) := by simp [shortDecode, h1]
    rw [hd]
    simp only [h1, ↓reduceIte, identShortMaskR, identPairFin, pairFstF_eq, pairSndF_eq, Nat.xor_eq]
    have hc1 := cocodeColF_spec ⟨identPairFst (j % 276) % 24, Nat.mod_lt _ (by decide)⟩
    have hc2 := cocodeColF_spec ⟨identPairSnd (j % 276) % 24, Nat.mod_lt _ (by decide)⟩
    simp only at hc1 hc2
    rw [hc1, hc2]
    congr 1
    by_cases hs : j / 276 % 2 = 0
    · have : (⟨j / 276 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext hs
      simp [hs]
    · have : (⟨j / 276 % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) ≠ 0 :=
        fun h => hs (congrArg Fin.val h)
      simp [hs, this]
  · by_cases h2 : j < 49128
    · have ho : (j - 552) / 64 % 759 < 759 := Nat.mod_lt _ (by decide)
      have he : (j - 552) % 64 < 64 := Nat.mod_lt _ (by decide)
      have hd : shortDecode j = Sum.inr (Sum.inl (⟨(j - 552) / 64 % 759, ho⟩,
          ⟨(j - 552) % 64, he⟩)) := by simp [shortDecode, h1, h2]
      rw [hd]
      simp only [h1, h2, ↓reduceIte, identShortMaskR, octCodeF_eq, octOmegaF_eq, octThetaF_eq,
        selXorF_cocode, Nat.xor_eq]
      rw [octNegF_eq ⟨_, ho⟩ ⟨_, he⟩]
    · have hdl : (j - 49128) / 24 % 2048 < 2048 := Nat.mod_lt _ (by decide)
      have hil : (j - 49128) % 24 < 24 := Nat.mod_lt _ (by decide)
      have hd : shortDecode j = Sum.inr (Sum.inr (⟨(j - 49128) / 24 % 2048, hdl⟩,
          ⟨(j - 49128) % 24, hil⟩)) := by simp [shortDecode, h1, h2]
      rw [hd]
      simp only [h1, h2, ↓reduceIte, identShortMaskR, oddThetaF_eq, Nat.xor_eq]
      have hc := cocodeColF_spec ⟨(j - 49128) % 24, hil⟩
      simp only at hc
      rw [hc]
      congr 2
      unfold identOddOmega
      rw [oddFlagF_eq, oddCodeF_eq]
      have hf : identOddWeightFlag ((j - 49128) / 24 % 2048) < 2 := by
        unfold identOddWeightFlag
        exact Nat.mod_lt _ (by decide)
      have hb : (identOddCode ((j - 49128) / 24 % 2048) >>> ((j - 49128) % 24)) &&& 1 < 2 :=
        lt_of_le_of_lt Nat.and_le_right (by decide)
      have hbit : (identOddCode ((j - 49128) / 24 % 2048)).testBit ((j - 49128) % 24) =
          decide ((identOddCode ((j - 49128) / 24 % 2048) >>> ((j - 49128) % 24)) &&& 1 = 1) := by
        rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow,
          show (1 : ℕ) = 2 ^ 1 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
      simp only [hbit, decide_eq_true_eq]
      exact (omegaMask_bits _ _ hf hb).symm

/-! ## Fast short checks -/

/-- One fast checked transported term. -/
def shortTermCheckF (d : QMaskP) (s t : ℕ × ℤ) : Bool :=
  let p := d.stepP (shortMaskF s.1, false)
  p.1 == shortMaskF t.1 && t.2 == (if p.2 then -s.2 else s.2)

/-- The fast check of a whole transported list. -/
def shortCheckF (d : QMaskP) : List (ℕ × ℤ) → List (ℕ × ℤ) → Bool
  | [], [] => true
  | s :: L, t :: L' => shortTermCheckF d s t && shortCheckF d L L'
  | _, _ => false

/-- The fast check is the check of the unpacked data. -/
theorem shortCheckF_eq (d : QMaskP) (hd : d.ok = true) :
    ∀ L L' : List (ℕ × ℤ), shortCheckF d L L' = shortCheck d.toData L L'
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | s :: L, t :: L' => by
    simp only [shortCheckF, shortCheck, shortCheckF_eq d hd L L']
    congr 1
    simp only [shortTermCheckF, shortTermCheck, shortMaskF_eq, QMaskP.stepP_eq d hd]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
