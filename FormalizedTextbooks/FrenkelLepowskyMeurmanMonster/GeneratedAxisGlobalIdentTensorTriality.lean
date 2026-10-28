/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorWord

/-! # Packed tensor parts of triality and the tensor pairing

The tensor coordinates of a triality image (`generatedAxisGlobalTrialityScaledTensorQ`, and the
inverse `generatedAxisGlobalInverseTensorQ`) consist of a sparse odd-short part and a part
determined by the source tensor.  The latter is computed here on packed columns: a half
difference (or half sum) of each column, followed by sign masks for the Golay weight phase and
the code coordinate.  The tensor pairing is a packed dot product. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-! ## Golay code helpers with kernel-friendly recursion -/

/-- The Golay generator masks as a function of a natural index. -/
def gmask (j : ℕ) : ℕ := if h : j < 12 then golayGeneratorMasks ⟨j, h⟩ else 0

/-- The Golay encoding of the low `n` bits, by an explicit recursor. -/
def codeAux (x : ℕ) (n : ℕ) : ℕ :=
  Nat.rec 0 (fun j acc => acc ^^^ (if x.testBit j then gmask j else 0)) n

/-- One step of the Golay encoding recursion. -/
theorem codeAux_succ (x n : ℕ) :
    codeAux x (n + 1) = codeAux x n ^^^ (if x.testBit n then gmask n else 0) := rfl

/-- The base of the Golay encoding recursion. -/
theorem codeAux_zero (x : ℕ) : codeAux x 0 = 0 := rfl

/-- The Golay encoding is the explicit recursion. -/
theorem golayEncodedMask_eq (x : ℕ) : golayEncodedMask x = codeAux x 12 := by
  simp only [golayEncodedMask, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldl,
    codeAux_succ, codeAux_zero]
  rfl

/-- The number of set bits below `n`, by an explicit recursor. -/
def popAux (x : ℕ) (n : ℕ) : ℕ := Nat.rec 0 (fun i acc => acc + (if x.testBit i then 1 else 0)) n

/-- One step of the population count recursion. -/
theorem popAux_succ (x n : ℕ) :
    popAux x (n + 1) = popAux x n + (if x.testBit n then 1 else 0) := rfl

/-- The Golay mask weight is the explicit population count. -/
theorem golayMaskWeight_eq (m : ℕ) : golayMaskWeight m = popAux m 24 := by
  rw [golayMaskWeight, Fin.sum_univ_eq_sum_range (fun i => if m.testBit i then 1 else 0) 24]
  generalize 24 = n
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ih, popAux_succ]

/-- The Golay weight phase: the weight divided by four is odd. -/
def qPred (d : ℕ) : Bool := (popAux (codeAux d 12) 24 / 4) % 2 == 1

/-- The weight phase bitset over all spin labels (of the low eleven bits). -/
def qBits : ℕ :=
    (0xa55a96969966c33c9966a55a9696c33c96969966a55ac33c6996699669960000 <<< 0) |||
    (0xffff3c3cffff55aa33ccffffffff5a5affffffff0ff06666f0f0ff00ccccaaaa <<< 256) |||
    (0xffffffff33cc5a5affff0ff0ffff66663c3cffffffff55aaff00ccccf0f0aaaa <<< 512) |||
    (0x0ff0ffffffff6666ffffffff3c3c55aaffff33ccffff5a5accccf0f0ff00aaaa <<< 768) |||
    (0xdbb2e87ee78ebdd4e78edbb2e87ebdd4e87ee78edbb2bdd4177e177e177e7ee8 <<< 1024) |||
    (0x7ee8bd2b7ee8d4bdb2db7ee87ee8db4d7ee87ee88ee7e77171e77e174ddb2bbd <<< 1280) |||
    (0x7ee87ee8b2dbdb4d7ee88ee77ee8e771bd2b7ee87ee8d4bd7e174ddb71e72bbd <<< 1536) |||
    (0x8ee77ee87ee8e7717ee87ee8bd2bd4bd7ee8b2db7ee8db4d4ddb71e77e172bbd <<< 1792) |||
    (0xa55a96969966c33c9966a55a9696c33c96969966a55ac33c6996699669960000 <<< 2048) |||
    (0xffff3c3cffff55aa33ccffffffff5a5affffffff0ff06666f0f0ff00ccccaaaa <<< 2304) |||
    (0xffffffff33cc5a5affff0ff0ffff66663c3cffffffff55aaff00ccccf0f0aaaa <<< 2560) |||
    (0x0ff0ffffffff6666ffffffff3c3c55aaffff33ccffff5a5accccf0f0ff00aaaa <<< 2816) |||
    (0xdbb2e87ee78ebdd4e78edbb2e87ebdd4e87ee78edbb2bdd4177e177e177e7ee8 <<< 3072) |||
    (0x7ee8bd2b7ee8d4bdb2db7ee87ee8db4d7ee87ee88ee7e77171e77e174ddb2bbd <<< 3328) |||
    (0x7ee87ee8b2dbdb4d7ee88ee77ee8e771bd2b7ee87ee8d4bd7e174ddb71e72bbd <<< 3584) |||
    (0x8ee77ee87ee8e7717ee87ee8bd2bd4bd7ee8b2db7ee8db4d4ddb71e77e172bbd <<< 3840)

set_option maxRecDepth 100000 in
/-- The weight phase bitset is the weight phase of the low label. -/
theorem qBits_spec : ∀ k : Fin 4096, qBits.testBit k.val = qPred (k.val % 2048) := by
  decide +kernel

/-- The integral sign of the Golay weight phase. -/
theorem intSign_weight (d : ℕ) :
    generatedAxisGlobalIntSign ((golayMaskWeight (golayEncodedMask d) / 4 : ℕ) : ZMod 2) =
      if qPred d then -1 else 1 := by
  rw [golayMaskWeight_eq, golayEncodedMask_eq, qPred]
  generalize popAux (codeAux d 12) 24 / 4 = n
  have h : ((n : ℕ) : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_mod]
  rw [h]
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn <;> simp [hn, generatedAxisGlobalIntSign]

/-- The Golay code coordinates of the generators, as a mask of generator indices. -/
def gcol (j : ℕ) : ℕ :=
  Nat.rec 0 (fun b acc => acc ||| (if (gmask b).testBit j then 2 ^ b else 0)) 12

/-- Bits of the generator coordinate mask. -/
theorem gcol_testBit (j b : ℕ) (hb : b < 12) : (gcol j).testBit b = (gmask b).testBit j := by
  have key : ∀ n, n ≤ 12 → ∀ c, (Nat.rec 0 (fun b acc => acc ||| (if (gmask b).testBit j then 2 ^ b
      else 0)) n : ℕ).testBit c = (decide (c < n) && (gmask c).testBit j) := by
    intro n
    induction n with
    | zero => intro _ c; simp
    | succ n ih =>
      intro hn c
      change (Nat.rec 0 (fun b acc => acc ||| (if (gmask b).testBit j then 2 ^ b else 0)) n |||
        (if (gmask n).testBit j then 2 ^ n else 0) : ℕ).testBit c = _
      rw [Nat.testBit_or, ih (by omega) c]
      by_cases hc : c = n
      · subst hc
        split_ifs with hg <;> simp [hg]
      · split_ifs with hg
        · rw [Nat.testBit_two_pow_of_ne (Ne.symm hc)]
          by_cases hlt : c < n
          · simp [hlt, show c < n + 1 by omega]
          · simp [hlt, show ¬ c < n + 1 by omega]
        · by_cases hlt : c < n
          · simp [hlt, show c < n + 1 by omega]
          · simp [hlt, show ¬ c < n + 1 by omega]
  rw [gcol, key 12 le_rfl b]
  simp [hb]

/-- A coordinate of the Golay encoding is a parity with the generator coordinate mask. -/
theorem golayEncodedMask_testBit (d j : ℕ) :
    (golayEncodedMask d).testBit j = bpar (d &&& gcol j) 12 := by
  rw [golayEncodedMask_eq]
  have key : ∀ n, n ≤ 12 → (codeAux d n).testBit j = bpar (d &&& gcol j) n := by
    intro n
    induction n with
    | zero => intro _; simp [codeAux_zero, bpar]
    | succ n ih =>
      intro hn
      rw [codeAux_succ, Nat.testBit_xor, ih (by omega), bpar, Nat.testBit_and,
        gcol_testBit j n (by omega)]
      split_ifs with hd <;> simp [hd]
  exact key 12 le_rfl

/-! ## Packed half sums and differences of the two label halves -/

/-- The clear-bit mask is a field mask. -/
theorem lmask_isFieldMask (w K k : ℕ) (hk : k < K) :
    IsFieldMask w (2 ^ K) (lmask w K k) (fun t => t.testBit k = false) := by
  intro t ht
  rw [fld_lmask w K k t hk ht]
  cases h : t.testBit k <;> simp [h]

/-- Half sum (`neg = false`) or half difference (`neg = true`) of the two halves of a column,
duplicated over both halves. -/
def colHalf (w : ℕ) (neg : Bool) (x : SVec) : SVec :=
  let D := sadd (ssel (lmask w 12 11) x) (scond neg (str w 12 11 (ssel (bmask w 12 11) x)))
  sadd D (str w 12 11 D)

/-- Index facts for the two halves. -/
theorem half_index (k : ℕ) (hk : k < 4096) :
    (k.testBit 11 = false → k % 2048 = k ∧ k ^^^ 2 ^ 11 = k + 2048) ∧
    (k.testBit 11 = true → k % 2048 = k ^^^ 2 ^ 11 ∧ k = (k ^^^ 2 ^ 11) + 2048) := by
  have hx := xor_two_pow_eq k 11
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at hx
    simp only [Bool.false_eq_true, ↓reduceIte] at hx
    refine ⟨?_, by rw [hx]; norm_num⟩
    apply Nat.mod_eq_of_lt
    by_contra hc
    have : k.testBit 11 = true := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
      (by omega) (by omega)
    rw [h] at this
    exact Bool.false_ne_true this
  · rw [h] at hx
    simp only [↓reduceIte] at hx
    have hge : 2 ^ 11 ≤ k := Nat.ge_two_pow_of_testBit h
    have hge' : 2048 ≤ k := by simpa using hge
    refine ⟨?_, ?_⟩
    · rw [hx, Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt (by omega)]
      norm_num
    · rw [hx]
      norm_num
      omega

/-- The half sum or difference: bounds and values. -/
theorem colHalf_spec {w B : ℕ} (neg : Bool) {x : SVec} (hx : SBnd w (2 ^ 12) B x)
    (hB : 4 * B < 2 ^ w) :
    SBnd w (2 ^ 12) (4 * B) (colHalf w neg x) ∧ ∀ k < 4096,
      sval w (colHalf w neg x) k =
        sval w x (k % 2048) + (if neg then -1 else 1) * sval w x (k % 2048 + 2048) := by
  obtain ⟨l1, l2⟩ := ssel_spec hx _ _ (lmask_isFieldMask w 12 11 (by norm_num))
  obtain ⟨h1, h2⟩ := ssel_spec hx _ _ (bmask_isFieldMask w 12 11 (by norm_num))
  obtain ⟨t1, t2⟩ := str_spec h1 11 (by norm_num)
  obtain ⟨c1, c2⟩ := scond_spec neg t1
  obtain ⟨d1, d2⟩ := sadd_spec l1 c1 (by omega)
  obtain ⟨u1, u2⟩ := str_spec d1 11 (by norm_num)
  obtain ⟨e1, e2⟩ := sadd_spec d1 u1 (by omega)
  refine ⟨by
    have : B + B + (B + B) = 4 * B := by ring
    simpa [colHalf, this] using e1, fun k hk => ?_⟩
  have hk' : k < 2 ^ 12 := by norm_num; exact hk
  have hxk : k ^^^ 2 ^ 11 < 2 ^ 12 := xor_two_pow_lt k 11 12 (by norm_num) hk'
  have hD : ∀ m < 2 ^ 12, sval w (sadd (ssel (lmask w 12 11) x)
      (scond neg (str w 12 11 (ssel (bmask w 12 11) x)))) m =
      (if m.testBit 11 = false then sval w x m else 0) +
        (if neg then -1 else 1) *
          (if (m ^^^ 2 ^ 11).testBit 11 = true then sval w x (m ^^^ 2 ^ 11) else 0) := by
    intro m hm
    rw [d2 m hm, l2 m hm, c2, t2 m hm, h2 _ (xor_two_pow_lt m 11 12 (by norm_num) hm)]
  simp only [colHalf]
  rw [e2 k hk', u2 k hk', hD k hk', hD _ hxk]
  have hbit : (k ^^^ 2 ^ 11).testBit 11 = !k.testBit 11 := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow_self]; cases k.testBit 11 <;> rfl
  have hinv : (k ^^^ 2 ^ 11) ^^^ 2 ^ 11 = k := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hbit, hinv]
  obtain ⟨hf, ht⟩ := half_index k hk
  cases hb : k.testBit 11
  · obtain ⟨hm, hx2⟩ := hf hb
    rw [hm, hx2]
    simp only [Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, mul_zero,
      add_zero]
  · obtain ⟨hm, hx2⟩ := ht hb
    rw [hm, ← hx2]
    simp only [Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, zero_add]
    ring

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
