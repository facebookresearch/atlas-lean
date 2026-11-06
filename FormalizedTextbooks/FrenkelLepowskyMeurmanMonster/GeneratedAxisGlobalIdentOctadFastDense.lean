/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOddZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorDot
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortPilot1Data

/-! # Dense octad sums from packed term chunks (namespace `OctadDense`)

For dense representations (tens of thousands of short terms) the octad integer sum `octSumZ` of
the exact pairing is evaluated without term lists.  The target lists are given as packed chunks
`(labels, numerators, count)` (decoded by `decodeTerms`); one pass over the chunks packs the octad
terms of `L` (index `label - 552 = 64 o + e`) into eight range accumulators (single-part updates),
and one pass packs the octad terms of `W` at the twisted reversed index `65535 - (64 o + octTw e)`
with the diagonal sign.  The octad transform of `L` is the packed Walsh-Hadamard network
`octPackXP` (with a tight `2^6` field bound), and the sum over the `W` terms is the middle field of
two big-number products (`fld_mid_two`).  Field bounds come from one mask test per packed number.
`OctadDense.octSumChk w b fwd CL CW n` checks a claimed value; `OctadDense.octSumZ_of_chk` gives
`octSumZ w fwd L W = n` and `OctadDense.octPackOk_of_chk` gives `octPackOk w L = true` when
`L.sh = ShortData.ofList (OctadDense.octChunkTerms CL)` and similarly for `W`.
-/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
namespace OctadDense
open scoped BigOperators
set_option autoImplicit false

/-! ## Term lists of packed chunks -/

/-- The terms of a list of packed chunks `(labels, numerators, count)`. -/
def octChunkTerms : List (ℕ × ℕ × ℕ) → List (ℕ × ℤ)
  | [] => []
  | c :: cs => decodeTerms c.1 c.2.1 c.2.2 ++ octChunkTerms cs

/-- The octad-label test of `ShortData.ofList`. -/
def octLabel (p : ℕ × ℤ) : Bool := decide (552 ≤ p.1) && decide (p.1 < 49128)

/-- One octad term of `L` at its field index `label - 552`. -/
def octFlatOne (p : ℕ × ℤ) : List (ℕ × ℤ) :=
  if octLabel p = true then [(p.1 - 552, p.2)] else []

/-- The octad terms of a term list at their field indices. -/
def octFlatOf (T : List (ℕ × ℤ)) : List (ℕ × ℤ) := T.flatMap octFlatOne

/-- The twisted reversed field index of an octad term of `W` (offset `t = label - 552`). -/
def octWIdx (t : ℕ) : ℕ := 65535 - (64 * (t / 64) + octTw (t % 64))

/-- The diagonal sign of an octad term of `W`. -/
def octWSgn (fwd : Bool) (t : ℕ) : ℤ := if fwd then octD (t % 64) else 1

/-- One octad term of `W`, twisted, signed and reversed. -/
def octWOne (fwd : Bool) (p : ℕ × ℤ) : List (ℕ × ℤ) :=
  if octLabel p = true then [(octWIdx (p.1 - 552), octWSgn fwd (p.1 - 552) * p.2)] else []

/-- The twisted, signed, reversed octad terms of `W`. -/
def octWFlatOf (fwd : Bool) (T : List (ℕ × ℤ)) : List (ℕ × ℤ) := T.flatMap (octWOne fwd)

/-! ## The chunk passes -/

/-- Eight range accumulators of `2^13` fields. -/
abbrev OctRanges := ((SVec × SVec) × (SVec × SVec)) × ((SVec × SVec) × (SVec × SVec))

/-- Range accumulators with the running absolute sum. -/
abbrev OctAcc := OctRanges × ℕ

/-- The empty accumulator. -/
def octAccZero : OctAcc :=
  ((((szero, szero), (szero, szero)), ((szero, szero), (szero, szero))), 0)

/-- Add `v` to the positive (`neg = false`) or the negative part of a signed packed vector. -/
def octPart (neg : Bool) (v : ℕ) (x : SVec) : SVec := cond neg (x.1, x.2 + v) (x.1 + v, x.2)

/-- Add `v` to one part of range `j < 8`. -/
def octAccAdd (j : ℕ) (neg : Bool) (v : ℕ) (x : OctRanges) : OctRanges :=
  cond (Nat.blt j 4)
    (cond (Nat.blt j 2)
      (cond (Nat.blt j 1) ((((octPart neg v x.1.1.1, x.1.1.2), x.1.2), x.2))
        ((((x.1.1.1, octPart neg v x.1.1.2), x.1.2), x.2)))
      (cond (Nat.blt j 3) (((x.1.1, (octPart neg v x.1.2.1, x.1.2.2)), x.2))
        (((x.1.1, (x.1.2.1, octPart neg v x.1.2.2)), x.2))))
    (cond (Nat.blt j 6)
      (cond (Nat.blt j 5) ((x.1, ((octPart neg v x.2.1.1, x.2.1.2), x.2.2)))
        ((x.1, ((x.2.1.1, octPart neg v x.2.1.2), x.2.2))))
      (cond (Nat.blt j 7) ((x.1, (x.2.1, (octPart neg v x.2.2.1, x.2.2.2))))
        ((x.1, (x.2.1, (x.2.2.1, octPart neg v x.2.2.2))))))

/-- The eight ranges as one packed vector of `2^16` fields. -/
def octAccFlat (w : ℕ) (x : OctRanges) : SVec :=
  sadd (sadd (sadd x.1.1.1 (sshl (w * 8192) x.1.1.2))
      (sadd (sshl (w * 16384) x.1.2.1) (sshl (w * 24576) x.1.2.2)))
    (sadd (sadd (sshl (w * 32768) x.2.1.1) (sshl (w * 40960) x.2.1.2))
      (sadd (sshl (w * 49152) x.2.2.1) (sshl (w * 57344) x.2.2.2)))

/-- A single-part signed vector. -/
def octPartV (neg : Bool) (v : ℕ) : SVec := cond neg (0, v) (v, 0)

/-- One term of `L`: octad labels are added at field `label - 552`. -/
def octLStep (w l c : ℕ) (x : OctAcc) : OctAcc :=
  cond (Nat.ble 552 l && Nat.blt l 49128)
    (octAccAdd ((l - 552) >>> 13) (Nat.blt c 128)
      (((c - 128) + (128 - c)) <<< (w * ((l - 552) &&& 8191))) x.1,
      x.2 + ((c - 128) + (128 - c)))
    x

/-- Packed table of the twisted row indices `octTw e` (six-bit entries). -/
def octTwTable : ℕ :=
  0xfc10bc13ae47236d4bccd3b042eb53ad55a89d96a472285f81e7636e59985e9a94b1246f3f1c8cd0a277e0617b0fdf80

/-- The twisted row index from the table. -/
def octTwF (e : ℕ) : ℕ := (octTwTable >>> (6 * e)) &&& 63

/-- The fast twisted reversed index. -/
def octWIdxF (t : ℕ) : ℕ := 65535 - ((t >>> 6 <<< 6) + octTwF (t &&& 63))

/-- One term of `W`: octad labels are added at the twisted reversed index with the diagonal
sign. -/
def octWStep (w : ℕ) (fwd : Bool) (l c : ℕ) (x : OctAcc) : OctAcc :=
  cond (Nat.ble 552 l && Nat.blt l 49128)
    (octAccAdd (octWIdxF (l - 552) >>> 13)
      (Bool.xor (Nat.blt c 128) (fwd && identOctDiagTable.testBit ((l - 552) &&& 63)))
      (((c - 128) + (128 - c)) <<< (w * (octWIdxF (l - 552) &&& 8191))) x.1,
      x.2 + ((c - 128) + (128 - c)))
    x

/-- One pass over a chunk. -/
def octLoop (step : ℕ → ℕ → OctAcc → OctAcc) (labs nums : ℕ) (x : OctAcc) : ℕ → OctAcc
  | 0 => x
  | n + 1 => octLoop step (labs >>> 17) (nums >>> 8) (step (labs &&& 131071) (nums &&& 255) x) n

/-- One pass over all chunks. -/
def octLoops (step : ℕ → ℕ → OctAcc → OctAcc) : List (ℕ × ℕ × ℕ) → OctAcc → OctAcc
  | [], x => x
  | c :: cs, x => octLoops step cs (octLoop step c.1 c.2.1 x c.2.2)

/-- The packed octad terms of `L` and their absolute sum. -/
def octPackL (w : ℕ) (cs : List (ℕ × ℕ × ℕ)) : SVec × ℕ :=
  let x := octLoops (octLStep w) cs octAccZero
  (octAccFlat w x.1, x.2)

/-- The packed twisted reversed octad terms of `W` and their absolute sum. -/
def octPackW (w : ℕ) (fwd : Bool) (cs : List (ℕ × ℕ × ℕ)) : SVec × ℕ :=
  let x := octLoops (octWStep w fwd) cs octAccZero
  (octAccFlat w x.1, x.2)

/-- The middle field `65535` of a product. -/
def octMid (w P : ℕ) : ℕ := (P >>> (w * 65535)) &&& (2 ^ w - 1)

/-- The signed dot product of `x` with the reversal of `r`, by two products. -/
def octMidDot (w : ℕ) (x r : SVec) : ℤ :=
  (octMid w (x.1 * r.1 + x.2 * r.2) : ℤ) - (octMid w (x.1 * r.2 + x.2 * r.1) : ℤ)

/-- The field mask with bits `b ..< w` set in each of `2^16` fields. -/
def octHi (w b : ℕ) : ℕ := dblM w ((2 ^ w - 1) ^^^ (2 ^ b - 1)) 1 16

/-- The width conditions: absolute sums `a` (of `L`) and `a'` (of `W`), all fields of the packed
`L` and `W` below `2^b`, and no overflow in the transform and the product. -/
def octFastOk (w b a a' : ℕ) (PL PW : SVec) : Bool :=
  decide (4 ^ 6 * a < 2 ^ w) && decide (a' < 2 ^ w) && decide (b ≤ w) &&
    Nat.beq (PL.1 &&& octHi w b) 0 && Nat.beq (PL.2 &&& octHi w b) 0 &&
    Nat.beq (PW.1 &&& octHi w b) 0 && Nat.beq (PW.2 &&& octHi w b) 0 &&
    decide (2 * (2 * 65536 * ((2 ^ 6 * (2 ^ b - 1)) * (2 ^ b - 1))) < 2 ^ w)

/-- The checked dense octad sum at field width `w` with field bound `2^b`: the width conditions
hold and the value is `n`. -/
def octSumChk (w b : ℕ) (fwd : Bool) (CL CW : List (ℕ × ℕ × ℕ)) (n : ℤ) : Bool :=
  let PL := octPackL w CL
  let PW := octPackW w fwd CW
  octFastOk w b PL.2 PW.2 PL.1 PW.1 && decide (octMidDot w (octPackXP w fwd PL.1) PW.1 = n)

/-! ## Algebra of signed packed sums -/

theorem octSadd_assoc (x y z : SVec) : sadd (sadd x y) z = sadd x (sadd y z) := by
  simp only [sadd, Nat.add_assoc]

theorem octSadd_comm (x y : SVec) : sadd x y = sadd y x := by
  simp only [sadd, Nat.add_comm]

theorem octSadd_zero (x : SVec) : sadd x szero = x := by
  simp [sadd, szero]

theorem octZero_sadd (x : SVec) : sadd szero x = x := by
  simp [sadd, szero]

theorem octPackF_append (w : ℕ) (l1 l2 : List (ℕ × ℤ)) :
    packF w (l1 ++ l2) = sadd (packF w l1) (packF w l2) := by
  induction l1 with
  | nil => exact (octZero_sadd _).symm
  | cons p l ih =>
    change sadd (sglS w p) (packF w (l ++ l2)) = sadd (sadd (sglS w p) (packF w l)) (packF w l2)
    rw [ih, octSadd_assoc]

theorem octAbsSum_append (l1 l2 : List (ℕ × ℤ)) : absSum (l1 ++ l2) = absSum l1 + absSum l2 := by
  simp [absSum, List.map_append, List.sum_append]

theorem octSshl_sadd (s : ℕ) (x y : SVec) : sshl s (sadd x y) = sadd (sshl s x) (sshl s y) := by
  simp only [sshl, sadd, Nat.shiftLeft_eq, Nat.add_mul]

/-! ## The passes are exact packings -/

theorem octPart_eq (neg : Bool) (v : ℕ) (x : SVec) : octPart neg v x = sadd x (octPartV neg v) := by
  cases neg <;> simp [octPart, octPartV, sadd]

theorem octAccFlat_add (w j : ℕ) (hj : j < 8) (neg : Bool) (v : ℕ) (x : OctRanges) :
    octAccFlat w (octAccAdd j neg v x) =
      sadd (octAccFlat w x) (sshl (w * (8192 * j)) (octPartV neg v)) := by
  obtain ⟨⟨⟨x0, x1⟩, ⟨x2, x3⟩⟩, ⟨⟨x4, x5⟩, ⟨x6, x7⟩⟩⟩ := x
  interval_cases j <;>
    simp [octAccAdd, octAccFlat, octPart_eq, sadd, sshl, Nat.shiftLeft_eq] <;>
    constructor <;> ring

theorem octSshl_partV (w s k m : ℕ) (neg : Bool) :
    sshl (w * k) (octPartV neg (m <<< (w * s))) = octPartV neg (m <<< (w * (s + k))) := by
  cases neg <;>
    simp only [octPartV, sshl, Bool.cond_true, Bool.cond_false, Nat.shiftLeft_eq, Nat.mul_add,
      pow_add, Nat.mul_assoc, Nat.zero_mul]

theorem octPartV_eq (w t c : ℕ) (neg : Bool) (hc : c < 256) :
    octPartV (Bool.xor (Nat.blt c 128) neg) (((c - 128) + (128 - c)) <<< (w * t)) =
      sglS w (t, (if neg then -1 else 1) * ((c : ℤ) - 128)) := by
  by_cases h : 128 ≤ c
  · have e1 : 128 - c = 0 := by omega
    have e3 : Nat.blt c 128 = false := by
      cases hb : Nat.blt c 128
      · rfl
      · exact absurd (Nat.blt_eq.mp hb) (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, c = 128 + k := ⟨c - 128, by omega⟩
    cases neg <;> simp [octPartV, sglS, e1, e3]
  · have e1 : c - 128 = 0 := by omega
    have e3 : Nat.blt c 128 = true := Nat.blt_eq.mpr (by omega)
    have e2 : (c : ℤ) - 128 = -((128 - c : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    cases neg <;> simp [octPartV, sglS, e1, e3, e2]

theorem octSgl_abs (c : ℕ) (hc : c < 256) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (s * ((c : ℤ) - 128)).natAbs = (c - 128) + (128 - c) := by
  rcases hs with rfl | rfl
  · by_cases h : 128 ≤ c
    · omega
    · omega
  · by_cases h : 128 ≤ c
    · omega
    · omega

/-- The split of a field offset into a range and an offset inside the range. -/
theorem octSplit13 (t : ℕ) : (t &&& 8191) + 8192 * (t >>> 13) = t := by
  rw [show (8191 : ℕ) = 2 ^ 13 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  have := Nat.mod_add_div t (2 ^ 13)
  norm_num at this ⊢
  omega

theorem octRange_lt (t : ℕ) (ht : t < 65536) : t >>> 13 < 8 := by
  rw [Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem octLStep_spec (w l c : ℕ) (hc : c < 256) (x : OctAcc) :
    octAccFlat w (octLStep w l c x).1 =
      sadd (octAccFlat w x.1) (packF w (octFlatOf [(l, (c : ℤ) - 128)])) ∧
    (octLStep w l c x).2 = x.2 + absSum (octFlatOf [(l, (c : ℤ) - 128)]) := by
  by_cases hl : 552 ≤ l ∧ l < 49128
  · have hb : (Nat.ble 552 l && Nat.blt l 49128) = true := by
      simp [Nat.ble_eq, Nat.blt_eq, hl.1, hl.2]
    have hlab : octLabel (l, (c : ℤ) - 128) = true := by
      simp [octLabel, hl.1, hl.2]
    have hflat : octFlatOf [(l, (c : ℤ) - 128)] = [(l - 552, (c : ℤ) - 128)] := by
      simp [octFlatOf, octFlatOne, hlab]
    simp only [octLStep, hb, Bool.cond_true]
    rw [hflat, octAccFlat_add w _ (octRange_lt _ (by omega)), octSshl_partV, octSplit13]
    refine ⟨?_, ?_⟩
    · have hv := octPartV_eq w (l - 552) c false hc
      rw [Bool.xor_false] at hv
      rw [hv]
      simp [packF, octSadd_zero]
    · simp only [absSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [show ((c : ℤ) - 128) = 1 * ((c : ℤ) - 128) by ring, octSgl_abs c hc 1 (Or.inl rfl)]
  · have hb : (Nat.ble 552 l && Nat.blt l 49128) = false := by
      by_cases h1 : 552 ≤ l
      · have h2 : ¬ l < 49128 := fun h2 => hl ⟨h1, h2⟩
        have hbl : Nat.blt l 49128 = false := by
          cases h : Nat.blt l 49128
          · rfl
          · exact absurd (Nat.blt_eq.mp h) h2
        simp [hbl]
      · simp [Nat.ble_eq, h1]
    have hlab : octLabel (l, (c : ℤ) - 128) = false := by
      by_cases h1 : 552 ≤ l
      · have h2 : ¬ l < 49128 := fun h2 => hl ⟨h1, h2⟩
        simp [octLabel, h1, h2]
      · simp [octLabel, h1]
    have hflat : octFlatOf [(l, (c : ℤ) - 128)] = [] := by
      simp [octFlatOf, octFlatOne, hlab]
    simp only [octLStep, hb, Bool.cond_false, hflat]
    exact ⟨(octSadd_zero _).symm, by simp [absSum]⟩

/-- The fast twisted index table agrees with `octTw`. -/
theorem octTwF_eq : ∀ e : Fin 64, octTwF e.val = octTw e.val := by
  decide +kernel

theorem octWIdxF_eq (t : ℕ) : octWIdxF t = octWIdx t := by
  have h1 : t >>> 6 <<< 6 = 64 * (t / 64) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    norm_num
    ring
  have h2 : t &&& 63 = t % 64 := by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h3 := octTwF_eq ⟨t % 64, Nat.mod_lt _ (by norm_num)⟩
  simp only at h3
  rw [octWIdxF, octWIdx, h1, h2, h3]

theorem octWIdx_lt (t : ℕ) : octWIdx t < 65536 := by
  unfold octWIdx
  omega

theorem octWStep_spec (w : ℕ) (fwd : Bool) (l c : ℕ) (hc : c < 256) (x : OctAcc) :
    octAccFlat w (octWStep w fwd l c x).1 =
      sadd (octAccFlat w x.1) (packF w (octWFlatOf fwd [(l, (c : ℤ) - 128)])) ∧
    (octWStep w fwd l c x).2 = x.2 + absSum (octWFlatOf fwd [(l, (c : ℤ) - 128)]) := by
  by_cases hl : 552 ≤ l ∧ l < 49128
  · have hb : (Nat.ble 552 l && Nat.blt l 49128) = true := by
      simp [Nat.ble_eq, Nat.blt_eq, hl.1, hl.2]
    have hlab : octLabel (l, (c : ℤ) - 128) = true := by
      simp [octLabel, hl.1, hl.2]
    have hflat : octWFlatOf fwd [(l, (c : ℤ) - 128)] =
        [(octWIdx (l - 552), octWSgn fwd (l - 552) * ((c : ℤ) - 128))] := by
      simp [octWFlatOf, octWOne, hlab]
    have hneg : (if (fwd && identOctDiagTable.testBit ((l - 552) &&& 63)) = true then (-1 : ℤ)
        else 1) = octWSgn fwd (l - 552) := by
      have h2 : (l - 552) &&& 63 = (l - 552) % 64 := by
        rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
      unfold octWSgn octD
      rw [h2, Nat.mod_mod]
      cases fwd <;> simp
    simp only [octWStep, hb, Bool.cond_true]
    rw [hflat, octWIdxF_eq,
      octAccFlat_add w _ (octRange_lt _ (octWIdx_lt _)), octSshl_partV, octSplit13]
    refine ⟨?_, ?_⟩
    · rw [octPartV_eq w _ c _ hc, hneg]
      simp [packF, octSadd_zero]
    · simp only [absSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [octSgl_abs c hc _ (by unfold octWSgn octD; split_ifs <;> simp)]
  · have hb : (Nat.ble 552 l && Nat.blt l 49128) = false := by
      by_cases h1 : 552 ≤ l
      · have h2 : ¬ l < 49128 := fun h2 => hl ⟨h1, h2⟩
        have hbl : Nat.blt l 49128 = false := by
          cases h : Nat.blt l 49128
          · rfl
          · exact absurd (Nat.blt_eq.mp h) h2
        simp [hbl]
      · simp [Nat.ble_eq, h1]
    have hlab : octLabel (l, (c : ℤ) - 128) = false := by
      by_cases h1 : 552 ≤ l
      · have h2 : ¬ l < 49128 := fun h2 => hl ⟨h1, h2⟩
        simp [octLabel, h1, h2]
      · simp [octLabel, h1]
    have hflat : octWFlatOf fwd [(l, (c : ℤ) - 128)] = [] := by
      simp [octWFlatOf, octWOne, hlab]
    simp only [octWStep, hb, Bool.cond_false, hflat]
    exact ⟨(octSadd_zero _).symm, by simp [absSum]⟩

/-- A chunk pass adds the packing of the chunk's terms. -/
theorem octLoop_spec (w : ℕ) (step : ℕ → ℕ → OctAcc → OctAcc) (g : ℕ × ℤ → List (ℕ × ℤ))
    (hstep : ∀ l c x, c < 256 →
      octAccFlat w (step l c x).1 =
        sadd (octAccFlat w x.1) (packF w ([(l, (c : ℤ) - 128)].flatMap g)) ∧
      (step l c x).2 = x.2 + absSum ([(l, (c : ℤ) - 128)].flatMap g)) :
    ∀ (n labs nums : ℕ) (x : OctAcc),
      octAccFlat w (octLoop step labs nums x n).1 =
        sadd (octAccFlat w x.1) (packF w ((decodeTerms labs nums n).flatMap g)) ∧
      (octLoop step labs nums x n).2 = x.2 + absSum ((decodeTerms labs nums n).flatMap g)
  | 0, labs, nums, x => by
    simp [octLoop, decodeTerms, packF, octSadd_zero, absSum]
  | n + 1, labs, nums, x => by
    have hc : nums &&& 255 < 256 := Nat.lt_succ_of_le Nat.and_le_right
    obtain ⟨h1, h2⟩ := hstep (labs &&& 131071) (nums &&& 255) x hc
    obtain ⟨i1, i2⟩ := octLoop_spec w step g hstep n (labs >>> 17) (nums >>> 8)
      (step (labs &&& 131071) (nums &&& 255) x)
    have hd : decodeTerms labs nums (n + 1) =
        [((labs &&& 131071 : ℕ), ((nums &&& 255 : ℕ) : ℤ) - 128)] ++
          decodeTerms (labs >>> 17) (nums >>> 8) n := rfl
    have hl : octLoop step labs nums x (n + 1) =
        octLoop step (labs >>> 17) (nums >>> 8) (step (labs &&& 131071) (nums &&& 255) x) n := rfl
    rw [hl, hd, List.flatMap_append, octPackF_append, octAbsSum_append]
    refine ⟨?_, ?_⟩
    · rw [i1, h1, octSadd_assoc]
    · rw [i2, h2, Nat.add_assoc]

/-- A pass over all chunks adds the packing of all terms. -/
theorem octLoops_spec (w : ℕ) (step : ℕ → ℕ → OctAcc → OctAcc) (g : ℕ × ℤ → List (ℕ × ℤ))
    (hstep : ∀ l c x, c < 256 →
      octAccFlat w (step l c x).1 =
        sadd (octAccFlat w x.1) (packF w ([(l, (c : ℤ) - 128)].flatMap g)) ∧
      (step l c x).2 = x.2 + absSum ([(l, (c : ℤ) - 128)].flatMap g)) :
    ∀ (cs : List (ℕ × ℕ × ℕ)) (x : OctAcc),
      octAccFlat w (octLoops step cs x).1 =
        sadd (octAccFlat w x.1) (packF w ((octChunkTerms cs).flatMap g)) ∧
      (octLoops step cs x).2 = x.2 + absSum ((octChunkTerms cs).flatMap g)
  | [], x => by simp [octLoops, octChunkTerms, packF, octSadd_zero, absSum]
  | c :: cs, x => by
    obtain ⟨h1, h2⟩ := octLoop_spec w step g hstep c.2.2 c.1 c.2.1 x
    obtain ⟨i1, i2⟩ := octLoops_spec w step g hstep cs (octLoop step c.1 c.2.1 x c.2.2)
    have hl : octLoops step (c :: cs) x = octLoops step cs (octLoop step c.1 c.2.1 x c.2.2) := rfl
    have hc : octChunkTerms (c :: cs) = decodeTerms c.1 c.2.1 c.2.2 ++ octChunkTerms cs := rfl
    rw [hl, hc, List.flatMap_append, octPackF_append, octAbsSum_append]
    refine ⟨?_, ?_⟩
    · rw [i1, h1, octSadd_assoc]
    · rw [i2, h2, Nat.add_assoc]

theorem octAccFlat_zero (w : ℕ) : octAccFlat w octAccZero.1 = szero := by
  simp [octAccFlat, octAccZero, sadd, sshl, szero]

/-- The `L` pass is the exact packing of the octad terms. -/
theorem octPackL_spec (w : ℕ) (cs : List (ℕ × ℕ × ℕ)) :
    (octPackL w cs).1 = packF w (octFlatOf (octChunkTerms cs)) ∧
      (octPackL w cs).2 = absSum (octFlatOf (octChunkTerms cs)) := by
  have hstep : ∀ l c x, c < 256 →
      octAccFlat w (octLStep w l c x).1 =
        sadd (octAccFlat w x.1) (packF w ([(l, (c : ℤ) - 128)].flatMap octFlatOne)) ∧
      (octLStep w l c x).2 = x.2 + absSum ([(l, (c : ℤ) - 128)].flatMap octFlatOne) :=
    fun l c x hc => octLStep_spec w l c hc x
  obtain ⟨h1, h2⟩ := octLoops_spec w (octLStep w) octFlatOne hstep cs octAccZero
  rw [octAccFlat_zero, octZero_sadd] at h1
  exact ⟨h1, by rw [octPackL, h2]; simp [octAccZero, octFlatOf]⟩

/-- The `W` pass is the exact packing of the twisted reversed octad terms. -/
theorem octPackW_spec (w : ℕ) (fwd : Bool) (cs : List (ℕ × ℕ × ℕ)) :
    (octPackW w fwd cs).1 = packF w (octWFlatOf fwd (octChunkTerms cs)) ∧
      (octPackW w fwd cs).2 = absSum (octWFlatOf fwd (octChunkTerms cs)) := by
  have hstep : ∀ l c x, c < 256 →
      octAccFlat w (octWStep w fwd l c x).1 =
        sadd (octAccFlat w x.1) (packF w ([(l, (c : ℤ) - 128)].flatMap (octWOne fwd))) ∧
      (octWStep w fwd l c x).2 = x.2 + absSum ([(l, (c : ℤ) - 128)].flatMap (octWOne fwd)) :=
    fun l c x hc => octWStep_spec w fwd l c hc x
  obtain ⟨h1, h2⟩ := octLoops_spec w (octWStep w fwd) (octWOne fwd) hstep cs octAccZero
  rw [octAccFlat_zero, octZero_sadd] at h1
  exact ⟨h1, by rw [octPackW, h2]; simp [octAccZero, octWFlatOf]⟩

/-! ## Term lists of `ShortData.ofList` -/

/-- The octad blocks of `ShortData.ofList`, flattened at their field indices. -/
theorem octFlat_blocks_list (T : List (ℕ × ℤ)) :
    ((T.filter (fun p => decide (552 ≤ p.1) && decide (p.1 < 49128))).map
      (fun p => ((p.1 - 552) / 64, [((p.1 - 552) % 64, p.2)]))).flatMap
      (fun b => b.2.map (fun q => (64 * b.1 + q.1 % 64, q.2))) = octFlatOf T := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    unfold octFlatOf at ih ⊢
    rw [List.filter_cons, List.flatMap_cons]
    by_cases h : octLabel p = true
    · have h' : (decide (552 ≤ p.1) && decide (p.1 < 49128)) = true := h
      have hp : 552 ≤ p.1 ∧ p.1 < 49128 := by simpa [octLabel] using h
      rw [ite_eq_left h', List.map_cons, List.flatMap_cons, ih]
      have he : 64 * ((p.1 - 552) / 64) + (p.1 - 552) % 64 % 64 = p.1 - 552 := by omega
      simp only [octFlatOne, h, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, he]
    · have h' : ¬ (decide (552 ≤ p.1) && decide (p.1 < 49128)) = true := h
      rw [ite_eq_right h', ih]
      simp [octFlatOne, h]

theorem octLFlat_ofList (L : IdentVec) (T : List (ℕ × ℤ)) (hL : L.sh = ShortData.ofList T) :
    octLFlat L = octFlatOf T := by
  unfold octLFlat
  rw [hL]
  exact octFlat_blocks_list T

theorem octFlatOf_lt (T : List (ℕ × ℤ)) : ∀ p ∈ octFlatOf T, p.1 < 48576 := by
  intro p hp
  simp only [octFlatOf, List.mem_flatMap] at hp
  obtain ⟨q, _, hq⟩ := hp
  unfold octFlatOne at hq
  split_ifs at hq with h
  · have hq' : 552 ≤ q.1 ∧ q.1 < 49128 := by simpa [octLabel] using h
    simp only [List.mem_singleton] at hq
    rw [hq]
    simp only
    omega
  · simp at hq

theorem octWFlatOf_lt (fwd : Bool) (T : List (ℕ × ℤ)) : ∀ p ∈ octWFlatOf fwd T, p.1 < 65536 := by
  intro p hp
  simp only [octWFlatOf, List.mem_flatMap] at hp
  obtain ⟨q, _, hq⟩ := hp
  unfold octWOne at hq
  split_ifs at hq with h
  · simp only [List.mem_singleton] at hq
    rw [hq]
    exact octWIdx_lt _
  · simp at hq

/-- The packed-check width condition gives the applicability of the packed octad transform. -/
theorem octPackOk_of_flat (w : ℕ) (L : IdentVec) (T : List (ℕ × ℤ))
    (hL : L.sh = ShortData.ofList T) (h : 4 ^ 6 * absSum (octFlatOf T) < 2 ^ w) :
    octPackOk w L = true := by
  rw [octPackOk, octLFlat_ofList L T hL]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun p hp => lt_of_lt_of_le (octFlatOf_lt T p hp) (by norm_num), h⟩

/-! ## The sum over the octad terms of `W` -/

/-- The octad coordinates summed over the octad blocks of `ShortData.ofList`. -/
theorem octWSum_list (w : ℕ) (fwd : Bool) (X : SVec) (T : List (ℕ × ℤ)) :
    (((T.filter (fun p => decide (552 ≤ p.1) && decide (p.1 < 49128))).map
      (fun p => ((p.1 - 552) / 64, [((p.1 - 552) % 64, p.2)]))).map
      (fun b => (b.2.map (fun q => q.2 * octZ w fwd X b.1 q.1)).sum)).sum =
      ((octWFlatOf fwd T).map (fun q => q.2 * sval w X (65535 - q.1))).sum := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    unfold octWFlatOf at ih ⊢
    rw [List.filter_cons, List.flatMap_cons, List.map_append, List.sum_append]
    by_cases h : octLabel p = true
    · have h' : (decide (552 ≤ p.1) && decide (p.1 < 49128)) = true := h
      have hp : 552 ≤ p.1 ∧ p.1 < 49128 := by simpa [octLabel] using h
      rw [ite_eq_left h', List.map_cons, List.map_cons, List.sum_cons, ih]
      congr 1
      simp only [octWOne, h, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, octZ, svalS_eq_sval, octWIdx, octWSgn]
      have htw := octTw_lt ((p.1 - 552) % 64)
      have hi : 65535 - (65535 - (64 * ((p.1 - 552) / 64) + octTw ((p.1 - 552) % 64))) =
          64 * ((p.1 - 552) / 64) + octTw ((p.1 - 552) % 64) := by omega
      rw [hi]
      cases fwd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
    · have h' : ¬ (decide (552 ≤ p.1) && decide (p.1 < 49128)) = true := h
      rw [ite_eq_right h', ih]
      simp [octWOne, h]

/-- The octad coordinates summed over the `W` octad terms, for any packed transform `X`. -/
theorem octWSum_flat (w : ℕ) (fwd : Bool) (X : SVec) (W : IdentVec) (T : List (ℕ × ℤ))
    (hW : W.sh = ShortData.ofList T) :
    (W.sh.oct.map (fun b => (b.2.map (fun q => q.2 * octZ w fwd X b.1 q.1)).sum)).sum =
      ((octWFlatOf fwd T).map (fun q => q.2 * sval w X (65535 - q.1))).sum := by
  rw [hW]
  exact octWSum_list w fwd X T

/-- Pairing with a reversed exact packing reads the packed vector at the reversed indices. -/
theorem octRevSum (w : ℕ) (X : SVec) (l : List (ℕ × ℤ)) (hl : ∀ q ∈ l, q.1 < 65536) :
    ∑ i ∈ Finset.range 65536, sval w X i * idxSum l (65535 - i) =
      (l.map (fun q => q.2 * sval w X (65535 - q.1))).sum := by
  induction l with
  | nil => simp only [idxSum, List.map_nil, List.sum_nil, mul_zero, Finset.sum_const_zero]
  | cons q l ih =>
    have hq : q.1 < 65536 := hl q (by simp)
    have ih' := ih (fun r hr => hl r (by simp [hr]))
    have hsplit : ∀ i, idxSum (q :: l) (65535 - i) =
        (if q.1 = 65535 - i then q.2 else 0) + idxSum l (65535 - i) := by
      intro i
      simp [idxSum]
    simp only [hsplit, mul_add, Finset.sum_add_distrib, ih', List.map_cons, List.sum_cons]
    have hcond : ∀ i ∈ Finset.range 65536, sval w X i * (if q.1 = 65535 - i then q.2 else 0) =
        if i = 65535 - q.1 then q.2 * sval w X (65535 - q.1) else 0 := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      by_cases h : i = 65535 - q.1
      · subst h
        rw [ite_eq_left (by omega), ite_eq_left rfl]
        ring
      · rw [ite_eq_right (by omega), ite_eq_right h]
        ring
    have hfirst : ∑ i ∈ Finset.range 65536, sval w X i * (if q.1 = 65535 - i then q.2 else 0) =
        q.2 * sval w X (65535 - q.1) := by
      rw [Finset.sum_congr rfl hcond, Finset.sum_ite_eq']
      simp only [Finset.mem_range]
      rw [ite_eq_left (by omega)]
    rw [hfirst]

/-! ## The middle-field dot product -/

theorem octMid_eq (w P : ℕ) : octMid w P = fld w P 65535 := by
  rw [octMid, ← fldS_eq]
  rfl

/-- The two products compute the dot product with the reversed second factor. -/
theorem octMidDot_eq {w Bx By : ℕ} {x r : SVec} (hx : SBnd w 65536 Bx x) (hr : SBnd w 65536 By r)
    (hB : 2 * (2 * 65536 * (Bx * By)) < 2 ^ w) :
    octMidDot w x r = ∑ i ∈ Finset.range 65536, sval w x i * sval w r (65535 - i) := by
  have hn : (0 : ℕ) < 65536 := by norm_num
  have m1 := fld_mid_two w 65536 hn x.1 x.2 r.1 r.2 Bx By hx.1 hx.2.1 hr.1 hr.2.1
    (fun i hi => (hx.2.2 i hi).1) (fun i hi => (hx.2.2 i hi).2)
    (fun i hi => (hr.2.2 i hi).1) (fun i hi => (hr.2.2 i hi).2) hB
  have m2 := fld_mid_two w 65536 hn x.1 x.2 r.2 r.1 Bx By hx.1 hx.2.1 hr.2.1 hr.1
    (fun i hi => (hx.2.2 i hi).1) (fun i hi => (hx.2.2 i hi).2)
    (fun i hi => (hr.2.2 i hi).2) (fun i hi => (hr.2.2 i hi).1) hB
  rw [octMidDot, octMid_eq, octMid_eq, show (65535 : ℕ) = 65536 - 1 from rfl, m1, m2]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sval]
  ring

/-! ## Field bounds from masks; a tight Walsh-Hadamard bound -/

theorem octHi_fld (w b i : ℕ) (hb : b ≤ w) (hi : i < 2 ^ 16) :
    fld w (octHi w b) i = (2 ^ w - 1) ^^^ (2 ^ b - 1) := by
  have h1 : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt (by positivity) one_pos
  have h2 : 2 ^ b - 1 < 2 ^ w :=
    lt_of_lt_of_le (Nat.sub_lt (by positivity) one_pos) (Nat.pow_le_pow_right (by norm_num) hb)
  have hB : (2 ^ w - 1) ^^^ (2 ^ b - 1) < 2 ^ (w * 1) := by
    rw [Nat.mul_one]
    exact Nat.xor_lt_two_pow h1 h2
  have h := fld_dblM w ((2 ^ w - 1) ^^^ (2 ^ b - 1)) 1 (by norm_num) hB 16 i (by simpa using hi)
  rw [octHi, h, Nat.mod_one, fld_zero_right, Nat.mod_eq_of_lt (by simpa using hB)]

theorem octHi_bound (w b P : ℕ) (hb : b ≤ w) (h : P &&& octHi w b = 0) (i : ℕ)
    (hi : i < 2 ^ 16) : fld w P i ≤ 2 ^ b - 1 := by
  have h1 : fld w P i &&& ((2 ^ w - 1) ^^^ (2 ^ b - 1)) = 0 := by
    rw [← octHi_fld w b i hb hi, ← fld_land, h]
    simp [fld]
  have hlt : fld w P i < 2 ^ b := by
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    by_cases hjw : j < w
    · have := congrArg (fun x => Nat.testBit x j) h1
      simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
        Nat.zero_testBit] at this
      simpa [hjw, show ¬ j < b by omega] using this
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (fld_lt w P i)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  omega

theorem octSsel_fld {w n : ℕ} (P M : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (hM : IsFieldMask w n M p) (i : ℕ) (hi : i < n) :
    fld w (P &&& M) i = if p i then fld w P i else 0 := by
  rw [fld_land, hM i hi]
  split_ifs
  · exact Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt w P i)
  · simp

/-- A butterfly on disjoint masks doubles the field bound. -/
theorem octBfly_tight {W K B : ℕ} {x : SVec} (hx : SBnd W (2 ^ K) B x) (k M0 M1 : ℕ) (hk : k < K)
    (hM0 : IsFieldMask W (2 ^ K) M0 (fun u => u.testBit k = false))
    (hM1 : IsFieldMask W (2 ^ K) M1 (fun u => u.testBit k = true))
    (hB : B + B < 2 ^ W) :
    SBnd W (2 ^ K) (B + B) (bflyM W K k M0 M1 x) := by
  obtain ⟨s1, _⟩ := strM_spec hx k M0 hk hM0
  obtain ⟨n1, _⟩ := sneg_spec hx
  obtain ⟨a1, _⟩ := sadd_spec hx s1 hB
  obtain ⟨a2, _⟩ := sadd_spec s1 n1 hB
  have key : ∀ (P Q : ℕ), P < 2 ^ (W * 2 ^ K) → Q < 2 ^ (W * 2 ^ K) →
      (∀ i < 2 ^ K, fld W P i ≤ B + B) → (∀ i < 2 ^ K, fld W Q i ≤ B + B) →
      (P &&& M0) + (Q &&& M1) < 2 ^ (W * 2 ^ K) ∧
        ∀ i < 2 ^ K, fld W ((P &&& M0) + (Q &&& M1)) i ≤ B + B := by
    intro P Q hP hQ hPb hQb
    have hsum : ∀ i < 2 ^ K, fld W (P &&& M0) i + fld W (Q &&& M1) i < 2 ^ W := by
      intro i hi
      have := hPb i hi
      have := hQb i hi
      rw [octSsel_fld P M0 _ hM0 i hi, octSsel_fld Q M1 _ hM1 i hi]
      by_cases hbit : i.testBit k <;> simp [hbit] <;> omega
    obtain ⟨h1, h2⟩ := fld_add W (2 ^ K) _ _ (lt_of_le_of_lt Nat.and_le_left hP)
      (lt_of_le_of_lt Nat.and_le_left hQ) hsum
    refine ⟨h1, fun i hi => ?_⟩
    have := hPb i hi
    have := hQb i hi
    rw [h2 i hi, octSsel_fld P M0 _ hM0 i hi, octSsel_fld Q M1 _ hM1 i hi]
    by_cases hbit : i.testBit k <;> simp [hbit] <;> omega
  have k1 := key _ _ a1.1 a2.1 (fun i hi => (a1.2.2 i hi).1) (fun i hi => (a2.2.2 i hi).1)
  have k2 := key _ _ a1.2.1 a2.2.1 (fun i hi => (a1.2.2 i hi).2) (fun i hi => (a2.2.2 i hi).2)
  exact ⟨k1.1, k2.1, fun i hi => ⟨k1.2 i hi, k2.2 i hi⟩⟩

/-- The packed Walsh-Hadamard network multiplies the field bound by `2^k`. -/
theorem octWht_tight (w B : ℕ) (x : SVec) (hx : SBnd w (2 ^ 16) B x) (hB : 2 ^ 6 * B < 2 ^ w) :
    ∀ k ≤ 6, SBnd w (2 ^ 16) (2 ^ k * B) (whtP w x k)
  | 0, _ => by simpa [whtP] using hx
  | k + 1, hk => by
    have ih := octWht_tight w B x hx hB k (by omega)
    have h2 : 2 ^ k * B + 2 ^ k * B = 2 ^ (k + 1) * B := by ring
    have hle : 2 ^ (k + 1) * B ≤ 2 ^ 6 * B :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hk)
    rw [← h2]
    exact octBfly_tight ih k _ _ (by omega) (octBit0_isFieldMask w k (by omega))
      (octBit1_isFieldMask w k (by omega)) (by omega)

/-- The packed octad transform multiplies the field bound by `2^6`. -/
theorem octPackXP_tight (w Bp : ℕ) (fwd : Bool) (P : SVec) (hP : SBnd w (2 ^ 16) Bp P)
    (hB : 2 ^ 6 * Bp < 2 ^ w) : SBnd w (2 ^ 16) (2 ^ 6 * Bp) (octPackXP w fwd P) := by
  have hBp : Bp < 2 ^ w := by
    have : 2 ^ 6 * Bp = 64 * Bp := by norm_num
    omega
  have hin : SBnd w (2 ^ 16) Bp
      (if fwd then P else sflip (allMask w (2 ^ 16)) (rep64 w identOctDiagTable) P) := by
    cases fwd
    · exact (sflip_spec hP (rep64 w identOctDiagTable)
        (fun t => identOctDiagTable.testBit (t % 64) = true) (rep64_isFieldMask w _) hBp).1
    · exact hP
  exact octWht_tight w Bp _ hin hB 6 le_rfl

/-! ## The checked dense octad sum -/

/-- A field mask check and an exact packing give the tight bound of the packing. -/
theorem octPack_tight (w b n : ℕ) (P : SVec) (hP : P.1 < 2 ^ (w * n) ∧ P.2 < 2 ^ (w * n))
    (hn : n = 2 ^ 16) (hb : b ≤ w) (h1 : P.1 &&& octHi w b = 0) (h2 : P.2 &&& octHi w b = 0) :
    SBnd w n (2 ^ b - 1) P := by
  subst hn
  exact ⟨hP.1, hP.2, fun i hi => ⟨octHi_bound w b _ hb h1 i hi, octHi_bound w b _ hb h2 i hi⟩⟩

/-- The checked dense octad sum is the octad integer sum of the exact pairing. -/
theorem octSumZ_of_chk (w b : ℕ) (fwd : Bool) (L W : IdentVec) (CL CW : List (ℕ × ℕ × ℕ))
    (n : ℤ) (hL : L.sh = ShortData.ofList (octChunkTerms CL))
    (hW : W.sh = ShortData.ofList (octChunkTerms CW))
    (h : octSumChk w b fwd CL CW n = true) : octSumZ w fwd L W = n := by
  obtain ⟨pL1, pL2⟩ := octPackL_spec w CL
  obtain ⟨pW1, pW2⟩ := octPackW_spec w fwd CW
  simp only [octSumChk, octFastOk, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hbw⟩, hl1⟩, hl2⟩, hw1⟩, hw2⟩, hbig⟩, hv⟩ := h
  rw [pL2] at ha
  rw [pW2] at hb
  rw [pL1] at hl1 hl2 hv
  rw [pW1] at hw1 hw2 hv
  set TL := octChunkTerms CL
  set TW := octChunkTerms CW
  have hflat := octLFlat_ofList L TL hL
  have hok : octPackOk w L = true := octPackOk_of_flat w L TL hL ha
  -- the exact packing of `L`
  have hSL : absSum (octLFlat L) < 2 ^ w := by rw [hflat]; omega
  obtain ⟨sP1, sP2⟩ := packF_spec w (2 ^ 16) (octLFlat L)
    (fun p hp => by rw [hflat] at hp; exact lt_of_lt_of_le (octFlatOf_lt TL p hp) (by norm_num))
    hSL
  rw [← hflat] at hl1 hl2 hv
  have hPt := octPack_tight w b _ _ ⟨sP1.1, sP1.2.1⟩ rfl hbw hl1 hl2
  set X := octPackXP w fwd (packF w (octLFlat L))
  -- the tight bounds
  have hB6 : 2 ^ 6 * (2 ^ b - 1) < 2 ^ w := by
    rcases Nat.eq_zero_or_pos (2 ^ b - 1) with h0 | h0
    · rw [h0]; positivity
    · calc 2 ^ 6 * (2 ^ b - 1) ≤ 2 * (2 * 65536 * ((2 ^ 6 * (2 ^ b - 1)) * (2 ^ b - 1))) := by
            nlinarith
        _ < 2 ^ w := hbig
  have hX := octPackXP_tight w _ fwd _ hPt hB6
  -- the packed `W`
  obtain ⟨sR1, sR2⟩ := packF_spec w 65536 (octWFlatOf fwd TW) (octWFlatOf_lt fwd TW) hb
  have hRt := octPack_tight w b 65536 _ ⟨sR1.1, sR1.2.1⟩ (by norm_num) hbw hw1 hw2
  -- the octad coordinates agree for both packings
  have hZ : ∀ o e, octZ w fwd (octPackXH w fwd L) o e = octZ w fwd X o e := by
    intro o e
    rw [octZH_eq w fwd L hok o e, octZ_eq_of_pack w fwd L hok _ sP1 sP2 o e]
  have hsum : octSumZ w fwd L W =
      (W.sh.oct.map (fun b => (b.2.map (fun q => q.2 * octZ w fwd X b.1 q.1)).sum)).sum := by
    unfold octSumZ
    simp only [hZ]
  rw [hsum, octWSum_flat w fwd X W TW hW, ← octRevSum w X _ (octWFlatOf_lt fwd TW)]
  have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  rw [e16] at hX
  rw [← hv, octMidDot_eq hX hRt hbig]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [sR2 (65535 - i) (by omega)]

/-- The checked dense octad sum gives the applicability of the packed octad transform. -/
theorem octPackOk_of_chk (w b : ℕ) (fwd : Bool) (L : IdentVec) (CL CW : List (ℕ × ℕ × ℕ))
    (n : ℤ) (hL : L.sh = ShortData.ofList (octChunkTerms CL))
    (h : octSumChk w b fwd CL CW n = true) : octPackOk w L = true := by
  obtain ⟨_, pL2⟩ := octPackL_spec w CL
  simp only [octSumChk, octFastOk, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [pL2] at h
  exact octPackOk_of_flat w L _ hL h.1.1.1.1.1.1.1.1

end OctadDense
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
