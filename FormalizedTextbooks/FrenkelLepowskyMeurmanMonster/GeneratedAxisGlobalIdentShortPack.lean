/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortCheckM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOctH

/-! # A field-parallel short transport check

The masks of a chunk of at most `2^t` source and target terms are packed in 32-bit fields
(`packM`, masks from the certified table `identMaskG`).  The image masks and the central bits of
all terms of the chunk are computed at once by field-parallel selections (`imgP`) and parities
(`parP`), then compared with the packed target masks and the target values.  `chunkP_sound`
gives `shortCheckF` for a chunk, and `shortCheckPk_sound` for a long list checked in chunks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

/-! ## Masks in 32-bit fields -/

/-- Pack a list of masks in 32-bit fields (first element in field `0`), each cut to 24 bits. -/
def packM : List ℕ → ℕ
  | [] => 0
  | m :: l => (m &&& 16777215) ||| (packM l <<< 32)

theorem fld_packM : ∀ (l : List ℕ) (k : ℕ), fld 32 (packM l) k = l.getD k 0 &&& 16777215
  | [], k => by simp [packM, fld_zero_right_zero]
  | m :: l, k => by
    have h1 : m &&& 16777215 < 2 ^ 32 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
    rw [packM, fld_lor, fld_small 32 _ k h1, show (32 : ℕ) = 32 * 1 from rfl, fld_shiftLeft]
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.zero_or, Nat.le_add_left,
        Nat.add_sub_cancel, List.getD_cons_succ]
      exact fld_packM l k

/-- The repunit: `1` in each of the first `2^t` fields of width 32. -/
def lowP (t : ℕ) : ℕ := dblM 32 1 1 t

theorem lowP_lt (t : ℕ) : lowP t < 2 ^ (32 * 2 ^ t) := by
  have h := dblM_lt 32 1 1 (by norm_num) t
  simpa [lowP] using h

theorem fld_lowP (t k : ℕ) (hk : k < 2 ^ t) : fld 32 (lowP t) k = 1 := by
  rw [lowP, fld_dblM 32 1 1 (by norm_num) (by norm_num) t k (by simpa using hk), Nat.mod_one]
  simp [fld]

/-- Bit `b` of every field, as `0`/`1` fields (with the repunit `L`). -/
def bitsP (V L b : ℕ) : ℕ := (V >>> b) &&& L

theorem fld_bitsP (V L b k : ℕ) (hb : b < 32) (hL : fld 32 L k = 1) :
    fld 32 (bitsP V L b) k = if (fld 32 V k).testBit b then 1 else 0 := by
  rw [bitsP, fld_land, hL, Nat.and_one_is_mod]
  have h1 : (fld 32 (V >>> b) k).testBit 0 = (fld 32 V k).testBit b := by
    rw [testBit_fld, testBit_fld, Nat.testBit_shiftRight]
    simp only [show (0 : ℕ) < 32 by norm_num, hb, decide_true, Bool.true_and]
    congr 1
    omega
  rw [← h1]
  rcases Nat.mod_two_eq_zero_or_one (fld 32 (V >>> b) k) with h | h
  · rw [h, ite_eq_right]
    rw [Nat.testBit_zero, h]
    simp
  · rw [h, ite_eq_left]
    rw [Nat.testBit_zero, h]
    simp

theorem bitsP_le (V L b : ℕ) : bitsP V L b ≤ L := Nat.and_le_right

/-! ## Field-parallel selections and parities -/

/-- In every field: the exclusive or of `C j` over the set bits `j < i` of the field. -/
def imgP (C : ℕ → ℕ) (V L : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => imgP C V L i ^^^ ((16777215 * bitsP V L i) &&& (C i * L))

theorem fld_imgP (C : ℕ → ℕ) (hC : ∀ j, C j < 2 ^ 24) (V L K : ℕ) (hL : L < 2 ^ (32 * K))
    (hLf : ∀ k < K, fld 32 L k = 1) : ∀ i ≤ 32, ∀ k < K,
    fld 32 (imgP C V L i) k = xorRange (fun j => if (fld 32 V k).testBit j then C j else 0) i
  | 0, _, k, _ => by simp [imgP, xorRange, fld_zero_right_zero]
  | i + 1, hi, k, hk => by
    rw [imgP, fld_xor, fld_imgP C hC V L K hL hLf i (by omega) k hk, xorRange, fld_land]
    congr 1
    have hb := fld_bitsP V L i k (by omega) (hLf k hk)
    have m1 := fld_mul 32 16777215 K (bitsP V L i) (lt_of_le_of_lt (bitsP_le V L i) hL)
      (fun k' hk' => by
        rw [fld_bitsP V L i k' (by omega) (hLf k' hk')]
        split_ifs <;> norm_num)
    have m2 := fld_mul 32 (C i) K L hL (fun k' hk' => by
      rw [hLf k' hk', mul_one]; exact lt_trans (hC i) (by norm_num))
    rw [m1.2 k hk, m2.2 k hk, hb, hLf k hk, mul_one]
    split_ifs
    · rw [mul_one, show (16777215 : ℕ) = 2 ^ 24 - 1 by norm_num, Nat.and_comm,
        Nat.and_two_pow_sub_one_of_lt_two_pow (hC i)]
    · simp

/-- In every field: the parity of the low `n` bits of the field (as `0`/`1`). -/
def parP (Z L : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => parP Z L b ^^^ bitsP Z L b

theorem fld_parP (Z L K : ℕ) (hLf : ∀ k < K, fld 32 L k = 1) : ∀ n ≤ 32, ∀ k < K,
    fld 32 (parP Z L n) k = if bpar (fld 32 Z k) n then 1 else 0
  | 0, _, k, _ => by simp [parP, bpar, fld_zero_right_zero]
  | n + 1, hn, k, hk => by
    rw [parP, fld_xor, fld_parP Z L K hLf n (by omega) k hk,
      fld_bitsP Z L n k (by omega) (hLf k hk), bpar]
    cases bpar (fld 32 Z k) n <;> cases (fld 32 Z k).testBit n <;> rfl

/-- An exclusive or of bits is the parity. -/
theorem xorRange_bits (x : ℕ) : ∀ n,
    xorRange (fun b => if x.testBit b then 1 else 0) n = if bpar x n then 1 else 0
  | 0 => by simp [xorRange, bpar]
  | n + 1 => by
    rw [xorRange, xorRange_bits x n, bpar]
    cases bpar x n <;> cases x.testBit n <;> rfl

/-- The dot bit is the parity of the conjunction. -/
theorem identDot24_bit (a b : ℕ) : (identDot24 a b).testBit 0 = bpar (a &&& b) 24 := by
  rw [identDot24_eq]
  unfold monsterCo1GeometryBinaryMaskDot
  rw [maskSum_ofFn]
  rw [xorRange_congr _ (fun i => if (a &&& b).testBit i then 1 else 0) 24 (fun i hi => by
    simp only [hi, ↓reduceDIte, Nat.testBit_and]
    cases a.testBit i <;> cases b.testBit i <;> rfl), xorRange_bits]
  cases bpar (a &&& b) 24 <;> rfl

/-! ## The field-parallel check of a chunk -/

/-- The value check: target values against flipped source values, flips in bit `32 k` of `P`. -/
def valsP : List (ℕ × ℤ) → List (ℕ × ℤ) → ℕ → Bool
  | [], [], _ => true
  | s :: S, t :: T, P => (t.2 == if P.testBit 0 then -s.2 else s.2) && valsP S T (P >>> 32)
  | _, _, _ => false

theorem valsP_spec : ∀ (S T : List (ℕ × ℤ)) (P : ℕ), valsP S T P = true →
    S.length = T.length ∧ ∀ k (h1 : k < S.length) (h2 : k < T.length),
      T[k].2 = if P.testBit (32 * k) then -S[k].2 else S[k].2
  | [], [], _, _ => ⟨rfl, fun k h1 => absurd h1 (by simp)⟩
  | [], _ :: _, _, h => by simp [valsP] at h
  | _ :: _, [], _, h => by simp [valsP] at h
  | s :: S, t :: T, P, h => by
    simp only [valsP, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hl, hk⟩ := valsP_spec S T (P >>> 32) h.2
    refine ⟨by simp [hl], fun k h1 h2 => ?_⟩
    cases k with
    | zero => simpa using h.1
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [hk k (by simpa using h1) (by simpa using h2), Nat.testBit_shiftRight,
        show 32 + 32 * k = 32 * (k + 1) by omega]

/-- The field-parallel check of a chunk of at most `2^t` terms. -/
def chunkP (d : QMaskP) (t : ℕ) (S T : List (ℕ × ℤ)) : Bool :=
  d.ok && (S.length == T.length) && Nat.ble S.length (2 ^ t) &&
    S.all (fun s => Nat.blt s.1 98280) && T.all (fun s => Nat.blt s.1 98280) &&
    (imgP (fun i => fld 24 d.colsP i) (packM (S.map (fun s => identMaskG s.1))) (lowP t) 24 ==
      packM (T.map (fun s => identMaskG s.1))) &&
    valsP S T (parP ((imgP (fun i => fld 24 d.rowsP i) (packM (S.map (fun s => identMaskG s.1)))
      (lowP t) 24 ^^^ (d.coeff % 16777216) * lowP t) &&&
        packM (S.map (fun s => identMaskG s.1))) (lowP t) 24)

/-- A fast check of a list from its term checks. -/
theorem shortCheckF_of_forall (d : QMaskP) : ∀ S T : List (ℕ × ℤ), S.length = T.length →
    (∀ k (h1 : k < S.length) (h2 : k < T.length), shortTermCheckF d S[k] T[k] = true) →
    shortCheckF d S T = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | s :: S, t :: T, hl, h => by
    simp only [shortCheckF, Bool.and_eq_true]
    refine ⟨h 0 (by simp) (by simp), shortCheckF_of_forall d S T (by simpa using hl)
      (fun k h1 h2 => ?_)⟩
    have := h (k + 1) (by simpa using h1) (by simpa using h2)
    simpa using this

theorem identMaskG_lt (j : ℕ) : identMaskG j < 2 ^ 24 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem getD_map_mask (S : List (ℕ × ℤ)) (k : ℕ) (h : k < S.length) :
    (S.map (fun s => identMaskG s.1)).getD k 0 &&& 16777215 = identMaskG S[k].1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  simp only [Option.map_some, Option.getD_some]
  rw [show (16777215 : ℕ) = 2 ^ 24 - 1 by norm_num]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (identMaskG_lt _)

/-- A field-parallel chunk check is the fast check of the chunk. -/
theorem chunkP_sound (d : QMaskP) (t : ℕ) (S T : List (ℕ × ℤ)) (h : chunkP d t S T = true) :
    shortCheckF d S T = true := by
  simp only [chunkP, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, List.all_eq_true,
    Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hd, hlen⟩, hK⟩, hS⟩, hT⟩, hI⟩, hv⟩ := h
  have hd' := hd
  simp only [QMaskP.ok, Bool.and_eq_true, beq_iff_eq] at hd'
  set L := lowP t with hLdef
  set V := packM (S.map (fun s => identMaskG s.1)) with hVdef
  have hL := lowP_lt t
  have hLf : ∀ k < 2 ^ t, fld 32 L k = 1 := fun k hk => fld_lowP t k hk
  have hcols : ∀ j, fld 24 d.colsP j < 2 ^ 24 := fun j => fld_lt _ _ _
  have hrows : ∀ j, fld 24 d.rowsP j < 2 ^ 24 := fun j => fld_lt _ _ _
  obtain ⟨_, hvals⟩ := valsP_spec S T _ hv
  apply shortCheckF_of_forall d S T hlen
  intro k h1 h2
  have hkK : k < 2 ^ t := lt_of_lt_of_le h1 hK
  have hsl := hS S[k] (List.getElem_mem h1)
  have htl := hT T[k] (List.getElem_mem h2)
  -- the source mask
  have hVk : fld 32 V k = shortMaskF S[k].1 := by
    rw [hVdef, fld_packM, getD_map_mask S k h1, identMaskG_eq _ hsl]
  -- the image mask
  have hIk := fld_imgP _ hcols V L _ hL hLf 24 (by norm_num) k hkK
  rw [hI, fld_packM, getD_map_mask T k h2, identMaskG_eq _ htl, hVk] at hIk
  -- the central bit
  have hc' : (d.coeff % 16777216) * L < 2 ^ (32 * 2 ^ t) ∧ ∀ i < 2 ^ t,
      fld 32 ((d.coeff % 16777216) * L) i = (d.coeff % 16777216) * fld 32 L i :=
    fld_mul 32 _ _ L hL (fun i hi => by
      rw [hLf i hi, mul_one]
      exact lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))
  have hRk := fld_imgP _ hrows V L _ hL hLf 24 (by norm_num) k hkK
  have hPk := fld_parP ((imgP (fun i => fld 24 d.rowsP i) V L 24 ^^^
    (d.coeff % 16777216) * L) &&& V) L _ hLf 24 (by norm_num) k hkK
  rw [fld_land, fld_xor, hRk, hc'.2 k hkK, hLf k hkK, mul_one, hVk] at hPk
  have hbit := hvals k h1 h2
  rw [show 32 * k = 32 * k + 0 by rfl, ← Bool.true_and (Nat.testBit _ (32 * k + 0)),
    ← decide_eq_true (show 0 < 32 by norm_num), ← testBit_fld, hPk] at hbit
  -- assemble
  unfold shortTermCheckF QMaskP.stepP
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.false_xor]
  rw [selXorF_spec _ _ hd'.1, selXorF_spec _ _ hd'.2, identDot24_bit]
  refine ⟨hIk.symm, ?_⟩
  rw [hbit]
  have hpar : bpar ((xorRange (fun j => if (shortMaskF S[k].1).testBit j then
      fld 24 d.rowsP j else 0) 24 ^^^ d.coeff % 16777216) &&& shortMaskF S[k].1) 24 =
      bpar ((xorRange (fun j => if (shortMaskF S[k].1).testBit j then
      fld 24 d.rowsP j else 0) 24 ^^^ d.coeff) &&& shortMaskF S[k].1) 24 := by
    apply bpar_congr
    intro i hi
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor,
      show (16777216 : ℕ) = 2 ^ 24 by norm_num, Nat.testBit_mod_two_pow]
    simp [hi]
  rw [hpar]
  cases bpar ((xorRange (fun j => if (shortMaskF S[k].1).testBit j then
      fld 24 d.rowsP j else 0) 24 ^^^ d.coeff) &&& shortMaskF S[k].1) 24 <;> rfl

/-! ## Long lists in chunks -/

/-- A fast check splits at any position. -/
theorem shortCheckF_split (d : QMaskP) :
    ∀ (n : ℕ) (S T : List (ℕ × ℤ)), shortCheckF d (S.take n) (T.take n) = true →
      shortCheckF d (S.drop n) (T.drop n) = true → shortCheckF d S T = true
  | 0, S, T, _, h2 => by simpa using h2
  | n + 1, [], [], _, _ => rfl
  | n + 1, [], _ :: _, h1, _ => by simp [shortCheckF] at h1
  | n + 1, _ :: _, [], h1, _ => by simp [shortCheckF] at h1
  | n + 1, s :: S, t :: T, h1, h2 => by
    simp only [List.take_succ_cons, shortCheckF, Bool.and_eq_true] at h1
    simp only [List.drop_succ_cons] at h2
    simp only [shortCheckF, Bool.and_eq_true]
    exact ⟨h1.1, shortCheckF_split d n S T h1.2 h2⟩

/-- The field-parallel check of a long list in chunks of `2^t` terms, with `n` chunks of fuel. -/
def shortCheckPk (d : QMaskP) (t : ℕ) : ℕ → List (ℕ × ℤ) → List (ℕ × ℤ) → Bool
  | 0, S, T => S.isEmpty && T.isEmpty
  | n + 1, S, T => chunkP d t (S.take (2 ^ t)) (T.take (2 ^ t)) &&
      shortCheckPk d t n (S.drop (2 ^ t)) (T.drop (2 ^ t))

/-- The chunked field-parallel check is the fast check. -/
theorem shortCheckPk_sound (d : QMaskP) (t : ℕ) :
    ∀ (n : ℕ) (S T : List (ℕ × ℤ)), shortCheckPk d t n S T = true → shortCheckF d S T = true
  | 0, S, T, h => by
    simp only [shortCheckPk, Bool.and_eq_true, List.isEmpty_iff] at h
    rw [h.1, h.2]
    rfl
  | n + 1, S, T, h => by
    simp only [shortCheckPk, Bool.and_eq_true] at h
    exact shortCheckF_split d (2 ^ t) S T (chunkP_sound d t _ _ h.1)
      (shortCheckPk_sound d t n _ _ h.2)
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
