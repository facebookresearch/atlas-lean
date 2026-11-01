/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPair

/-! # The packed source sign letter

A packed implementation of the rational sign tensor operator
`generatedAxisGlobalRationalTensorSign a ε` (bound to `localTensorRepresentation
(generatedFifthSignFiber a ε)` by `generatedAxisGlobalRationalTensorSign_actual`).  Each output
column combines a translated half difference and a half sum of the input column with two sign
masks: the `Y` phase mask is built from the Golay weight bitset `qBits` and a linear mask, the
`Z` phase mask from the fold structure of `parkerThetaMask`.  The word action
`tensorWordAll` covers all four letter kinds, including sign letters. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-! ## Signs and parities -/

/-- The integral sign of a Boolean. -/
def bsg (b : Bool) : ℤ := if b then -1 else 1

/-- Signs multiply along exclusive or. -/
theorem bsg_xor (a b : Bool) : bsg (a ^^ b) = bsg a * bsg b := by
  cases a <;> cases b <;> decide

/-- A sign squares to one. -/
theorem bsg_sq (a : Bool) : bsg a * bsg a = 1 := by
  cases a <;> decide

/-- The integral sign of a `ZMod 2` value. -/
theorem intSign_bsg (c : ZMod 2) : generatedAxisGlobalIntSign c = bsg (decide (c = 1)) := by
  fin_cases c <;> decide

/-- The integral sign of a Boolean indicator. -/
theorem intSign_ite (b : Bool) :
    generatedAxisGlobalIntSign (if b = true then 1 else 0) = bsg b := by
  cases b <;> decide

/-- The spin dot product of two bit vectors given by naturals. -/
theorem spinDot_lab (X Y : ℕ) :
    spinDot (lab X) (lab Y) = if bpar (Y &&& X) 12 then 1 else 0 := by
  rw [← bpar_sum, spinDot, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [lab, Nat.testBit_and]
  cases X.testBit i.val <;> cases Y.testBit i.val <;> simp

/-- The integral sign of a spin dot product of bit vectors. -/
theorem intSign_spinDot_lab (X Y : ℕ) :
    generatedAxisGlobalIntSign (spinDot (lab X) (lab Y)) = bsg (bpar (Y &&& X) 12) := by
  rw [spinDot_lab, intSign_ite]

/-- Parity is additive over exclusive or. -/
theorem bpar_xor (X Y a : ℕ) :
    ∀ n, bpar ((X ^^^ Y) &&& a) n = (bpar (X &&& a) n ^^ bpar (Y &&& a) n) := by
  intro n
  induction n with
  | zero => simp [bpar]
  | succ n ih =>
    simp only [bpar, ih, Nat.testBit_and, Nat.testBit_xor]
    cases bpar (X &&& a) n <;> cases bpar (Y &&& a) n <;> cases X.testBit n <;>
      cases Y.testBit n <;> cases a.testBit n <;> rfl

/-- Parity of zero. -/
theorem bpar_zero (n : ℕ) : bpar 0 n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bpar, ih]

/-- Parity of a conjunction with zero. -/
theorem bpar_zero_and (a n : ℕ) : bpar (0 &&& a) n = false := by
  rw [Nat.zero_and]
  exact bpar_zero n

/-! ## Folds of exclusive ors -/

/-- Parity of an exclusive-or fold is the Boolean fold of the parities. -/
theorem bpar_foldl_xor {α : Type*} (g : α → ℕ) (a n : ℕ) : ∀ (L : List α) (m0 : ℕ),
    bpar ((L.foldl (fun m i => m ^^^ g i) m0) &&& a) n =
      L.foldl (fun b i => b ^^ bpar (g i &&& a) n) (bpar (m0 &&& a) n)
  | [], _ => rfl
  | i :: L, m0 => by
    simp only [List.foldl_cons]
    rw [bpar_foldl_xor g a n L (m0 ^^^ g i), bpar_xor]

/-- Parity of a nested exclusive-or fold. -/
theorem bpar_foldl_xor2 {α β : Type*} (h : α → β → ℕ) (L2 : List β) (a n : ℕ) :
    ∀ (L1 : List α) (m0 : ℕ),
    bpar ((L1.foldl (fun m i => L2.foldl (fun p j => p ^^^ h i j) m) m0) &&& a) n =
      L1.foldl (fun b i => L2.foldl (fun c j => c ^^ bpar (h i j &&& a) n) b)
        (bpar (m0 &&& a) n)
  | [], _ => rfl
  | i :: L1, m0 => by
    simp only [List.foldl_cons]
    rw [bpar_foldl_xor2 h L2 a n L1, bpar_foldl_xor (h i) a n L2 m0]

/-- The field mask of an exclusive-or fold of field masks. -/
theorem isFieldMask_foldl_xor {α : Type*} {w N : ℕ} (G : α → ℕ) (p : α → ℕ → Bool)
    (hG : ∀ i, IsFieldMask w N (G i) (fun k => p i k = true)) :
    ∀ (L : List α) (M0 : ℕ) (P0 : ℕ → Bool), IsFieldMask w N M0 (fun k => P0 k = true) →
    IsFieldMask w N (L.foldl (fun M i => M ^^^ G i) M0)
      (fun k => L.foldl (fun b i => b ^^ p i k) (P0 k) = true)
  | [], _, _, h0 => h0
  | i :: L, M0, P0, h0 => by
    simp only [List.foldl_cons]
    apply isFieldMask_foldl_xor G p hG L (M0 ^^^ G i) (fun k => P0 k ^^ p i k)
    refine (isFieldMask_xor h0 (hG i)).congr (fun k _ => ?_)
    cases P0 k <;> cases p i k <;> simp

/-- The field mask of a nested exclusive-or fold of field masks. -/
theorem isFieldMask_foldl_xor2 {α β : Type*} {w N : ℕ} (G : α → β → ℕ)
    (p : α → β → ℕ → Bool) (hG : ∀ i j, IsFieldMask w N (G i j) (fun k => p i j k = true))
    (L2 : List β) :
    ∀ (L1 : List α) (M0 : ℕ) (P0 : ℕ → Bool), IsFieldMask w N M0 (fun k => P0 k = true) →
    IsFieldMask w N (L1.foldl (fun M i => L2.foldl (fun Q j => Q ^^^ G i j) M) M0)
      (fun k => L1.foldl (fun b i => L2.foldl (fun c j => c ^^ p i j k) b) (P0 k) = true)
  | [], _, _, h0 => h0
  | i :: L1, M0, P0, h0 => by
    simp only [List.foldl_cons]
    exact isFieldMask_foldl_xor2 G p hG L2 L1 _ _
      (isFieldMask_foldl_xor (G i) (p i) (hG i) L2 M0 P0 h0)

/-! ## The theta fold mask -/

/-- The field mask of bit `i` of the low label `k % 2048`. -/
def lowBit (w i : ℕ) : ℕ := if i < 11 then bmask w 12 i else 0

/-- The low bit mask is a field mask. -/
theorem lowBit_isFieldMask (w i : ℕ) :
    IsFieldMask w (2 ^ 12) (lowBit w i) (fun k => (k % 2048).testBit i = true) := by
  unfold lowBit
  split_ifs with hi
  · refine (bmask_isFieldMask w 12 i (by omega)).congr (fun k _ => ?_)
    rw [show (2048 : ℕ) = 2 ^ 11 by norm_num, Nat.testBit_mod_two_pow]
    simp [hi]
  · refine (zero_isFieldMask w _).congr (fun k _ => ?_)
    rw [show (2048 : ℕ) = 2 ^ 11 by norm_num, Nat.testBit_mod_two_pow]
    simp [hi]

/-- The linear theta terms of the `Z` phase mask. -/
def zG1 (w a : ℕ) (i : Fin 12) : ℕ :=
  if bpar (parkerBasisThetaMasks i &&& a) 12 = true then lowBit w i.val else 0

/-- The linear theta predicates. -/
def zP1 (a : ℕ) (i : Fin 12) (k : ℕ) : Bool :=
  bpar ((if (k % 2048).testBit i.val then parkerBasisThetaMasks i else 0) &&& a) 12

/-- The linear theta terms are field masks. -/
theorem zG1_isFieldMask (w a : ℕ) (i : Fin 12) :
    IsFieldMask w (2 ^ 12) (zG1 w a i) (fun k => zP1 a i k = true) := by
  unfold zG1
  split_ifs with h
  · refine (lowBit_isFieldMask w i.val).congr (fun k _ => ?_)
    unfold zP1
    cases hb : (k % 2048).testBit i.val <;> simp [h, bpar_zero]
  · refine (zero_isFieldMask w _).congr (fun k _ => ?_)
    unfold zP1
    cases hb : (k % 2048).testBit i.val <;> simp [h, bpar_zero]

/-- The quadratic associator terms of the `Z` phase mask. -/
def zG2 (w a : ℕ) (i j : Fin 12) : ℕ :=
  if i < j ∧ bpar (parkerBasisAssociatorMasks i j &&& a) 12 = true then
    lowBit w i.val &&& lowBit w j.val else 0

/-- The quadratic associator predicates. -/
def zP2 (a : ℕ) (i j : Fin 12) (k : ℕ) : Bool :=
  bpar ((if i < j ∧ (k % 2048).testBit i.val ∧ (k % 2048).testBit j.val then
    parkerBasisAssociatorMasks i j else 0) &&& a) 12

/-- The quadratic associator terms are field masks. -/
theorem zG2_isFieldMask (w a : ℕ) (i j : Fin 12) :
    IsFieldMask w (2 ^ 12) (zG2 w a i j) (fun k => zP2 a i j k = true) := by
  unfold zG2
  split_ifs with h
  · refine (isFieldMask_and (lowBit_isFieldMask w i.val) (lowBit_isFieldMask w j.val)).congr
      (fun k _ => ?_)
    unfold zP2
    cases hb1 : (k % 2048).testBit i.val <;> cases hb2 : (k % 2048).testBit j.val <;>
      simp [h.1, h.2, bpar_zero]
  · refine (zero_isFieldMask w _).congr (fun k _ => ?_)
    unfold zP2
    by_cases hij : i < j
    · have h' : bpar (parkerBasisAssociatorMasks i j &&& a) 12 = false := by
        simpa [hij] using h
      cases hb1 : (k % 2048).testBit i.val <;> cases hb2 : (k % 2048).testBit j.val <;>
        simp [hij, h', bpar_zero]
    · simp [hij, bpar_zero]

/-- The theta fold mask: the parity of `θ(k % 2048) ∧ a` as a field mask. -/
def signZFold (w a : ℕ) : ℕ :=
  (List.finRange 12).foldl (fun M i => M ^^^ zG1 w a i)
    ((List.finRange 12).foldl
      (fun M i => (List.finRange 12).foldl (fun N j => N ^^^ zG2 w a i j) M) 0)

/-- The predicate of the theta fold mask. -/
def zFoldPred (a k : ℕ) : Bool :=
  (List.finRange 12).foldl (fun b i => b ^^ zP1 a i k)
    ((List.finRange 12).foldl
      (fun b i => (List.finRange 12).foldl (fun c j => c ^^ zP2 a i j k) b) false)

/-- The theta fold mask is a field mask. -/
theorem signZFold_isFieldMask (w a : ℕ) :
    IsFieldMask w (2 ^ 12) (signZFold w a) (fun k => zFoldPred a k = true) := by
  have h0 := isFieldMask_foldl_xor2 (zG2 w a) (zP2 a) (zG2_isFieldMask w a) (List.finRange 12)
    (List.finRange 12) 0 (fun _ => false) ((zero_isFieldMask w _).congr (fun k _ => by simp))
  exact isFieldMask_foldl_xor (zG1 w a) (zP1 a) (zG1_isFieldMask w a) (List.finRange 12) _ _ h0

/-- The theta fold predicate is the parity of the theta mask of the low label. -/
theorem zFoldPred_eq (a k : ℕ) : zFoldPred a k = bpar (parkerThetaMask (k % 2048) &&& a) 12 := by
  rw [parkerThetaMask, bpar_foldl_xor, bpar_foldl_xor2, bpar_zero_and]
  rfl

/-! ## The two sign masks -/

/-- The `Z` phase mask. -/
def signZMask (w a : ℕ) : ℕ :=
  signZFold w a ^^^ linMask w 12 (parkerThetaMask a &&& 2047) false 12

/-- The `Z` phase predicate. -/
def zPred (a k : ℕ) : Bool := zFoldPred a k ^^ bpar (k &&& (parkerThetaMask a &&& 2047)) 12

/-- The `Z` phase mask is a field mask. -/
theorem signZMask_isFieldMask (w a : ℕ) :
    IsFieldMask w (2 ^ 12) (signZMask w a) (fun k => zPred a k = true) := by
  refine (isFieldMask_xor (signZFold_isFieldMask w a)
    (linMask_isFieldMask w 12 (parkerThetaMask a &&& 2047) false 12 le_rfl)).congr
    (fun k _ => ?_)
  simp only [zPred, Bool.false_xor]
  cases zFoldPred a k <;> cases bpar (k &&& (parkerThetaMask a &&& 2047)) 12 <;> simp

/-- The constant part of the `Y` phase. -/
def signC0 (a : ℕ) (ε : ZMod 2) : Bool := decide (ε = 1) ^^ qPred a

/-- The `Y` phase mask. -/
def signYMask (w a : ℕ) (ε : ZMod 2) : ℕ :=
  linMask w 12 (parkerThetaMask a &&& 2047) (signC0 a ε) 12 ^^^ bmask w 12 11 ^^^
    spread w qBits (2 ^ 12)

/-- The `Y` phase predicate. -/
def yPred (a : ℕ) (ε : ZMod 2) (k : ℕ) : Bool :=
  (signC0 a ε ^^ bpar (k &&& (parkerThetaMask a &&& 2047)) 12) ^^ k.testBit 11 ^^
    qBits.testBit k

/-- The `Y` phase mask is a field mask. -/
theorem signYMask_isFieldMask (w a : ℕ) (ε : ZMod 2) :
    IsFieldMask w (2 ^ 12) (signYMask w a ε) (fun k => yPred a ε k = true) := by
  have h1 := linMask_isFieldMask w 12 (parkerThetaMask a &&& 2047) (signC0 a ε) 12 le_rfl
  have h2 := bmask_isFieldMask w 12 11 (by norm_num)
  have h3 := spread_isFieldMask w (2 ^ 12) qBits
  refine ((isFieldMask_xor (isFieldMask_xor h1 h2) h3)).congr (fun k _ => ?_)
  simp only [yPred]
  cases (signC0 a ε ^^ bpar (k &&& (parkerThetaMask a &&& 2047)) 12) <;>
    cases k.testBit 11 <;> cases qBits.testBit k <;> simp

/-! ## The packed sign letter -/

/-- The packed source sign letter on column `j`, on numerators over twice the denominator. -/
def colSign (w a : ℕ) (ε : ZMod 2) (j : ℕ) (x : SVec) : SVec :=
  sadd
    (scond (bpar (a % 2048 &&& gcol j) 12)
      (sflip (allMask w (2 ^ 12)) (signYMask w a ε)
        (strs w 12 (bitsOf (a % 2048))
          (sflip (allMask w (2 ^ 12)) (spread w qBits (2 ^ 12)) (colHalf w true x)))))
    (scond (bpar (gcol j &&& a) 12)
      (sflip (allMask w (2 ^ 12)) (signZMask w a) (colHalf w false x)))

/-- Selective negation as multiplication by a sign. -/
theorem ite_neg_bsg (b : Bool) (v : ℤ) : (if b = true then -v else v) = bsg b * v := by
  cases b <;> simp [bsg]

/-- The packed sign letter on one column: bounds and values. -/
theorem colSign_spec {w B : ℕ} (a : ℕ) (ε : ZMod 2) (j : ℕ) {x : SVec}
    (hx : SBnd w (2 ^ 12) B x) (hB : 8 * B < 2 ^ w) :
    SBnd w (2 ^ 12) (8 * B) (colSign w a ε j x) ∧ ∀ k < 4096,
      sval w (colSign w a ε j x) k =
        bsg (bpar (a % 2048 &&& gcol j) 12) * bsg (yPred a ε k) *
          bsg (qBits.testBit (k ^^^ a % 2048)) *
            (sval w x ((k ^^^ a % 2048) % 2048) - sval w x ((k ^^^ a % 2048) % 2048 + 2048)) +
        bsg (bpar (gcol j &&& a) 12) * bsg (zPred a k) *
          (sval w x (k % 2048) + sval w x (k % 2048 + 2048)) := by
  have hB4 : 4 * B < 2 ^ w := by omega
  have ha0 : a % 2048 < 4096 := by omega
  obtain ⟨h1, v1⟩ := colHalf_spec true hx hB4
  obtain ⟨h2, v2⟩ := sflip_spec h1 _ _ (spread_isFieldMask w (2 ^ 12) qBits) hB4
  obtain ⟨h3, v3⟩ := strs_spec (bitsOf (a % 2048)) h2 (bitsOf_lt _)
  obtain ⟨h4, v4⟩ := sflip_spec h3 _ _ (signYMask_isFieldMask w a ε) hB4
  obtain ⟨h5, v5⟩ := scond_spec (bpar (a % 2048 &&& gcol j) 12) h4
  obtain ⟨g1, u1⟩ := colHalf_spec false hx hB4
  obtain ⟨g2, u2⟩ := sflip_spec g1 _ _ (signZMask_isFieldMask w a) hB4
  obtain ⟨g3, u3⟩ := scond_spec (bpar (gcol j &&& a) 12) g2
  obtain ⟨s1, s2⟩ := sadd_spec h5 g3 (by omega)
  refine ⟨by
    have e : 4 * B + 4 * B = 8 * B := by ring
    rw [← e]; exact s1, fun k hk => ?_⟩
  have hk' : k < 2 ^ 12 := by norm_num; exact hk
  have hxk : k ^^^ a % 2048 < 4096 := Nat.xor_lt_two_pow (n := 12) hk ha0
  have hxk' : k ^^^ a % 2048 < 2 ^ 12 := by norm_num; exact hxk
  unfold colSign
  rw [s2 k hk', v5, v4 k hk', v3 k hk', xorBits_bitsOf _ ha0, v2 _ hxk', v1 _ hxk,
    u3, u2 k hk', u1 k hk, ite_neg_bsg, ite_neg_bsg, ite_neg_bsg]
  simp only [bsg, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> ring

/-- The packed source sign letter on a packed tensor, on numerators over twice the
denominator. -/
def tensorSign (w a : ℕ) (ε : ZMod 2) (X : List SVec) : List SVec :=
  (List.range 24).map (fun j => colSign w a ε j (tcol X j))

/-- Columns of the packed sign letter. -/
theorem tcol_tensorSign (w a : ℕ) (ε : ZMod 2) (X : List SVec) (j : ℕ) (hj : j < 24) :
    tcol (tensorSign w a ε X) j = colSign w a ε j (tcol X j) :=
  tcol_range_map _ 24 j hj

/-- Bounds of the packed sign letter. -/
theorem tensorSign_bnd {w B : ℕ} (a : ℕ) (ε : ZMod 2) {X : List SVec} (hX : TBnd w B X)
    (hB : 8 * B < 2 ^ w) : TBnd w (8 * B) (tensorSign w a ε X) := by
  intro j hj
  rw [tcol_tensorSign w a ε X j hj]
  exact (colSign_spec a ε j (hX j hj) hB).1

/-! ## Binding to the rational sign operator -/

/-- Low residues of exclusive ors. -/
theorem xor_mod2048 (x y : ℕ) : (x ^^^ y) % 2048 = x % 2048 ^^^ y % 2048 := by
  rw [show (2048 : ℕ) = 2 ^ 11 by norm_num, Nat.xor_mod_two_pow]

/-- The low label of the translated output label is the sign input code. -/
theorem signInput_val (a k : Fin 4096) :
    (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k)).val =
      k.val % 2048 ^^^ a.val % 2048 := by
  change (k.val % 2048 ^^^ a.val) % 2048 = _
  rw [xor_mod2048, Nat.mod_mod]

/-- The translated label reduces to the sign input code. -/
theorem xor_low_val (a k : Fin 4096) :
    (k.val ^^^ a.val % 2048) % 2048 =
      (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k)).val := by
  rw [signInput_val, xor_mod2048, Nat.mod_mod]

/-- The low label value. -/
theorem spinLabelLow_val (k : Fin 4096) : (generatedAxisGlobalSpinLabelLow k).val = k.val % 2048 :=
  rfl

/-- Bit `11` of a label as a sign. -/
theorem intSign_coeff11 (k : Fin 4096) :
    generatedAxisGlobalIntSign (golayLabelCoefficients k 11) = bsg (k.val.testBit 11) :=
  intSign_ite _

/-- The code coordinate sign as a parity sign. -/
theorem codeSign_bsg (d : Fin 2048) (i : Fin 24) :
    generatedAxisGlobalCodeSign d i = bsg (bpar (d.val &&& gcol i.val) 12) := by
  rw [generatedAxisGlobalCodeSign, golayEncodedMask_testBit]
  rfl

/-- The Golay weight phase as a sign. -/
theorem intSign_weight_bsg (d : ℕ) :
    generatedAxisGlobalIntSign ((golayMaskWeight (golayEncodedMask d) / 4 : ℕ) : ZMod 2) =
      bsg (qPred d) :=
  intSign_weight d

/-- The source theta word as a bit vector. -/
theorem sourceWordTheta_lab (a : Fin 4096) : sourceWordTheta a = lab (parkerThetaMask a.val) :=
  rfl

/-- The low dictionary row as a bit vector. -/
theorem fifthSpinLow_lab (e : Fin 2048) : generatedFifthSpinLow e = lab e.val := rfl

/-- Label coefficients as a bit vector. -/
theorem coeff_lab (k : Fin 4096) : golayLabelCoefficients k = lab k.val := rfl

/-- The generator coordinate column as a bit vector. -/
theorem genCol_lab (i : Fin 24) :
    (fun k => (golayGeneratorBit k i : ZMod 2)) = lab (gcol i.val) := by
  funext k
  rw [lab, gcol_testBit i.val k.val k.isLt]
  have hg : gmask k.val = golayGeneratorMasks k := by simp [gmask]
  rw [hg, golayGeneratorBit]
  split_ifs <;> simp

/-- The four signs of the difference term of the sign operator. -/
theorem sign_diff_term (a : Fin 4096) (ε : ZMod 2) (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      generatedAxisGlobalCodeSign (generatedAxisGlobalSpinLabelLow k) i *
      generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase a ε
        (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k))
        (generatedAxisGlobalSpinLabelLow k)) *
      generatedAxisGlobalCodeSign
        (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k)) i =
    bsg (bpar (a.val % 2048 &&& gcol i.val) 12) * bsg (yPred a.val ε k.val) *
      bsg (qBits.testBit (k.val ^^^ a.val % 2048)) := by
  have hq : qBits.testBit (k.val ^^^ a.val % 2048) =
      qPred (k.val % 2048 ^^^ a.val % 2048) := by
    have h := qBits_spec ⟨k.val ^^^ a.val % 2048,
      Nat.xor_lt_two_pow (n := 12) k.isLt (by omega)⟩
    rw [h, xor_mod2048, Nat.mod_mod]
  rw [intSign_coeff11, codeSign_bsg, codeSign_bsg, signInput_val, generatedAxisGlobalSignYPhase,
    intSign_add, intSign_add, intSign_add, intSign_add, intSign_bsg ε, intSign_weight_bsg,
    intSign_weight_bsg, intSign_weight_bsg, signInput_val, sourceWordTheta_lab, fifthSpinLow_lab,
    intSign_spinDot_lab]
  simp only [spinLabelLow_val, hq, yPred, signC0, bsg_xor, bpar_xor, qBits_spec k, bpar_low]
  linear_combination (bsg (k.val.testBit 11) * bsg (bpar (a.val % 2048 &&& gcol i.val) 12) *
    bsg (decide (ε = 1)) * bsg (qPred a.val) *
    bsg (bpar (k.val % 2048 &&& parkerThetaMask a.val) 12) *
    bsg (qPred (k.val % 2048 ^^^ a.val % 2048)) * bsg (qPred (k.val % 2048))) *
    bsg_sq (bpar (k.val % 2048 &&& gcol i.val) 12)

/-- The sign of the sum term of the sign operator. -/
theorem sign_sum_term (a : Fin 4096) (k : Fin 4096) (i : Fin 24) :
    generatedAxisGlobalIntSign
        (generatedAxisGlobalSignZPhase a (generatedAxisGlobalSpinLabelLow k) i) =
      bsg (bpar (gcol i.val &&& a.val) 12) * bsg (zPred a.val k.val) := by
  rw [generatedAxisGlobalSignZPhase, intSign_add, intSign_add, genCol_lab, coeff_lab, coeff_lab,
    sourceWordTheta_lab, sourceWordTheta_lab, intSign_spinDot_lab, intSign_spinDot_lab,
    intSign_spinDot_lab]
  simp only [zPred, bsg_xor, zFoldPred_eq, bpar_low, spinLabelLow_val]
  rw [Nat.and_comm (parkerThetaMask a.val)]
  ring

/-- The packed sign letter computes the rational source sign operator. -/
theorem tensorSign_rat {w B : ℕ} (a : Fin 4096) (ε : ZMod 2) {X : List SVec} (hX : TBnd w B X)
    (hB : 8 * B < 2 ^ w) (D : ℚ) :
    tensorRat w (tensorSign w a.val ε X) (2 * D) =
      generatedAxisGlobalRationalTensorSign a ε (tensorRat w X D) := by
  funext k i
  simp only [tensorRat, generatedAxisGlobalRationalTensorSign]
  rw [tcol_tensorSign w a.val ε X i.val i.isLt,
    (colSign_spec a.val ε i.val (hX i.val i.isLt) hB).2 k.val k.isLt, xor_low_val]
  have h1 := sign_diff_term a ε k i
  have h2 := sign_sum_term a k i
  have h1q : ((generatedAxisGlobalIntSign (golayLabelCoefficients k 11) : ℤ) : ℚ) *
      (generatedAxisGlobalCodeSign (generatedAxisGlobalSpinLabelLow k) i : ℚ) *
      (generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase a ε
        (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k))
        (generatedAxisGlobalSpinLabelLow k)) : ℚ) *
      (generatedAxisGlobalCodeSign
        (generatedAxisGlobalSignInputCode a (generatedAxisGlobalSpinLabelLow k)) i : ℚ) =
      ((bsg (bpar (a.val % 2048 &&& gcol i.val) 12) * bsg (yPred a.val ε k.val) *
        bsg (qBits.testBit (k.val ^^^ a.val % 2048)) : ℤ) : ℚ) := by
    exact_mod_cast h1
  have h2q : ((generatedAxisGlobalIntSign
        (generatedAxisGlobalSignZPhase a (generatedAxisGlobalSpinLabelLow k) i) : ℤ) : ℚ) =
      ((bsg (bpar (gcol i.val &&& a.val) 12) * bsg (zPred a.val k.val) : ℤ) : ℚ) := by
    exact_mod_cast h2
  rw [h1q, h2q]
  simp only [generatedAxisGlobalTensorLowLabel, generatedAxisGlobalTensorHighLabel,
    generatedAxisGlobalSpinLabelLow]
  push_cast
  ring

/-! ## Words with sign letters -/

/-- The packed tensor action of one letter. -/
def tensorLetterAll (w : ℕ) : IdentLetter → List SVec → List SVec
  | .sign a ε, X => tensorSign w a.val ε X
  | l, X => tensorLetter w l X

/-- The denominator factor of one letter. -/
def letterDenAll : IdentLetter → ℕ
  | .sign _ _ => 2
  | l => letterDen l

/-- The field bound growth factor of one letter. -/
def letterGrowthAll : IdentLetter → ℕ
  | .sign _ _ => 8
  | l => letterGrowth l

/-- The packed tensor action of a word: the last letter acts first. -/
def tensorWordAll (w : ℕ) : List IdentLetter → List SVec → List SVec
  | [], X => X
  | l :: ls, X => tensorLetterAll w l (tensorWordAll w ls X)

/-- The denominator factor of a word. -/
def tensorWordDenAll : List IdentLetter → ℕ
  | [] => 1
  | l :: ls => letterDenAll l * tensorWordDenAll ls

/-- The field bound growth factor of a word. -/
def tensorWordGrowthAll : List IdentLetter → ℕ
  | [] => 1
  | l :: ls => letterGrowthAll l * tensorWordGrowthAll ls

/-- One letter: bounds and the genuine tensor action. -/
theorem tensorLetterAll_actual {w B : ℕ} (l : IdentLetter) {X : List SVec} (hX : TBnd w B X)
    (hB : letterGrowthAll l * B < 2 ^ w) (D : ℚ) :
    TBnd w (letterGrowthAll l * B) (tensorLetterAll w l X) ∧
      localTensorRepresentation l.fiber
        (generatedAxisGlobalRationalTensorReal (tensorRat w X D)) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat w (tensorLetterAll w l X) (letterDenAll l * D)) := by
  cases l with
  | sign a ε =>
    have hB' : 8 * B < 2 ^ w := by simpa [letterGrowthAll] using hB
    refine ⟨by simpa [letterGrowthAll, tensorLetterAll] using tensorSign_bnd a.val ε hX hB', ?_⟩
    simp only [IdentLetter.fiber, tensorLetterAll, letterDenAll, Nat.cast_ofNat]
    rw [tensorSign_rat a ε hX hB']
    exact generatedAxisGlobalRationalTensorSign_actual _ a ε
  | xi => exact tensorLetter_actual .xi rfl hX hB D
  | mono l => exact tensorLetter_actual (.mono l) rfl hX hB D
  | qel g => exact tensorLetter_actual (.qel g) rfl hX hB D

/-- A word: bounds and the genuine tensor action of the whole word. -/
theorem tensorWordAll_actual {w B : ℕ} : ∀ (ls : List IdentLetter) {X : List SVec},
    TBnd w B X → tensorWordGrowthAll ls * B < 2 ^ w → ∀ (D : ℚ),
    TBnd w (tensorWordGrowthAll ls * B) (tensorWordAll w ls X) ∧
      localTensorRepresentation (identWordFiber ls)
        (generatedAxisGlobalRationalTensorReal (tensorRat w X D)) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat w (tensorWordAll w ls X) (tensorWordDenAll ls * D))
  | [], X, hX, _, D => by
    refine ⟨by simpa [tensorWordGrowthAll, tensorWordAll] using hX, ?_⟩
    simp [identWordFiber, tensorWordAll, tensorWordDenAll]
  | l :: ls, X, hX, hB, D => by
    have hpos : 0 < letterGrowthAll l := by
      cases l <;> simp [letterGrowthAll, letterGrowth]
    have hB1 : tensorWordGrowthAll ls * B < 2 ^ w := by
      simp only [tensorWordGrowthAll] at hB
      calc tensorWordGrowthAll ls * B ≤ letterGrowthAll l * (tensorWordGrowthAll ls * B) :=
            Nat.le_mul_of_pos_left _ hpos
        _ = letterGrowthAll l * tensorWordGrowthAll ls * B := by ring
        _ < 2 ^ w := hB
    obtain ⟨h1, h2⟩ := tensorWordAll_actual ls hX hB1 D
    have hB2 : letterGrowthAll l * (tensorWordGrowthAll ls * B) < 2 ^ w := by
      simp only [tensorWordGrowthAll] at hB; linarith [hB]
    obtain ⟨h3, h4⟩ := tensorLetterAll_actual l h1 hB2 (tensorWordDenAll ls * D)
    refine ⟨by simpa [tensorWordGrowthAll, tensorWordAll, Nat.mul_assoc] using h3, ?_⟩
    have hfib : identWordFiber (l :: ls) = l.fiber * identWordFiber ls := by
      simp [identWordFiber]
    rw [hfib, map_mul, LinearEquiv.mul_apply, h2, h4]
    simp only [tensorWordAll, tensorWordDenAll, Nat.cast_mul, mul_assoc]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
