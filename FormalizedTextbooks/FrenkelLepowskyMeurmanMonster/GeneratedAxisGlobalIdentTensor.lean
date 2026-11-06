/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPacked
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorWord

/-! # Packed tensor letters

A packed tensor is a list of 24 signed packed columns, each with `4096` fields indexed by the
original spin labels.  This module gives packed implementations of the existing rational
tensor operators (`generatedAxisGlobalRationalTensorQ`, ...), whose `_actual` lemmas bind them
to `localTensorRepresentation`.  Every packed operation is proved to compute the rational
formula exactly, under explicit field bounds. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-- Column `i` of a packed tensor (zero outside the list). -/
def tcol (X : List SVec) (i : ℕ) : SVec := X.getD i szero

/-- The rational tensor of packed numerators `X` over the denominator `D`. -/
def tensorRat (w : ℕ) (X : List SVec) (D : ℚ) : GeneratedAxisGlobalRationalTensor :=
  fun k i => (sval w (tcol X i.val) k.val : ℚ) / D

/-- All 24 columns of a packed tensor satisfy the field bound `B`. -/
def TBnd (w B : ℕ) (X : List SVec) : Prop := ∀ i < 24, SBnd w (2 ^ 12) B (tcol X i)

/-- Spin labels add by exclusive or. -/
theorem spinLabel_add_coeff (k m : Fin 4096) :
    (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + golayLabelCoefficients m)).val =
      k.val ^^^ m.val := by
  have hlt : k.val ^^^ m.val < 4096 := Nat.xor_lt_two_pow (n := 12) k.isLt m.isLt
  have h : golayLabelCoefficients k + golayLabelCoefficients m =
      golayLabelCoefficients ⟨k.val ^^^ m.val, hlt⟩ := by
    funext j
    simp only [golayLabelCoefficients, Pi.add_apply, Nat.testBit_xor]
    cases k.val.testBit j.val <;> cases m.val.testBit j.val <;> decide
  rw [h, generatedAxisGlobalSpinLabel_coeff]

/-- Spin labels of a sum with an arbitrary spin vector. -/
theorem spinLabel_add (k : Fin 4096) (t : SpinIndex) :
    (generatedAxisGlobalSpinLabel (golayLabelCoefficients k + t)).val =
      k.val ^^^ (generatedAxisGlobalSpinLabel t).val := by
  conv_lhs => rw [← generatedAxisGlobalSpinLabel_decode t]
  exact spinLabel_add_coeff k _

/-! ## Linear sign masks -/

/-- Parity of the low `j` bits of `x`. -/
def bpar (x : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => bpar x j ^^ x.testBit j

/-- The field mask of `{t : c xor parity of the low j bits of (t AND m)}`. -/
def linMask (w K m : ℕ) (c : Bool) : ℕ → ℕ
  | 0 => if c then allMask w (2 ^ K) else 0
  | j + 1 => linMask w K m c j ^^^ (if m.testBit j then bmask w K j else 0)

/-- Exclusive or of two full-or-zero fields. -/
theorem ite_xor_ite (a b : Bool) (F : ℕ) :
    ((if a = true then F else 0) ^^^ (if b = true then F else 0)) =
      if (a ^^ b) = true then F else 0 := by
  cases a <;> cases b <;> simp

/-- A linear mask is the field mask of its parity predicate. -/
theorem linMask_isFieldMask (w K m : ℕ) (c : Bool) : ∀ j, j ≤ K →
    IsFieldMask w (2 ^ K) (linMask w K m c j) (fun t => (c ^^ bpar (t &&& m) j) = true) := by
  intro j
  induction j with
  | zero =>
    intro _ t ht
    cases c <;> simp [linMask, bpar, fld_allMask, ht, fld_zero_right_zero]
  | succ j ih =>
    intro hj t ht
    have h1 := ih (by omega) t ht
    simp only [linMask, fld_xor, h1, bpar, Nat.testBit_and]
    by_cases hm : m.testBit j
    · simp only [hm, ↓reduceIte, Bool.and_true, fld_bmask w K j t (by omega) ht]
      rw [ite_xor_ite, Bool.xor_assoc]
    · have hm' : m.testBit j = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ↓reduceIte, fld_zero_right_zero, Nat.xor_zero,
        Bool.and_false, Bool.xor_false]

/-- Low-bit parity as a sum in `ZMod 2`. -/
theorem bpar_sum (x : ℕ) : ∀ j : ℕ,
    (∑ i ∈ Finset.range j, (if x.testBit i then (1 : ZMod 2) else 0)) =
      if bpar x j then 1 else 0 := by
  intro j
  induction j with
  | zero => simp [bpar]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, bpar]
    cases bpar x j <;> cases x.testBit j <;> decide

/-- The spin dot product of two labels is the parity of their conjunction. -/
theorem spinDot_coeff (m k : Fin 4096) :
    spinDot (golayLabelCoefficients m) (golayLabelCoefficients k) =
      if bpar (k.val &&& m.val) 12 then 1 else 0 := by
  rw [← bpar_sum, spinDot, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [golayLabelCoefficients, Nat.testBit_and]
  cases m.val.testBit i.val <;> cases k.val.testBit i.val <;> simp

/-! ## The extraspecial letter -/

/-- The set bits of `m` below `j`, highest first. -/
def bitsBelow (m : ℕ) : ℕ → List ℕ
  | 0 => []
  | j + 1 => if m.testBit j then j :: bitsBelow m j else bitsBelow m j

/-- The set bits of a twelve-bit mask. -/
def bitsOf (m : ℕ) : List ℕ := bitsBelow m 12

/-- The residue modulo `2^(j+1)` adds bit `j`. -/
theorem mod_two_pow_succ_xor (m j : ℕ) :
    m % 2 ^ (j + 1) = (if m.testBit j then 2 ^ j else 0) ^^^ m % 2 ^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow]
  rcases lt_trichotomy i j with h | h | h
  · have h1 : i < j + 1 := by omega
    split_ifs <;> simp [h, h1, Nat.ne_of_gt h]
  · subst h
    split_ifs with hm <;> simp [hm]
  · have h1 : ¬ i < j + 1 := by omega
    have h2 : ¬ i < j := by omega
    split_ifs <;> simp [h1, h2, Nat.ne_of_lt h]

/-- The bits below `j` recompose the residue modulo `2^j`. -/
theorem xorBits_bitsBelow (m : ℕ) : ∀ j, xorBits (bitsBelow m j) = m % 2 ^ j := by
  intro j
  induction j with
  | zero => simp [bitsBelow, xorBits, Nat.mod_one]
  | succ j ih =>
    rw [mod_two_pow_succ_xor, bitsBelow]
    split_ifs with hm
    · simp [xorBits, ih]
    · simp [ih]

/-- The bits of a twelve-bit mask recompose it. -/
theorem xorBits_bitsOf (m : ℕ) (hm : m < 4096) : xorBits (bitsOf m) = m := by
  rw [bitsOf, xorBits_bitsBelow]
  exact Nat.mod_eq_of_lt hm

/-- All listed bits are below `j`. -/
theorem bitsBelow_lt (m : ℕ) : ∀ j, ∀ k ∈ bitsBelow m j, k < j := by
  intro j
  induction j with
  | zero => simp [bitsBelow]
  | succ j ih =>
    intro k hk
    simp only [bitsBelow] at hk
    split_ifs at hk
    · rcases List.mem_cons.mp hk with h | h
      · omega
      · have := ih k h; omega
    · have := ih k hk; omega

/-- All listed bits are below twelve. -/
theorem bitsOf_lt (m : ℕ) : ∀ k ∈ bitsOf m, k < 12 := bitsBelow_lt m 12

/-- The translation label of an extraspecial element. -/
def qTransl (q : Q) : ℕ := (generatedAxisGlobalSpinLabel (spinTranslation q)).val

/-- The modulation label of an extraspecial element. -/
def qModul (q : Q) : ℕ := (generatedAxisGlobalSpinLabel (spinModulation q)).val

/-- The central bit of an extraspecial element. -/
def qCentralBit (q : Q) : Bool := decide (toAdd q.coeff = 1)

/-- The packed extraspecial action on one column. -/
def colQ (w : ℕ) (q : Q) (x : SVec) : SVec :=
  sflip (allMask w (2 ^ 12)) (linMask w 12 (qModul q) (qCentralBit q) 12)
    (strs w 12 (bitsOf (qTransl q)) x)

/-- The packed extraspecial action on a tensor. -/
def tensorQ (w : ℕ) (q : Q) (X : List SVec) : List SVec := X.map (colQ w q)

theorem tcol_map (f : SVec → SVec) (hf : f szero = szero) (X : List SVec) (i : ℕ) :
    tcol (X.map f) i = f (tcol X i) := by
  unfold tcol
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases X[i]? <;> simp [hf]

/-- Adding a Boolean indicator in `ZMod 2` is an exclusive or. -/
theorem zmod2_add_ite : ∀ (c : ZMod 2) (b : Bool),
    (c + if b = true then 1 else 0) = if (decide (c = 1) ^^ b) = true then 1 else 0 := by
  decide

/-- The extraspecial phase in label form. -/
theorem spinPhase_coeff (q : Q) (k : Fin 4096) :
    spinPhase q (golayLabelCoefficients k) =
      if (qCentralBit q ^^ bpar (k.val &&& qModul q) 12) then 1 else 0 := by
  have hm : spinModulation q = golayLabelCoefficients
      (generatedAxisGlobalSpinLabel (spinModulation q)) :=
    (generatedAxisGlobalSpinLabel_decode _).symm
  rw [spinPhase, hm, spinDot_coeff]
  change (toAdd q.coeff + if bpar (k.val &&& qModul q) 12 then 1 else 0) =
    if (qCentralBit q ^^ bpar (k.val &&& qModul q) 12) then 1 else 0
  simp only [qCentralBit]
  exact zmod2_add_ite _ _

/-- Translations of the zero vector vanish. -/
theorem strs_zero (W K : ℕ) : ∀ ks : List ℕ, strs W K ks szero = szero
  | [] => rfl
  | k :: ks => by
    have h : str W K k szero = szero := by
      simp only [str, szero, tr, Nat.zero_and, Nat.zero_shiftLeft, Nat.zero_shiftRight,
        Nat.zero_or]
    rw [strs, h, strs_zero W K ks]

/-- The packed column action of an extraspecial element: bounds and values. -/
theorem colQ_spec {w B : ℕ} (q : Q) {x : SVec} (hx : SBnd w (2 ^ 12) B x) (hB : B < 2 ^ w) :
    SBnd w (2 ^ 12) B (colQ w q x) ∧ ∀ k : Fin 4096,
      sval w (colQ w q x) k.val =
        (if (qCentralBit q ^^ bpar (k.val &&& qModul q) 12) = true then -1 else 1) *
          sval w x (k.val ^^^ qTransl q) := by
  have htl : qTransl q < 4096 := (generatedAxisGlobalSpinLabel (spinTranslation q)).isLt
  obtain ⟨s1, v1⟩ := strs_spec (bitsOf (qTransl q)) hx (bitsOf_lt _)
  obtain ⟨s2, v2⟩ := sflip_spec s1 _ _ (linMask_isFieldMask w 12 (qModul q) (qCentralBit q) 12
    le_rfl) hB
  refine ⟨s2, fun k => ?_⟩
  unfold colQ
  rw [v2 k.val k.isLt, v1 k.val k.isLt, xorBits_bitsOf _ htl]
  split_ifs <;> ring

/-- The packed extraspecial column action fixes zero. -/
theorem colQ_zero (w : ℕ) (q : Q) : colQ w q szero = szero := by
  rw [colQ, strs_zero]
  simp [sflip, sadd, ssel, sneg, szero]

/-- Bounds of the packed extraspecial tensor action. -/
theorem tensorQ_bnd {w B : ℕ} (q : Q) {X : List SVec} (hX : TBnd w B X) (hB : B < 2 ^ w) :
    TBnd w B (tensorQ w q X) := by
  intro i hi
  rw [tensorQ, tcol_map _ (colQ_zero w q) X i]
  exact (colQ_spec q (hX i hi) hB).1

/-- The packed extraspecial tensor action computes the rational extraspecial operator. -/
theorem tensorQ_rat {w B : ℕ} (q : Q) {X : List SVec} (hX : TBnd w B X) (hB : B < 2 ^ w)
    (D : ℚ) :
    tensorRat w (tensorQ w q X) D = generatedAxisGlobalRationalTensorQ q (tensorRat w X D) := by
  funext k i
  have hcol : tcol (tensorQ w q X) i.val = colQ w q (tcol X i.val) := by
    rw [tensorQ, tcol_map _ (colQ_zero w q) X i.val]
  simp only [tensorRat, generatedAxisGlobalRationalTensorQ]
  rw [hcol, (colQ_spec q (hX i.val i.isLt) hB).2 k, spinPhase_coeff]
  have hl : generatedAxisGlobalSpinLabel (golayLabelCoefficients k + spinTranslation q) =
      ⟨k.val ^^^ qTransl q, Nat.xor_lt_two_pow (n := 12) k.isLt
        (generatedAxisGlobalSpinLabel (spinTranslation q)).isLt⟩ :=
    Fin.ext (spinLabel_add k (spinTranslation q))
  rw [hl]
  by_cases hp : (qCentralBit q ^^ bpar (k.val &&& qModul q) 12) = true
  · simp only [hp, ↓reduceIte, generatedAxisGlobalIntSign]
    norm_num
    ring
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, generatedAxisGlobalIntSign]
    norm_num

/-! ## Sums of signed packed vectors -/

/-- The field-wise sum of a list of signed packed vectors. -/
def ssum : List SVec → SVec
  | [] => szero
  | x :: xs => sadd x (ssum xs)

/-- Bounds and values of a list sum: bounds add up along the list. -/
theorem ssum_spec {w n B : ℕ} : ∀ (xs : List SVec), (∀ x ∈ xs, SBnd w n B x) →
    xs.length * B < 2 ^ w →
    SBnd w n (xs.length * B) (ssum xs) ∧
      ∀ i < n, sval w (ssum xs) i = (xs.map (fun x => sval w x i)).sum
  | [], _, _ => ⟨by simpa [ssum] using SBnd_zero w n 0, fun i _ => by simp [ssum, sval_zero]⟩
  | x :: xs, hxs, hlen => by
    have hx : SBnd w n B x := hxs x (by simp)
    have hlen' : xs.length * B < 2 ^ w := by
      simp only [List.length_cons] at hlen
      nlinarith
    obtain ⟨h1, h2⟩ := ssum_spec xs (fun y hy => hxs y (by simp [hy])) hlen'
    have hsum : B + xs.length * B < 2 ^ w := by
      simp only [List.length_cons] at hlen; nlinarith
    obtain ⟨h3, h4⟩ := sadd_spec hx h1 hsum
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [List.length_cons, ssum]
      exact h3.mono (by nlinarith)
    · simp only [ssum, List.map_cons, List.sum_cons]
      rw [h4 i hi, h2 i hi]

/-- A conditionally negated vector. -/
def scond (neg : Bool) (x : SVec) : SVec := if neg then sneg x else x

/-- Bounds and values of a conditional negation. -/
theorem scond_spec {w n B : ℕ} (neg : Bool) {x : SVec} (hx : SBnd w n B x) :
    SBnd w n B (scond neg x) ∧
      ∀ i, sval w (scond neg x) i = (if neg then -1 else 1) * sval w x i := by
  cases neg
  · exact ⟨hx, fun i => by simp [scond]⟩
  · obtain ⟨h1, h2⟩ := sneg_spec hx
    exact ⟨h1, fun i => by simp [scond, h2]⟩

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
