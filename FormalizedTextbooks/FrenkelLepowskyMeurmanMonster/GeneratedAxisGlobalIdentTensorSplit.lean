/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOddDense
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound

/-! # Split packed tensors: pairings of tensors with large fields at field width `64`

Words with several Xi letters give packed tensors whose fields (positive and negative parts kept
separately) exceed the product bounds of the multiplicative dot products at field width `64`.
Every field splits as `2^s * hi + lo` (`hi`/`lo` by masks and one shift, no field-wise work):
`sval_split`, the tensor dot product and the integer odd parts split accordingly
(`tdot_split_left`/`_right`, `oddWZ_split`, `oddLZ_split`), and each piece has small fields.
`pairTriGZT` is `pairTriGMZ` with the exact tensor dot product `tdot` (no product bound needed),
with `pairTriGZT_eq`, `pairTriGZT_parts`, `ident_forward_GZT` / `ident_inverse_GZT`; the odd parts
of split tensors come from the dense odd check without a representation (`oddWZ_of_chk2`,
`oddLZ_of_chk2`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators
set_option autoImplicit false

namespace TSplit

/-! ## Splitting the fields -/

/-- The low `s` bits of each of `4096` fields. -/
def loMask (w s : ℕ) : ℕ := repC w (2 ^ s - 1)

/-- The low `w - s` bits of each of `4096` fields. -/
def hiMask (w s : ℕ) : ℕ := repC w (2 ^ (w - s) - 1)

/-- The low `s` bits of every field. -/
def loP (w s : ℕ) (x : SVec) : SVec := (x.1 &&& loMask w s, x.2 &&& loMask w s)

/-- Every field divided by `2^s`. -/
def hiP (w s : ℕ) (x : SVec) : SVec := ((x.1 >>> s) &&& hiMask w s, (x.2 >>> s) &&& hiMask w s)

/-- The low parts of all columns. -/
def tlo (w s : ℕ) (X : List SVec) : List SVec := X.map (loP w s)

/-- The high parts of all columns. -/
def thi (w s : ℕ) (X : List SVec) : List SVec := X.map (hiP w s)

theorem two_pow_sub_one_lt {a b : ℕ} (h : a ≤ b) : 2 ^ a - 1 < 2 ^ b :=
  lt_of_lt_of_le (Nat.sub_lt (by positivity) one_pos) (Nat.pow_le_pow_right (by norm_num) h)

theorem fld_lo (w s P i : ℕ) (hs : s ≤ w) (hi : i < 4096) :
    fld w (P &&& loMask w s) i = fld w P i % 2 ^ s := by
  rw [fld_land, loMask, fld_repC w _ (two_pow_sub_one_lt hs) i hi, Nat.and_two_pow_sub_one_eq_mod]

theorem fld_hi (w s P i : ℕ) (hs : s ≤ w) (hi : i < 4096) :
    fld w ((P >>> s) &&& hiMask w s) i = fld w P i / 2 ^ s := by
  rw [fld_land, hiMask, fld_repC w _ (two_pow_sub_one_lt (Nat.sub_le w s)) i hi,
    Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_mod_two_pow, testBit_fld, Nat.testBit_shiftRight, Nat.testBit_div_two_pow,
    testBit_fld]
  by_cases hb : b + s < w
  · have h1 : b < w - s := by omega
    have h2 : b < w := by omega
    simp only [h1, h2, hb, decide_true, Bool.true_and]
    rw [show s + (w * i + b) = w * i + (b + s) by ring]
  · have h1 : ¬ b < w - s := by omega
    simp [h1, hb]

/-- Every field is `2^s` times its high part plus its low part. -/
theorem sval_split (w s : ℕ) (hs : s ≤ w) (x : SVec) (i : ℕ) (hi : i < 4096) :
    sval w x i = 2 ^ s * sval w (hiP w s x) i + sval w (loP w s x) i := by
  simp only [sval, hiP, loP, fld_hi w s _ i hs hi, fld_lo w s _ i hs hi]
  have e1 : (fld w x.1 i : ℤ) = 2 ^ s * ((fld w x.1 i / 2 ^ s : ℕ) : ℤ) +
      ((fld w x.1 i % 2 ^ s : ℕ) : ℤ) := by exact_mod_cast (Nat.div_add_mod _ _).symm
  have e2 : (fld w x.2 i : ℤ) = 2 ^ s * ((fld w x.2 i / 2 ^ s : ℕ) : ℤ) +
      ((fld w x.2 i % 2 ^ s : ℕ) : ℤ) := by exact_mod_cast (Nat.div_add_mod _ _).symm
  rw [e1, e2]
  ring

theorem lo_szero (w s : ℕ) : loP w s szero = szero := by simp [loP, szero]

theorem hi_szero (w s : ℕ) : hiP w s szero = szero := by simp [hiP, szero]

theorem tcol_tlo (w s : ℕ) (X : List SVec) (i : ℕ) : tcol (tlo w s X) i = loP w s (tcol X i) := by
  unfold tcol tlo
  conv_lhs => rw [← lo_szero w s]
  rw [List.getD_map]

theorem tcol_thi (w s : ℕ) (X : List SVec) (i : ℕ) : tcol (thi w s X) i = hiP w s (tcol X i) := by
  unfold tcol thi
  conv_lhs => rw [← hi_szero w s]
  rw [List.getD_map]

theorem lo_sbnd (w s : ℕ) (hs : s ≤ w) (x : SVec) : SBnd w (2 ^ 12) (2 ^ s - 1) (loP w s x) := by
  have hm : loMask w s < 2 ^ (w * 2 ^ 12) := repC_lt w _ (two_pow_sub_one_lt hs)
  refine ⟨lt_of_le_of_lt Nat.and_le_right hm, lt_of_le_of_lt Nat.and_le_right hm, fun i hi => ?_⟩
  have hi' : i < 4096 := by norm_num at hi; exact hi
  simp only [loP]
  rw [fld_lo w s _ i hs hi', fld_lo w s _ i hs hi']
  exact ⟨Nat.le_sub_one_of_lt (Nat.mod_lt _ (by positivity)),
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by positivity))⟩

theorem hi_sbnd {w s B : ℕ} (hs : s ≤ w) {x : SVec} (hx : SBnd w (2 ^ 12) B x) :
    SBnd w (2 ^ 12) (B / 2 ^ s) (hiP w s x) := by
  have hm : hiMask w s < 2 ^ (w * 2 ^ 12) := repC_lt w _ (two_pow_sub_one_lt (Nat.sub_le w s))
  refine ⟨lt_of_le_of_lt Nat.and_le_right hm, lt_of_le_of_lt Nat.and_le_right hm, fun i hi => ?_⟩
  have hi' : i < 4096 := by norm_num at hi; exact hi
  simp only [hiP]
  rw [fld_hi w s _ i hs hi', fld_hi w s _ i hs hi']
  exact ⟨Nat.div_le_div_right (hx.2.2 i hi).1, Nat.div_le_div_right (hx.2.2 i hi).2⟩

theorem tlo_bnd (w s : ℕ) (hs : s ≤ w) (X : List SVec) : TBnd w (2 ^ s - 1) (tlo w s X) := by
  intro i _
  rw [tcol_tlo]
  exact lo_sbnd w s hs _

theorem thi_bnd {w s B : ℕ} (hs : s ≤ w) {X : List SVec} (hX : TBnd w B X) :
    TBnd w (B / 2 ^ s) (thi w s X) := by
  intro i hi
  rw [tcol_thi]
  exact hi_sbnd hs (hX i hi)

/-! ## Splitting the tensor dot product -/

theorem list_sum_lin {α : Type*} (l : List α) (f g h : α → ℤ) (c : ℤ)
    (H : ∀ a ∈ l, f a = c * g a + h a) :
    (l.map f).sum = c * (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [H a (by simp), ih (fun b hb => H b (by simp [hb]))]
    ring

theorem sdot_split_right (w s : ℕ) (hs : s ≤ w) (x y : SVec) :
    sdot w x y 4096 = 2 ^ s * sdot w x (hiP w s y) 4096 + sdot w x (loP w s y) 4096 := by
  rw [sdot_eq, sdot_eq, sdot_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sval_split w s hs y k (Finset.mem_range.mp hk)]
  ring

theorem sdot_split_left (w s : ℕ) (hs : s ≤ w) (x y : SVec) :
    sdot w x y 4096 = 2 ^ s * sdot w (hiP w s x) y 4096 + sdot w (loP w s x) y 4096 := by
  rw [sdot_eq, sdot_eq, sdot_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sval_split w s hs x k (Finset.mem_range.mp hk)]
  ring

theorem tdot_split_right (w s : ℕ) (hs : s ≤ w) (X Y : List SVec) :
    tdot w X Y = 2 ^ s * tdot w X (thi w s Y) + tdot w X (tlo w s Y) := by
  unfold tdot
  apply list_sum_lin
  intro i _
  rw [tcol_thi, tcol_tlo]
  exact sdot_split_right w s hs _ _

theorem tdot_split_left (w s : ℕ) (hs : s ≤ w) (X Y : List SVec) :
    tdot w X Y = 2 ^ s * tdot w (thi w s X) Y + tdot w (tlo w s X) Y := by
  unfold tdot
  apply list_sum_lin
  intro i _
  rw [tcol_thi, tcol_tlo]
  exact sdot_split_left w s hs _ _

/-- The checked tensor dot product of two split tensors (both split at `s`). -/
def tdotSplitChk (w s B C : ℕ) (X Y : List SVec) (c : ℤ) : Bool :=
  decide (s ≤ w) &&
    decide (2 * (2 * 4096 * ((B / 2 ^ s) * (C / 2 ^ s))) < 2 ^ w) &&
    decide (2 * (2 * 4096 * ((2 ^ s - 1) * (C / 2 ^ s))) < 2 ^ w) &&
    decide (2 * (2 * 4096 * ((B / 2 ^ s) * (2 ^ s - 1))) < 2 ^ w) &&
    decide (2 * (2 * 4096 * ((2 ^ s - 1) * (2 ^ s - 1))) < 2 ^ w) &&
    decide (2 ^ s * (2 ^ s * tdotM w (thi w s X) (thi w s Y) + tdotM w (tlo w s X) (thi w s Y)) +
      (2 ^ s * tdotM w (thi w s X) (tlo w s Y) + tdotM w (tlo w s X) (tlo w s Y)) = c)

theorem tdot_of_splitChk {w s B C : ℕ} {X Y : List SVec} {c : ℤ} (hX : TBnd w B X)
    (hY : TBnd w C Y) (h : tdotSplitChk w s B C X Y c = true) : tdot w X Y = c := by
  simp only [tdotSplitChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hs, b1⟩, b2⟩, b3⟩, b4⟩, hv⟩ := h
  rw [tdot_split_right w s hs, tdot_split_left w s hs X (thi w s Y),
    tdot_split_left w s hs X (tlo w s Y), ← hv,
    tdotM_eq (thi_bnd hs hX) (thi_bnd hs hY) b1, tdotM_eq (tlo_bnd w s hs X) (thi_bnd hs hY) b2,
    tdotM_eq (thi_bnd hs hX) (tlo_bnd w s hs Y) b3, tdotM_eq (tlo_bnd w s hs X) (tlo_bnd w s hs Y) b4]

/-! ## Splitting the integer odd parts -/

theorem oddWTerm_split (w s : ℕ) (hs : s ≤ w) (fwd : Bool) (X : List SVec) (lab : ℕ) :
    oddWTerm w fwd X lab = 2 ^ s * oddWTerm w fwd (thi w s X) lab + oddWTerm w fwd (tlo w s X) lab := by
  have hd : oddD lab < 2048 := Nat.mod_lt _ (by norm_num)
  unfold oddWTerm
  simp only [svalS_eq_sval, tcol_thi, tcol_tlo]
  rw [sval_split w s hs (tcol X (oddJ lab)) (oddD lab) (by omega),
    sval_split w s hs (tcol X (oddJ lab)) (oddD lab + 2048) (by omega)]
  cases fwd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

theorem oddLTerm_eq (w : ℕ) (fwd : Bool) (Y : List SVec) (lab : ℕ) :
    oddLTerm w fwd Y lab = oddWTerm w (!fwd) Y lab := by
  cases fwd <;> simp only [oddLTerm, oddWTerm, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]

theorem oddWZ_split (w s : ℕ) (hs : s ≤ w) (fwd : Bool) (X : List SVec) (W : IdentVec) :
    oddWZ w fwd X W = 2 ^ s * oddWZ w fwd (thi w s X) W + oddWZ w fwd (tlo w s X) W := by
  unfold oddWZ
  apply list_sum_lin
  intro q _
  rw [oddWTerm_split w s hs fwd X q.1]
  ring

theorem oddLZ_split (w s : ℕ) (hs : s ≤ w) (fwd : Bool) (Y : List SVec) (L : IdentVec) :
    oddLZ w fwd Y L = 2 ^ s * oddLZ w fwd (thi w s Y) L + oddLZ w fwd (tlo w s Y) L := by
  unfold oddLZ
  apply list_sum_lin
  intro q _
  rw [oddLTerm_eq, oddLTerm_eq, oddLTerm_eq, oddWTerm_split w s hs (!fwd) Y q.1]
  ring

/-- An odd term read from a tensor is a field of its signed half sum or difference. -/
theorem oddWTerm_half {w B : ℕ} (fwd : Bool) {X : List SVec} (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w) (lab : ℕ) :
    oddWTerm w fwd X lab = sval w (oddHalf w fwd (!fwd) (oddJ lab) (tcol X (oddJ lab))) (oddD lab) := by
  have hd : oddD lab < 2048 := Nat.mod_lt _ (by norm_num)
  obtain ⟨-, v⟩ := oddHalf_spec fwd (!fwd) (oddJ lab) (hX (oddJ lab) (oddJ_lt lab)) hB
  rw [v (oddD lab) (by omega), Nat.mod_eq_of_lt hd]
  unfold oddWTerm
  simp only [svalS_eq_sval]
  cases fwd
  · have h1 := oddPredF_co (oddJ lab) (oddD lab) hd
    rw [← oddCS_cast] at h1
    have hs : (if oddPredF false (oddJ lab) (oddD lab) then (-1 : ℤ) else 1) =
        oddCS (oddD lab) (oddJ lab) := by
      cases h : oddPredF false (oddJ lab) (oddD lab) <;> simp [h] at h1 ⊢ <;> exact_mod_cast h1
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    rw [hs]
    ring
  · have h1 := oddPredF_wt (oddJ lab) (oddD lab) hd
    rw [← oddWS_cast] at h1
    have hs : (if oddPredF true (oddJ lab) (oddD lab) then (-1 : ℤ) else 1) = oddWS (oddD lab) := by
      cases h : oddPredF true (oddJ lab) (oddD lab) <;> simp [h] at h1 ⊢ <;> exact_mod_cast h1
    simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]
    rw [hs]
    ring

/-- The integer odd part of `W` against any packed tensor, from the dense odd check. -/
theorem oddWZ_of_chk2 {w B : ℕ} (fwd : Bool) (W : IdentVec) (CW : List (ℕ × ℕ × ℕ))
    {X : List SVec} (hW : W.sh = ShortData.ofList (OctadDense.octChunkTerms CW))
    (hX : TBnd w B X) {n : ℤ} (h : OddDense.oddChk w B fwd (!fwd) CW X n = true) :
    oddWZ w fwd X W = n := by
  have hB : 4 * B < 2 ^ w := by
    simp only [OddDense.oddChk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1
  have hs := OddDense.oddChk_sum hX h
  rw [← OddDense.odd_ofList W CW hW] at hs
  unfold oddWZ
  rw [← hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  rw [oddWTerm_half fwd hX hB q.1]

/-- The integer odd part of `L` against any packed tensor, from the dense odd check. -/
theorem oddLZ_of_chk2 {w C : ℕ} (fwd : Bool) (L : IdentVec) (CL : List (ℕ × ℕ × ℕ))
    {Y : List SVec} (hL : L.sh = ShortData.ofList (OctadDense.octChunkTerms CL))
    (hY : TBnd w C Y) {n : ℤ} (h : OddDense.oddChk w C (!fwd) fwd CL Y n = true) :
    oddLZ w fwd Y L = n := by
  have hC : 4 * C < 2 ^ w := by
    simp only [OddDense.oddChk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1
  have hs := OddDense.oddChk_sum hY h
  rw [← OddDense.odd_ofList L CL hL] at hs
  unfold oddLZ
  rw [← hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  rw [oddLTerm_eq, oddWTerm_half (!fwd) hY hC q.1, Bool.not_not]

end TSplit

/-! ## The pairing with the exact tensor dot product -/

/-- `pairTriGMZ` with the exact packed tensor dot product. -/
def pairTriGZT (wo w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W +
    (if octPackOk wo L then
      W.sden * (pairSumQ fwd L W + L.sden * (octSumZ wo fwd L W : ℚ) / 8 +
        (oddWZ w fwd X W : ℚ) / (2 * D))
    else triShortF fwd L W) +
    (L.sden * (oddLZ w fwd Y L : ℚ) / E + (tdot w (trialityTensorT w (!fwd) X) Y : ℚ) /
      (2 * D * E)) / 2

/-- With packed tensors, `pairTriGZT` is the exact pairing (only the triality bound needed). -/
theorem pairTriGZT_eq (wo w : ℕ) (fwd : Bool) (L W : IdentVec) {X Y : List SVec} {D E : ℚ}
    {B : ℕ} (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w) : pairTriGZT wo w fwd L W X Y D E = pairTri fwd L W := by
  have h1 := pairTriGMZ_eq wo w fwd L W X Y D E hLt hWt
  have h2 : pairTriGZT wo w fwd L W X Y D E = pairTriGMZ wo w fwd L W X Y D E +
      ((tdot w (trialityTensorT w (!fwd) X) Y : ℚ) -
        (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ)) / (2 * D * E) / 2 := by
    unfold pairTriGZT pairTriGMZ
    ring
  rw [h2, h1, ← pairTriG_eq]
  unfold pairTriGM pairTriG
  rw [hLt, hWt, tPart_sum fwd hX hB Y D E]
  ring

/-- `pairTriGZT` from the values of its parts. -/
theorem pairTriGZT_parts {wo w : ℕ} {fwd : Bool} {L W : IdentVec} {X Y : List SVec} {D E : ℚ}
    {m p : ℚ} {n a b c : ℤ} (hok : octPackOk wo L = true) (hm : triMatF fwd L W = m)
    (hp : pairSumQ fwd L W = p) (hn : octSumZ wo fwd L W = n) (ha : oddWZ w fwd X W = a)
    (hb : oddLZ w fwd Y L = b) (hc : tdot w (trialityTensorT w (!fwd) X) Y = c) :
    pairTriGZT wo w fwd L W X Y D E =
      m + W.sden * (p + L.sden * (n : ℚ) / 8 + (a : ℚ) / (2 * D)) +
        (L.sden * (b : ℚ) / E + (c : ℚ) / (2 * D * E)) / 2 := by
  unfold pairTriGZT
  rw [hok, hm, hp, hn, ha, hb, hc]
  rfl

/-- Forward identification from `pairTriGZT`. -/
theorem ident_forward_GZT (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGZT wo w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward i j h g L W hL hW hx hy (by rw [← pairTriGZT_eq wo w true L W hLt hWt hX hB, hp])

/-- Inverse identification from `pairTriGZT`. -/
theorem ident_inverse_GZT (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriGZT wo w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse i j h g L W hL hW hx hy (by rw [← pairTriGZT_eq wo w false L W hLt hWt hX hB, hp])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
