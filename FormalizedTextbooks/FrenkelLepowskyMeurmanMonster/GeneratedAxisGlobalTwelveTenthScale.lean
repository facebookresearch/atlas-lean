/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairVec
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWTight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorBound
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiOp

/-! # Exact rescaling of identification vectors

Dense identification vectors carry large common factors: the short numerators of the Tenth axis
are multiples of a large power of two, and so are the packed tensor numerators of word images
over the product of the letter denominators.  This module divides them out exactly.

* `ShortData.scale c` multiplies all short numerators by `c`; `IdentVec.real_of_scale` replaces
  a short block by a block with numerators divided by `c` and the scale multiplied by `c`.
* `shiftT s X` divides all fields of a packed tensor by `2^s`; `tensorRat_shiftT` turns one kernel
  check (the shifted tensor scaled back is the original tensor, and its fields are below `2^k`)
  into the equality of rational tensors with the denominator divided by `2^s`, together with the
  tight bound `2^k - 1`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-! ## Short blocks -/

/-- Multiply all numerators of a term list by `c`. -/
def termsScale (c : ℤ) (L : List (ℕ × ℤ)) : List (ℕ × ℤ) := L.map (fun p => (p.1, c * p.2))

/-- Multiply all numerators of a sparse short block by `c`. -/
def ShortData.scale (c : ℤ) (S : ShortData) : ShortData :=
  ⟨termsScale c S.pairs, S.oct.map (fun b => (b.1, termsScale c b.2)), termsScale c S.odd⟩

theorem octsFlat_scale (c : ℤ) : ∀ B : List (ℕ × List (ℕ × ℤ)),
    octsFlat (B.map (fun b => (b.1, termsScale c b.2))) = termsScale c (octsFlat B)
  | [] => rfl
  | b :: B => by
    rw [List.map_cons, octsFlat, octsFlat, octsFlat_scale c B, termsScale, termsScale,
      termsScale, List.map_append]
    congr 1
    simp only [octFlat, List.map_map]
    rfl

/-- The flat terms of a scaled block are the scaled flat terms. -/
theorem ShortData.flat_scale (c : ℤ) (S : ShortData) :
    (S.scale c).flat = termsScale c S.flat := by
  rw [ShortData.flat, ShortData.flat, ShortData.scale]
  simp only
  rw [octsFlat_scale]
  simp only [termsScale, List.map_append]

/-- Scaling does not change the range conditions. -/
theorem ShortData.ok_scale (c : ℤ) (S : ShortData) : (S.scale c).ok = S.ok := by
  simp only [ShortData.ok, ShortData.scale, termsScale, List.all_map, Function.comp_def]

/-- The rational short coordinates of a scaled list. -/
theorem shortFunQ_scale (c : ℤ) (L : List (ℕ × ℤ)) (r : GriessShortIndex) :
    shortFunQ (termsScale c L) r = c * shortFunQ L r := by
  unfold shortFunQ termsScale
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  split_ifs <;> push_cast <;> ring

/-- A representation with the short numerators divided by `c` and the scale multiplied by `c`. -/
theorem IdentVec.real_of_scale (V V' : IdentVec) (c : ℤ) (hm : V'.mat = V.mat)
    (hs : V.sh = V'.sh.scale c) (hd : V'.sden = V.sden * c) (ht : V'.ten = V.ten) :
    V'.real = V.real := by
  unfold IdentVec.real IdentVec.packet
  rw [hm, ht, hd, hs]
  have h : (fun r => V.sden * shortFunQ (V'.sh.scale c).flat r) =
      (fun r => V.sden * (c : ℚ) * shortFunQ V'.sh.flat r) := by
    funext r
    rw [ShortData.flat_scale, shortFunQ_scale]
    ring
  rw [h]

/-! ## Packed tensors -/

theorem tcol_map_sscale (c : ℕ) (X : List SVec) (i : ℕ) :
    tcol (X.map (sscale c)) i = sscale c (tcol X i) := by
  unfold tcol
  induction X generalizing i with
  | nil => simp [sscale, szero]
  | cons x X ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

/-- Scaled packed numerators over a scaled denominator. -/
theorem tensorRat_sscale (w s B : ℕ) (X : List SVec) (D : ℚ) (hX : TBnd w B X)
    (hB : 2 ^ s * B < 2 ^ w) :
    tensorRat w (X.map (sscale (2 ^ s))) D = tensorRat w X (D / 2 ^ s) := by
  funext k i
  simp only [tensorRat]
  rw [tcol_map_sscale, (sscale_spec (hX i.val i.isLt) (2 ^ s) hB).2 k.val
    (lt_of_lt_of_eq k.isLt (by norm_num))]
  push_cast
  rw [div_div_eq_mul_div]
  ring

/-- Divide all fields of a packed tensor by `2^s` (exact when the low bits vanish). -/
def shiftT (s : ℕ) (X : List SVec) : List SVec := X.map (fun c => (c.1 >>> s, c.2 >>> s))

theorem tcol_shiftT (s : ℕ) (X : List SVec) (i : ℕ) :
    tcol (shiftT s X) i = ((tcol X i).1 >>> s, (tcol X i).2 >>> s) := by
  unfold shiftT tcol
  induction X generalizing i with
  | nil => simp [szero]
  | cons x X ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

/-- The size conditions of a shifted tensor, with the trivial field bound. -/
theorem tbnd_shiftT_coarse {w C : ℕ} (s : ℕ) {X : List SVec} (hX : TBnd w C X) :
    TBnd w (2 ^ w) (shiftT s X) := by
  intro i hi
  have h := hX i hi
  rw [tcol_shiftT]
  exact ⟨lt_of_le_of_lt (Nat.shiftRight_le _ _) h.1, lt_of_le_of_lt (Nat.shiftRight_le _ _) h.2.1,
    fun t _ => ⟨(fld_lt _ _ _).le, (fld_lt _ _ _).le⟩⟩

/-- A checked exact division of a packed tensor by `2^s`, with a tight bound of the quotient. -/
theorem tensorRat_shiftT (w s k C : ℕ) (X : List SVec) (D : ℚ) (hX : TBnd w C X) (hk : k ≤ w)
    (hks : 2 ^ s * (2 ^ k - 1) < 2 ^ w) (hlt : colsLtB w k (shiftT s X) = true)
    (heq : (shiftT s X).map (sscale (2 ^ s)) = X) :
    TBnd w (2 ^ k - 1) (shiftT s X) ∧ tensorRat w X D = tensorRat w (shiftT s X) (D / 2 ^ s) := by
  have hT := tbnd_tight w k _ (shiftT s X) (tbnd_shiftT_coarse s hX) hk hlt
  refine ⟨hT, ?_⟩
  conv_lhs => rw [← heq]
  exact tensorRat_sscale w s _ _ D hT hks

/-! ## Canonical signed packed vectors

The packed letter actions accumulate positive and negative contributions in separate parts, so
both parts of a field can be much larger than its value.  `canonP` replaces a signed vector by the
signed vector with the same field values and one vanishing part in every field (a constant
offset, one borrow-free subtraction, the sign bits as a field mask, two masked borrow-free
subtractions); then common factors of the values can be divided out. -/

/-- Subtraction without borrows between fields. -/
theorem fld_sub (w : ℕ) : ∀ (n A Q : ℕ), A < 2 ^ (w * n) → Q < 2 ^ (w * n) →
    (∀ i < n, fld w Q i ≤ fld w A i) →
    Q ≤ A ∧ ∀ i < n, fld w (A - Q) i = fld w A i - fld w Q i := by
  intro n
  induction n with
  | zero =>
    intro A Q hA hQ _
    have hA0 : A = 0 := by simpa using hA
    have hQ0 : Q = 0 := by simpa using hQ
    subst hA0 hQ0
    simp
  | succ n ih =>
    intro A Q hA hQ h
    have hw : 0 < 2 ^ w := by positivity
    have hA' : A / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul hw, ← pow_add]
      calc A < 2 ^ (w * (n + 1)) := hA
        _ = 2 ^ (w * n + w) := by ring_nf
    have hQ' : Q / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul hw, ← pow_add]
      calc Q < 2 ^ (w * (n + 1)) := hQ
        _ = 2 ^ (w * n + w) := by ring_nf
    have h0 := h 0 (Nat.succ_pos n)
    rw [fld_zero_right, fld_zero_right] at h0
    have hrest : ∀ i < n, fld w (Q / 2 ^ w) i ≤ fld w (A / 2 ^ w) i := by
      intro i hi
      have := h (i + 1) (by omega)
      rwa [fld_succ, fld_succ] at this
    obtain ⟨hle, hfld⟩ := ih (A / 2 ^ w) (Q / 2 ^ w) hA' hQ' hrest
    have hAs := Nat.mod_add_div A (2 ^ w)
    have hQs := Nat.mod_add_div Q (2 ^ w)
    have hma : A % 2 ^ w < 2 ^ w := Nat.mod_lt _ hw
    have e1 : 2 ^ w * (A / 2 ^ w - Q / 2 ^ w) + 2 ^ w * (Q / 2 ^ w) = 2 ^ w * (A / 2 ^ w) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hle]
    have hsplit : A - Q = (A % 2 ^ w - Q % 2 ^ w) + 2 ^ w * (A / 2 ^ w - Q / 2 ^ w) := by
      omega
    have hQA : Q ≤ A := by omega
    have hlow : A % 2 ^ w - Q % 2 ^ w < 2 ^ w := by omega
    have hmod : (A - Q) % 2 ^ w = A % 2 ^ w - Q % 2 ^ w := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
    have hdiv : (A - Q) / 2 ^ w = A / 2 ^ w - Q / 2 ^ w := by
      rw [hsplit, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hlow, zero_add]
    refine ⟨hQA, ?_⟩
    intro i hi
    cases i with
    | zero => rw [fld_zero_right, fld_zero_right, fld_zero_right, hmod]
    | succ i =>
      rw [fld_succ, fld_succ, fld_succ, hdiv]
      exact hfld i (by omega)

/-- The top bit of every field, moved to the bottom bit of the field. -/
theorem fld_topBit (w t i : ℕ) (hw : 1 ≤ w) (hi : i < 2 ^ 12) :
    fld w ((t >>> (w - 1)) &&& repC w 1) i = fld w t i / 2 ^ (w - 1) := by
  have h1 : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  rw [fld_land, fld_repC w 1 h1 i (by simpa using hi), Nat.and_one_is_mod]
  unfold fld
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  have hw2 : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [hw2, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add,
    Nat.mod_mod_of_dvd _ (Dvd.intro_left _ rfl), Nat.add_comm (w - 1)]

/-- The canonical form of a signed packed vector on `4096` fields. -/
def canonP (w : ℕ) (x : SVec) : SVec :=
  let R := repC w (2 ^ (w - 1))
  let t := (x.1 + R) - x.2
  let F := (2 ^ w - 1) * ((t >>> (w - 1)) &&& repC w 1)
  let G := allMask w (2 ^ 12) ^^^ F
  ((t &&& F) - (R &&& F), (R &&& G) - (t &&& G))

/-- The canonical form keeps the bounds and the values of all fields. -/
theorem canonP_spec {w B : ℕ} (hw : 1 ≤ w) {x : SVec} (hx : SBnd w (2 ^ 12) B x)
    (hB : B < 2 ^ (w - 1)) :
    SBnd w (2 ^ 12) B (canonP w x) ∧ ∀ i < 2 ^ 12, sval w (canonP w x) i = sval w x i := by
  obtain ⟨hx1, hx2, hxf⟩ := hx
  have hw2 : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hhalf : 2 ^ (w - 1) < 2 ^ w := by omega
  have hone : (1 : ℕ) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  set R := repC w (2 ^ (w - 1)) with hRdef
  have hRlt : R < 2 ^ (w * 2 ^ 12) := repC_lt w _ hhalf
  have hRf : ∀ i < 2 ^ 12, fld w R i = 2 ^ (w - 1) := fun i hi =>
    fld_repC w _ hhalf i (by simpa using hi)
  -- the offset sum
  obtain ⟨hs1, hs2⟩ := fld_add w (2 ^ 12) x.1 R hx1 hRlt (fun i hi => by
    rw [hRf i hi]; have := (hxf i hi).1; omega)
  -- the offset difference
  obtain ⟨hd1, hd2⟩ := fld_sub w (2 ^ 12) (x.1 + R) x.2 hs1 hx2 (fun i hi => by
    rw [hs2 i hi, hRf i hi]; have := (hxf i hi).2; omega)
  set t := x.1 + R - x.2 with htdef
  have htlt : t < 2 ^ (w * 2 ^ 12) := lt_of_le_of_lt (Nat.sub_le _ _) hs1
  have htf : ∀ i < 2 ^ 12, fld w t i = fld w x.1 i + 2 ^ (w - 1) - fld w x.2 i := by
    intro i hi; rw [hd2 i hi, hs2 i hi, hRf i hi]
  -- the sign mask
  set S := (t >>> (w - 1)) &&& repC w 1 with hSdef
  have hSlt : S < 2 ^ (w * 2 ^ 12) := lt_of_le_of_lt Nat.and_le_right (repC_lt w 1 hone)
  have hSf : ∀ i < 2 ^ 12, fld w S i = if fld w x.2 i ≤ fld w x.1 i then 1 else 0 := by
    intro i hi
    rw [hSdef, fld_topBit w t i hw hi, htf i hi]
    have ha := (hxf i hi).1
    have hb := (hxf i hi).2
    split_ifs with hc
    · apply Nat.div_eq_of_lt_le <;> omega
    · apply Nat.div_eq_of_lt
      omega
  -- the field masks
  obtain ⟨_, hF2⟩ := fld_mul w (2 ^ w - 1) (2 ^ 12) S hSlt (fun i hi => by
    rw [hSf i hi]; split_ifs <;> omega)
  set F := (2 ^ w - 1) * S with hFdef
  have hFf : ∀ i < 2 ^ 12,
      fld w F i = if fld w x.2 i ≤ fld w x.1 i then 2 ^ w - 1 else 0 := by
    intro i hi
    rw [hF2 i hi, hSf i hi]
    split_ifs <;> simp
  set G := allMask w (2 ^ 12) ^^^ F with hGdef
  have hGf : ∀ i < 2 ^ 12,
      fld w G i = if fld w x.2 i ≤ fld w x.1 i then 0 else 2 ^ w - 1 := by
    intro i hi
    rw [hGdef, fld_xor, fld_allMask, hFf i hi]
    simp only [hi, ↓reduceIte]
    split_ifs <;> simp
  have hand : ∀ v : ℕ, v < 2 ^ w → v &&& (2 ^ w - 1) = v := fun v hv => by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hv]
  have htF : ∀ i < 2 ^ 12, fld w (t &&& F) i =
      if fld w x.2 i ≤ fld w x.1 i then fld w t i else 0 := by
    intro i hi
    rw [fld_land, hFf i hi]
    split_ifs
    · exact hand _ (fld_lt _ _ _)
    · simp
  have hRF : ∀ i < 2 ^ 12, fld w (R &&& F) i =
      if fld w x.2 i ≤ fld w x.1 i then 2 ^ (w - 1) else 0 := by
    intro i hi
    rw [fld_land, hFf i hi, hRf i hi]
    split_ifs
    · exact hand _ hhalf
    · simp
  have htG : ∀ i < 2 ^ 12, fld w (t &&& G) i =
      if fld w x.2 i ≤ fld w x.1 i then 0 else fld w t i := by
    intro i hi
    rw [fld_land, hGf i hi]
    split_ifs
    · simp
    · exact hand _ (fld_lt _ _ _)
  have hRG : ∀ i < 2 ^ 12, fld w (R &&& G) i =
      if fld w x.2 i ≤ fld w x.1 i then 0 else 2 ^ (w - 1) := by
    intro i hi
    rw [fld_land, hGf i hi, hRf i hi]
    split_ifs
    · simp
    · exact hand _ hhalf
  -- the two masked differences
  have htFlt : t &&& F < 2 ^ (w * 2 ^ 12) := lt_of_le_of_lt Nat.and_le_left htlt
  have hRFlt : R &&& F < 2 ^ (w * 2 ^ 12) := lt_of_le_of_lt Nat.and_le_left hRlt
  have htGlt : t &&& G < 2 ^ (w * 2 ^ 12) := lt_of_le_of_lt Nat.and_le_left htlt
  have hRGlt : R &&& G < 2 ^ (w * 2 ^ 12) := lt_of_le_of_lt Nat.and_le_left hRlt
  obtain ⟨_, hp2⟩ := fld_sub w (2 ^ 12) (t &&& F) (R &&& F) htFlt hRFlt (fun i hi => by
    rw [htF i hi, hRF i hi, htf i hi]
    have ha := (hxf i hi).1
    have hb := (hxf i hi).2
    split_ifs <;> omega)
  obtain ⟨_, hn2⟩ := fld_sub w (2 ^ 12) (R &&& G) (t &&& G) hRGlt htGlt (fun i hi => by
    rw [htG i hi, hRG i hi, htf i hi]
    have ha := (hxf i hi).1
    have hb := (hxf i hi).2
    split_ifs <;> omega)
  have hc : canonP w x = ((t &&& F) - (R &&& F), (R &&& G) - (t &&& G)) := rfl
  rw [hc]
  refine ⟨⟨lt_of_le_of_lt (Nat.sub_le _ _) htFlt, lt_of_le_of_lt (Nat.sub_le _ _) hRGlt,
    fun i hi => ?_⟩, fun i hi => ?_⟩
  · simp only
    rw [hp2 i hi, hn2 i hi, htF i hi, hRF i hi, htG i hi, hRG i hi, htf i hi]
    have ha := (hxf i hi).1
    have hb := (hxf i hi).2
    split_ifs <;> omega
  · simp only [sval]
    rw [hp2 i hi, hn2 i hi, htF i hi, hRF i hi, htG i hi, hRG i hi, htf i hi]
    have ha := (hxf i hi).1
    have hb := (hxf i hi).2
    split_ifs <;> omega

/-- The canonical form of a packed tensor. -/
def canonT (w : ℕ) (X : List SVec) : List SVec :=
  (List.range 24).map (fun j => canonP w (tcol X j))

/-- The canonical form of a packed tensor keeps the bounds and the rational tensor. -/
theorem canonT_spec {w B : ℕ} (hw : 1 ≤ w) {X : List SVec} (hX : TBnd w B X)
    (hB : B < 2 ^ (w - 1)) (D : ℚ) :
    TBnd w B (canonT w X) ∧ tensorRat w (canonT w X) D = tensorRat w X D := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [canonT, tcol_range_map _ 24 i hi]
    exact (canonP_spec hw (hX i hi) hB).1
  · funext k i
    simp only [tensorRat]
    rw [canonT, tcol_range_map _ 24 i.val i.isLt,
      (canonP_spec hw (hX i.val i.isLt) hB).2 k.val (lt_of_lt_of_eq k.isLt (by norm_num))]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
