/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairWord

/-! # Packed odd cross terms of the triality pairing

The triality pairing contains two cross terms between odd short coordinates and the tensor
block: the odd short coordinates of the triality image (read from the tensor of `L`) paired with
the odd terms of `W`, and the odd terms of `L` paired with the tensor of `W`.  Evaluated term by
term they read single packed fields (slow and memory hungry in the kernel).  Here each is one
packed dot product per column: the odd terms are packed into columns (`packOdd`) and the signed
half sums or differences of the tensor columns are packed (`oddHalf`); `oddXP` sums the 24
multiplicative dot products. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-! ## Packing sparse odd terms -/

/-- A single signed field `c` at index `d`. -/
def sglF (w d : ℕ) (c : ℤ) : SVec :=
  if 0 ≤ c then (c.toNat <<< (w * d), 0) else (0, (-c).toNat <<< (w * d))

/-- Bounds and values of a single signed field. -/
theorem sglF_spec (w d : ℕ) (c : ℤ) (hd : d < 2 ^ 12) (hc : c.natAbs < 2 ^ w) :
    SBnd w (2 ^ 12) c.natAbs (sglF w d c) ∧ ∀ k, sval w (sglF w d c) k = if k = d then c else 0 := by
  by_cases h0 : 0 ≤ c
  · have hn : c.toNat < 2 ^ w := by omega
    simp only [sglF, h0, ↓reduceIte]
    refine ⟨⟨single_lt w _ d _ hn hd, by positivity, fun k _ => ?_⟩, fun k => ?_⟩
    · rw [fld_single w _ _ _ hn, fld_zero_right_zero]
      constructor
      · split_ifs <;> omega
      · exact Nat.zero_le _
    · simp only [sval]
      rw [fld_single w _ _ _ hn, fld_zero_right_zero]
      split_ifs <;> omega
  · have hn : (-c).toNat < 2 ^ w := by omega
    simp only [sglF, h0, ↓reduceIte]
    refine ⟨⟨by positivity, single_lt w _ d _ hn hd, fun k _ => ?_⟩, fun k => ?_⟩
    · rw [fld_single w _ _ _ hn, fld_zero_right_zero]
      constructor
      · exact Nat.zero_le _
      · split_ifs <;> omega
    · simp only [sval]
      rw [fld_single w _ _ _ hn, fld_zero_right_zero]
      split_ifs <;> omega

/-- The sum of the absolute values of the coefficients of a sparse list. -/
def absSumO : List (ℕ × ℤ) → ℕ
  | [] => 0
  | q :: L => q.2.natAbs + absSumO L

/-- Column `j` of the odd terms of a sparse list, packed by odd code label. -/
def packOdd (w j : ℕ) : List (ℕ × ℤ) → SVec
  | [] => szero
  | q :: L => if oddJ q.1 = j then sadd (sglF w (oddD q.1) q.2) (packOdd w j L) else packOdd w j L

/-- Odd code labels are field indices. -/
theorem oddD_lt (lab : ℕ) : oddD lab < 2 ^ 12 := by
  have := Nat.mod_lt ((lab - 49128) / 24) (show 0 < 2048 by norm_num)
  unfold oddD
  omega

/-- Odd coordinates are below `24`. -/
theorem oddJ_lt (lab : ℕ) : oddJ lab < 24 := Nat.mod_lt _ (by norm_num)

set_option maxRecDepth 100000 in
/-- Bounds and values of a packed odd column. -/
theorem packOdd_spec (w j : ℕ) : ∀ L : List (ℕ × ℤ), absSumO L < 2 ^ w →
    SBnd w (2 ^ 12) (absSumO L) (packOdd w j L) ∧ ∀ k, sval w (packOdd w j L) k =
      (L.map (fun q => if oddJ q.1 = j ∧ oddD q.1 = k then q.2 else 0)).sum
  | [], _ => ⟨SBnd_zero w (2 ^ 12) 0, fun k => by
      simp only [packOdd, sval_zero, List.map_nil, List.sum_nil]⟩
  | q :: L, h => by
    have hL : absSumO L < 2 ^ w := by simp only [absSumO] at h; omega
    obtain ⟨b1, v1⟩ := packOdd_spec w j L hL
    by_cases hj : oddJ q.1 = j
    · have hq : q.2.natAbs < 2 ^ w := by simp only [absSumO] at h; omega
      obtain ⟨s1, s2⟩ := sglF_spec w (oddD q.1) q.2 (oddD_lt q.1) hq
      obtain ⟨a1, a2⟩ := sadd_spec s1 b1 (by simp only [absSumO] at h; omega)
      refine ⟨by simpa [packOdd, hj, absSumO] using a1, fun k => ?_⟩
      simp only [packOdd, hj, ↓reduceIte, List.map_cons, List.sum_cons, true_and]
      by_cases hk : k < 2 ^ 12
      · rw [a2 k hk, s2, v1]
        by_cases hd : oddD q.1 = k
        · simp [hd]
        · simp [hd, Ne.symm hd]
      · have z1 := fld_eq_zero_of_lt w _ (2 ^ 12) k a1.1 (by omega)
        have z2 := fld_eq_zero_of_lt w _ (2 ^ 12) k a1.2.1 (by omega)
        have z3 := fld_eq_zero_of_lt w _ (2 ^ 12) k b1.1 (by omega)
        have z4 := fld_eq_zero_of_lt w _ (2 ^ 12) k b1.2.1 (by omega)
        have hd : ¬ oddD q.1 = k := by have := oddD_lt q.1; omega
        rw [ite_eq_right hd, zero_add, ← v1, sval, sval, z1, z2, z3, z4]
    · have hb : absSumO L ≤ absSumO (q :: L) := by simp only [absSumO]; omega
      refine ⟨by simpa [packOdd, hj] using b1.mono hb, fun k => ?_⟩
      simp only [packOdd, hj, ↓reduceIte, List.map_cons, List.sum_cons, false_and, zero_add]
      exact v1 k

/-! ## Signed half sums of tensor columns -/

/-- The sign mask: Golay weight phase (`wt = true`) or code coordinate `j` (`wt = false`). -/
def oddMaskF (w : ℕ) (wt : Bool) (j : ℕ) : ℕ :=
  if wt then spread w qBits (2 ^ 12) else linMask w 12 (gcol j &&& 2047) false 12

/-- The sign predicate of `oddMaskF`. -/
def oddPredF (wt : Bool) (j k : ℕ) : Bool :=
  if wt then qBits.testBit k else bpar (k &&& (gcol j &&& 2047)) 12

/-- The sign mask is a field mask. -/
theorem oddMaskF_isFieldMask (w : ℕ) (wt : Bool) (j : ℕ) :
    IsFieldMask w (2 ^ 12) (oddMaskF w wt j) (fun k => oddPredF wt j k = true) := by
  cases wt
  · show IsFieldMask w (2 ^ 12) (linMask w 12 (gcol j &&& 2047) false 12)
      (fun k => oddPredF false j k = true)
    exact (linMask_isFieldMask w 12 (gcol j &&& 2047) false 12 le_rfl).congr
      (fun k _ => by simp [oddPredF])
  · show IsFieldMask w (2 ^ 12) (spread w qBits (2 ^ 12)) (fun k => oddPredF true j k = true)
    exact (spread_isFieldMask w (2 ^ 12) qBits).congr (fun k _ => by simp [oddPredF])

/-- The signed half sum (`neg = false`) or difference (`neg = true`) of a tensor column. -/
def oddHalf (w : ℕ) (wt neg : Bool) (j : ℕ) (x : SVec) : SVec :=
  sflip (allMask w (2 ^ 12)) (oddMaskF w wt j) (colHalf w neg x)

/-- Bounds and values of a signed half sum or difference. -/
theorem oddHalf_spec {w B : ℕ} (wt neg : Bool) (j : ℕ) {x : SVec} (hx : SBnd w (2 ^ 12) B x)
    (hB : 4 * B < 2 ^ w) :
    SBnd w (2 ^ 12) (4 * B) (oddHalf w wt neg j x) ∧ ∀ k < 4096,
      sval w (oddHalf w wt neg j x) k = (if oddPredF wt j k then -1 else 1) *
        (sval w x (k % 2048) + (if neg then -1 else 1) * sval w x (k % 2048 + 2048)) := by
  obtain ⟨h1, v1⟩ := colHalf_spec neg hx hB
  obtain ⟨h2, v2⟩ := sflip_spec h1 _ _ (oddMaskF_isFieldMask w wt j) hB
  refine ⟨h2, fun k hk => ?_⟩
  unfold oddHalf
  rw [v2 k (by norm_num; exact hk), v1 k hk]
  split_ifs <;> ring

/-- The weight sign predicate at an odd code label. -/
theorem oddPredF_wt (j d : ℕ) (hd : d < 2048) :
    (if oddPredF true j d then (-1 : ℚ) else 1) = oddWeightSignF d := by
  rw [oddWeightSignF_eq d hd, oddWeightSign, intSign_weight]
  have hq := qBits_spec ⟨d, by omega⟩
  simp only at hq
  rw [Nat.mod_eq_of_lt hd] at hq
  simp only [oddPredF, ↓reduceIte, hq]
  split_ifs <;> simp

/-- The coordinate sign predicate at an odd code label. -/
theorem oddPredF_co (j d : ℕ) (hd : d < 2048) :
    (if oddPredF false j d then (-1 : ℚ) else 1) = oddCoordSignF d j := by
  rw [oddCoordSignF_eq d j hd, oddCoordSign, golayEncodedMask_testBit]
  simp only [oddPredF, Bool.false_eq_true, ↓reduceIte]
  rw [bpar_low, Nat.mod_eq_of_lt hd]

/-! ## The packed cross terms -/

/-- The packed cross term: the odd terms `U` against signed half sums of the columns of `X`. -/
def oddXP (w : ℕ) (wt neg : Bool) (U : List (ℕ × ℤ)) (X : List SVec) : ℤ :=
  ((List.range 24).map (fun j => sdotM w (packOdd w j U) (oddHalf w wt neg j (tcol X j)))).sum

/-- A list sum times a constant. -/
theorem list_sum_mul_const {α : Type*} (U : List α) (f : α → ℤ) (c : ℤ) :
    (U.map f).sum * c = (U.map (fun q => f q * c)).sum := by
  induction U with
  | nil => simp
  | cons q U ih => simp only [List.map_cons, List.sum_cons, add_mul, ih]

/-- A rational list sum divided by a constant. -/
theorem list_sum_div_const {α : Type*} (U : List α) (f : α → ℚ) (c : ℚ) :
    (U.map f).sum / c = (U.map (fun q => f q / c)).sum := by
  induction U with
  | nil => simp
  | cons q U ih => simp only [List.map_cons, List.sum_cons, add_div, ih]

/-- A constant times a rational list sum. -/
theorem const_mul_list_sum {α : Type*} (U : List α) (f : α → ℚ) (c : ℚ) :
    c * (U.map f).sum = (U.map (fun q => c * f q)).sum := by
  induction U with
  | nil => simp
  | cons q U ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- Casting an integer list sum. -/
theorem cast_list_sum {α : Type*} (U : List α) (f : α → ℤ) :
    (((U.map f).sum : ℤ) : ℚ) = (U.map (fun q => (f q : ℚ))).sum := by
  induction U with
  | nil => simp
  | cons q U ih => simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]

/-- Exchanging a finite sum with a list sum. -/
theorem sum_range_list_swap {α : Type*} (U : List α) (f : α → ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (U.map (fun q => f q i)).sum =
      (U.map (fun q => ∑ i ∈ Finset.range n, f q i)).sum := by
  induction U with
  | nil => simp
  | cons q U ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

set_option maxRecDepth 100000 in
/-- A packed cross term is the sum over the odd terms of the signed half sums. -/
theorem oddXP_eq {w B : ℕ} (wt neg : Bool) (U : List (ℕ × ℤ)) {X : List SVec} (hX : TBnd w B X)
    (hB : 4 * B < 2 ^ w) (hU : absSumO U < 2 ^ w)
    (hUB : 2 * (2 * 4096 * (absSumO U * (4 * B))) < 2 ^ w) :
    oddXP w wt neg U X = (U.map (fun q => q.2 * sval w (oddHalf w wt neg (oddJ q.1)
      (tcol X (oddJ q.1))) (oddD q.1))).sum := by
  have key : ∀ j < 24, sdotM w (packOdd w j U) (oddHalf w wt neg j (tcol X j)) =
      (U.map (fun q => if oddJ q.1 = j then
        q.2 * sval w (oddHalf w wt neg j (tcol X j)) (oddD q.1) else 0)).sum := by
    intro j hj
    obtain ⟨p1, p2⟩ := packOdd_spec w j U hU
    obtain ⟨o1, -⟩ := oddHalf_spec wt neg j (hX j hj) hB
    rw [sdotM_eq p1 o1 hUB]
    simp only [p2, list_sum_mul_const]
    rw [sum_range_list_swap U (fun q i => (if oddJ q.1 = j ∧ oddD q.1 = i then q.2 else 0) *
      sval w (oddHalf w wt neg j (tcol X j)) i) 4096]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    have hd : oddD q.1 < 4096 := oddD_lt q.1
    by_cases hjq : oddJ q.1 = j
    · simp only [hjq, true_and, ↓reduceIte, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq (Finset.range 4096) (oddD q.1), ite_eq_left (Finset.mem_range.mpr hd)]
    · simp [hjq]
  unfold oddXP
  rw [list_sum_map_range, Finset.sum_congr rfl (fun j hj => key j (Finset.mem_range.mp hj)),
    sum_range_list_swap U (fun q j => if oddJ q.1 = j then
      q.2 * sval w (oddHalf w wt neg j (tcol X j)) (oddD q.1) else 0) 24]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  rw [Finset.sum_ite_eq (Finset.range 24) (oddJ q.1), ite_eq_left (Finset.mem_range.mpr (oddJ_lt q.1))]

/-- The odd short coordinate of the triality image, as a signed half sum. -/
theorem triOddF_packedX {w B : ℕ} (fwd : Bool) (L : IdentVec) {X : List SVec} {D : ℚ}
    (hLt : L.ten = tensorRat w X D) (hX : TBnd w B X) (hB : 4 * B < 2 ^ w) (lab : ℕ) :
    triOddF fwd L lab = (sval w (oddHalf w fwd (!fwd) (oddJ lab) (tcol X (oddJ lab)))
      (oddD lab) : ℚ) / (2 * D) := by
  have hd : oddD lab < 2048 := Nat.mod_lt _ (by norm_num)
  have hdk : oddD lab < 4096 := by omega
  obtain ⟨-, v⟩ := oddHalf_spec fwd (!fwd) (oddJ lab) (hX (oddJ lab) (oddJ_lt lab)) hB
  rw [v (oddD lab) hdk, Nat.mod_eq_of_lt hd]
  unfold triOddF
  simp only [hLt, tensorRat]
  cases fwd
  · rw [← oddPredF_co (oddJ lab) (oddD lab) hd]
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    push_cast
    split_ifs <;> ring
  · rw [← oddPredF_wt (oddJ lab) (oddD lab) hd]
    simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]
    push_cast
    split_ifs <;> ring

/-- The tensor contribution of an odd term of `L`, as a signed half sum of `W`. -/
theorem triTCF_packedX {w C : ℕ} (fwd : Bool) (W : IdentVec) {Y : List SVec} {E : ℚ}
    (hWt : W.ten = tensorRat w Y E) (hY : TBnd w C Y) (hC : 4 * C < 2 ^ w) (lab : ℕ) :
    triTCF fwd W lab = (sval w (oddHalf w (!fwd) fwd (oddJ lab) (tcol Y (oddJ lab)))
      (oddD lab) : ℚ) / E := by
  have hd : oddD lab < 2048 := Nat.mod_lt _ (by norm_num)
  have hdk : oddD lab < 4096 := by omega
  obtain ⟨-, v⟩ := oddHalf_spec (!fwd) fwd (oddJ lab) (hY (oddJ lab) (oddJ_lt lab)) hC
  rw [v (oddD lab) hdk, Nat.mod_eq_of_lt hd]
  unfold triTCF
  simp only [hWt, tensorRat]
  cases fwd
  · rw [← oddPredF_wt (oddJ lab) (oddD lab) hd]
    simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    push_cast
    split_ifs <;> ring
  · rw [← oddPredF_co (oddJ lab) (oddD lab) hd]
    simp only [Bool.not_true, ↓reduceIte]
    push_cast
    split_ifs <;> ring

/-- The odd terms of `W` against the triality image of `L`, packed. -/
theorem oddX_eq {w B : ℕ} (fwd : Bool) (L : IdentVec) {X : List SVec} {D : ℚ}
    (hLt : L.ten = tensorRat w X D) (hX : TBnd w B X) (hB : 4 * B < 2 ^ w) (U : List (ℕ × ℤ))
    (hU : absSumO U < 2 ^ w) (hUB : 2 * (2 * 4096 * (absSumO U * (4 * B))) < 2 ^ w) :
    (U.map (fun q => (q.2 : ℚ) * triOddF fwd L q.1)).sum =
      (oddXP w fwd (!fwd) U X : ℚ) / (2 * D) := by
  rw [oddXP_eq fwd (!fwd) U hX hB hU hUB, cast_list_sum, list_sum_div_const]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  rw [triOddF_packedX fwd L hLt hX hB q.1]
  push_cast
  ring

/-- The odd terms of `L` against the tensor of `W`, packed. -/
theorem oddTC_eq {w C : ℕ} (fwd : Bool) (W : IdentVec) {Y : List SVec} {E : ℚ}
    (hWt : W.ten = tensorRat w Y E) (hY : TBnd w C Y) (hC : 4 * C < 2 ^ w) (U : List (ℕ × ℤ))
    (hU : absSumO U < 2 ^ w) (hUC : 2 * (2 * 4096 * (absSumO U * (4 * C))) < 2 ^ w) (s : ℚ) :
    (U.map (fun q => s * (q.2 : ℚ) * triTCF fwd W q.1)).sum =
      s * (oddXP w (!fwd) fwd U Y : ℚ) / E := by
  rw [oddXP_eq (!fwd) fwd U hY hC hU hUC, cast_list_sum, mul_div_assoc, list_sum_div_const,
    const_mul_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  rw [triTCF_packedX fwd W hWt hY hC q.1]
  push_cast
  ring

/-! ## The pairing with packed tensor cross terms -/

/-- The exact triality pairing with all tensor terms packed: the matrix part, the pair and octad
short parts of `pairTriG`, and the two odd cross terms and the tensor part as packed dot
products. -/
def pairTriX (w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W +
    W.sden * ((W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF fwd L q.1)).sum +
      (W.sh.oct.map (fun b => (b.2.map (fun q => (q.2 : ℚ) * triOctT fwd L b.1 q.1)).sum)).sum +
      (oddXP w fwd (!fwd) W.sh.odd X : ℚ) / (2 * D)) +
    (L.sden * (oddXP w (!fwd) fwd L.sh.odd Y : ℚ) / E +
      (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- The numeric side conditions of `pairTriX`. -/
structure PairXBounds (w B C : ℕ) (L W : IdentVec) : Prop where
  hB : 4 * B < 2 ^ w
  hC : 4 * C < 2 ^ w
  hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w
  hW1 : absSumO W.sh.odd < 2 ^ w
  hW2 : 2 * (2 * 4096 * (absSumO W.sh.odd * (4 * B))) < 2 ^ w
  hL1 : absSumO L.sh.odd < 2 ^ w
  hL2 : 2 * (2 * 4096 * (absSumO L.sh.odd * (4 * C))) < 2 ^ w

/-- With packed tensors and bounds, `pairTriX` is the exact pairing. -/
theorem pairTriX_eq {w B C : ℕ} (fwd : Bool) (L W : IdentVec) {X Y : List SVec} {D E : ℚ}
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hb : PairXBounds w B C L W) :
    pairTriX w fwd L W X Y D E = pairTri fwd L W := by
  rw [← pairTriGM_eq fwd L W hLt hWt hX hY hb.hB hb.hBC]
  unfold pairTriX pairTriGM triShortG
  rw [oddX_eq fwd L hLt hX hb.hB W.sh.odd hb.hW1 hb.hW2,
    oddTC_eq fwd W hWt hY hb.hC L.sh.odd hb.hL1 hb.hL2 L.sden]

/-- Forward identification from `pairTriX`. -/
theorem ident_forward_X (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hb : PairXBounds w B C L W)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriX w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward i j h g L W hL hW hx hy (by rw [← pairTriX_eq true L W hLt hWt hX hY hb, hp])

/-- Inverse identification from `pairTriX`. -/
theorem ident_inverse_X (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hb : PairXBounds w B C L W)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriX w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse i j h g L W hL hW hx hy (by rw [← pairTriX_eq false L W hLt hWt hX hY hb, hp])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
