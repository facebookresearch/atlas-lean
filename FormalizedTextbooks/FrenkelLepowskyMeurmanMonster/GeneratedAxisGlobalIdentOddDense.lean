/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOctadFastDense
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorOddX

/-! # Dense odd parts of the pairing

The integer odd parts `oddWZ` / `oddLZ` of `pairTriGMZ` read single packed tensor fields term by
term; on dense vectors (tens of thousands of odd terms) this exhausts kernel memory, and so do
the list-based packers (`oddXP`, `packH`).  Here, as in the dense octad part (`OctadDense`), the
odd terms are packed in a single pass over the literal target chunks (`oddPack`, range
accumulators, Nat operations only) at reversed indices (`2^16` fields, `2048` per tensor column),
the low halves of the signed half sums or differences of the 24 tensor columns are laid side by
side (`halfFlatA`), and the odd sum is the middle field of one product (`octMidDot`).
`oddWZ_of_chk` / `oddLZ_of_chk` give the integer parts from one kernel check `oddChk`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators
set_option autoImplicit false

namespace OddDense
open OctadDense

/-! ## The chunk pass over odd terms -/

/-- The reversed field index (`2^16` fields, `2048` per tensor column) of an odd label. -/
def oddIdx (l : ℕ) : ℕ := 65535 - (2048 * oddJ l + oddD l)

/-- An odd term at its reversed index (other terms are dropped). -/
def oddOne (p : ℕ × ℤ) : List (ℕ × ℤ) := if 49128 ≤ p.1 then [(oddIdx p.1, p.2)] else []

/-- One term of a chunk pass: odd labels are added at the reversed index. -/
def oddStep (w l c : ℕ) (x : OctAcc) : OctAcc :=
  cond (Nat.ble 49128 l)
    (octAccAdd (oddIdx l >>> 13) (Nat.blt c 128)
      (((c - 128) + (128 - c)) <<< (w * (oddIdx l &&& 8191))) x.1,
      x.2 + ((c - 128) + (128 - c)))
    x

/-- The packed odd terms of a chunk list and their absolute sum. -/
def oddPack (w : ℕ) (cs : List (ℕ × ℕ × ℕ)) : SVec × ℕ :=
  let x := octLoops (oddStep w) cs octAccZero
  (octAccFlat w x.1, x.2)

theorem oddIdx_lt (l : ℕ) : oddIdx l < 65536 := by
  unfold oddIdx
  omega

theorem oddStep_spec (w l c : ℕ) (hc : c < 256) (x : OctAcc) :
    octAccFlat w (oddStep w l c x).1 =
      sadd (octAccFlat w x.1) (packF w ([(l, (c : ℤ) - 128)].flatMap oddOne)) ∧
    (oddStep w l c x).2 = x.2 + absSum ([(l, (c : ℤ) - 128)].flatMap oddOne) := by
  by_cases hl : 49128 ≤ l
  · have hb : Nat.ble 49128 l = true := Nat.ble_eq.mpr hl
    have hflat : [(l, (c : ℤ) - 128)].flatMap oddOne = [(oddIdx l, (c : ℤ) - 128)] := by
      simp [oddOne, hl]
    simp only [oddStep, hb, Bool.cond_true]
    rw [hflat, octAccFlat_add w _ (octRange_lt _ (oddIdx_lt l)), octSshl_partV, octSplit13]
    refine ⟨?_, ?_⟩
    · have hv := octPartV_eq w (oddIdx l) c false hc
      rw [Bool.xor_false] at hv
      rw [hv]
      simp [packF, octSadd_zero]
    · simp only [absSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [show ((c : ℤ) - 128) = 1 * ((c : ℤ) - 128) by ring, octSgl_abs c hc 1 (Or.inl rfl)]
  · have hb : Nat.ble 49128 l = false := by
      cases h : Nat.ble 49128 l
      · rfl
      · exact absurd (Nat.ble_eq.mp h) hl
    have hflat : [(l, (c : ℤ) - 128)].flatMap oddOne = [] := by simp [oddOne, hl]
    simp only [oddStep, hb, Bool.cond_false, hflat]
    exact ⟨(octSadd_zero _).symm, by simp [absSum]⟩

/-- The pass is the exact packing of the odd terms. -/
theorem oddPack_spec (w : ℕ) (cs : List (ℕ × ℕ × ℕ)) :
    (oddPack w cs).1 = packF w ((octChunkTerms cs).flatMap oddOne) ∧
      (oddPack w cs).2 = absSum ((octChunkTerms cs).flatMap oddOne) := by
  obtain ⟨h1, h2⟩ := octLoops_spec w (oddStep w) oddOne
    (fun l c x hc => oddStep_spec w l c hc x) cs octAccZero
  rw [octAccFlat_zero, octZero_sadd] at h1
  exact ⟨h1, by rw [oddPack, h2]; simp [octAccZero]⟩

/-- The odd terms at their reversed indices are the mapped odd filter. -/
theorem flatMap_oddOne (T : List (ℕ × ℤ)) :
    T.flatMap oddOne = (T.filter (fun p => decide (49128 ≤ p.1))).map (fun q => (oddIdx q.1, q.2)) := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    rw [List.flatMap_cons, List.filter_cons, ih]
    by_cases h : 49128 ≤ p.1
    · simp [oddOne, h]
    · simp [oddOne, h]

/-! ## The tensor side: low halves side by side -/

/-- The low half (`2048` fields) of the signed half sum or difference of column `j`. -/
def halfLow (w : ℕ) (wt neg : Bool) (X : List SVec) (j : ℕ) : SVec :=
  ((oddHalf w wt neg j (tcol X j)).1 &&& allMask w 2048,
    (oddHalf w wt neg j (tcol X j)).2 &&& allMask w 2048)

/-- The first `k` low halves side by side, `2048` fields each. -/
def halfFlatA (w : ℕ) (wt neg : Bool) (X : List SVec) : ℕ → SVec
  | 0 => szero
  | k + 1 => ((halfFlatA w wt neg X k).1 ||| ((halfLow w wt neg X k).1 <<< (w * (2048 * k))),
      (halfFlatA w wt neg X k).2 ||| ((halfLow w wt neg X k).2 <<< (w * (2048 * k))))

theorem fld_eq_zero_of_lt {w P n i : ℕ} (hP : P < 2 ^ (w * n)) (hi : n ≤ i) : fld w P i = 0 := by
  have h1 : P < 2 ^ (w * i) :=
    lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hi))
  simp [fld, Nat.div_eq_of_lt h1]

theorem shl_lt {w x m s : ℕ} (hx : x < 2 ^ (w * m)) : x <<< (w * s) < 2 ^ (w * (m + s)) := by
  rw [Nat.shiftLeft_eq, Nat.mul_add, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hx (by positivity)

theorem allMask_lt (w n : ℕ) : allMask w n < 2 ^ (w * n) :=
  Nat.sub_lt (by positivity) one_pos

theorem halfLow_lt (w : ℕ) (wt neg : Bool) (X : List SVec) (j : ℕ) :
    (halfLow w wt neg X j).1 < 2 ^ (w * 2048) ∧ (halfLow w wt neg X j).2 < 2 ^ (w * 2048) :=
  ⟨lt_of_le_of_lt Nat.and_le_right (allMask_lt w 2048),
    lt_of_le_of_lt Nat.and_le_right (allMask_lt w 2048)⟩

theorem halfLow_fld (w : ℕ) (wt neg : Bool) (X : List SVec) (j i : ℕ) :
    fld w (halfLow w wt neg X j).1 i =
        (if i < 2048 then fld w (oddHalf w wt neg j (tcol X j)).1 i else 0) ∧
      fld w (halfLow w wt neg X j).2 i =
        (if i < 2048 then fld w (oddHalf w wt neg j (tcol X j)).2 i else 0) := by
  simp only [halfLow, fld_land, fld_allMask]
  constructor <;> split_ifs <;>
    simp [Nat.and_two_pow_sub_one_of_lt_two_pow (fld_lt _ _ _)]

theorem halfFlatA_lt (w : ℕ) (wt neg : Bool) (X : List SVec) : ∀ k,
    (halfFlatA w wt neg X k).1 < 2 ^ (w * (2048 * k)) ∧
      (halfFlatA w wt neg X k).2 < 2 ^ (w * (2048 * k))
  | 0 => by simp [halfFlatA, szero]
  | k + 1 => by
    obtain ⟨a1, a2⟩ := halfFlatA_lt w wt neg X k
    obtain ⟨c1, c2⟩ := halfLow_lt w wt neg X k
    have e : w * (2048 * (k + 1)) = w * (2048 + 2048 * k) := by ring
    have m : 2 ^ (w * (2048 * k)) ≤ 2 ^ (w * (2048 + 2048 * k)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w (by omega))
    simp only [halfFlatA]
    rw [e]
    exact ⟨Nat.or_lt_two_pow (lt_of_lt_of_le a1 m) (shl_lt c1),
      Nat.or_lt_two_pow (lt_of_lt_of_le a2 m) (shl_lt c2)⟩

theorem halfFlatA_fld (w : ℕ) (wt neg : Bool) (X : List SVec) : ∀ k t,
    fld w (halfFlatA w wt neg X k).1 t =
        (if t < 2048 * k then fld w (halfLow w wt neg X (t / 2048)).1 (t % 2048) else 0) ∧
      fld w (halfFlatA w wt neg X k).2 t =
        (if t < 2048 * k then fld w (halfLow w wt neg X (t / 2048)).2 (t % 2048) else 0)
  | 0, t => by simp [halfFlatA, szero, fld_zero_right_zero]
  | k + 1, t => by
    obtain ⟨a1, a2⟩ := halfFlatA_fld w wt neg X k t
    obtain ⟨c1, c2⟩ := halfLow_lt w wt neg X k
    simp only [halfFlatA]
    rw [fld_lor, fld_lor, a1, a2, fld_shiftLeft, fld_shiftLeft]
    by_cases h1 : t < 2048 * k
    · have h2 : t < 2048 * (k + 1) := by omega
      have h3 : ¬ (2048 * k ≤ t) := by omega
      simp [h1, h2, h3]
    · by_cases h2 : t < 2048 * (k + 1)
      · have h3 : 2048 * k ≤ t := by omega
        have h4 : t / 2048 = k := by omega
        have h5 : t % 2048 = t - 2048 * k := by omega
        simp [h1, h2, h3, h4, h5]
      · have h3 : 2048 * k ≤ t := by omega
        have z1 := fld_eq_zero_of_lt c1 (show 2048 ≤ t - 2048 * k by omega)
        have z2 := fld_eq_zero_of_lt c2 (show 2048 ≤ t - 2048 * k by omega)
        simp [h1, h2, h3, z1, z2]

/-! ## The dense odd sum -/

/-- The checked dense odd sum of the odd terms of a chunk list against the signed half sums
(`wt`: Golay weight signs, else coordinate signs; `neg`: differences) of the columns of `X`. -/
def oddChk (w B : ℕ) (wt neg : Bool) (cs : List (ℕ × ℕ × ℕ)) (X : List SVec) (n : ℤ) : Bool :=
  let P := oddPack w cs
  decide (4 * B < 2 ^ w) && decide (P.2 < 2 ^ w) &&
    decide (2 * (2 * 65536 * (P.2 * (4 * B))) < 2 ^ w) &&
    decide (octMidDot w P.1 (halfFlatA w wt neg X 24) = n)

/-- A finite sum against field sums of a sparse list is the sum over the list. -/
theorem sum_idxSum (n : ℕ) (f : ℕ → ℤ) : ∀ E : List (ℕ × ℤ), (∀ e ∈ E, e.1 < n) →
    ∑ i ∈ Finset.range n, idxSum E i * f i = (E.map (fun e => e.2 * f e.1)).sum
  | [], _ => by simp [idxSum]
  | e :: E, hE => by
    have h1 : e.1 < n := hE e (by simp)
    have ih := sum_idxSum n f E (fun x hx => hE x (by simp [hx]))
    have hs : ∀ i, idxSum (e :: E) i = (if e.1 = i then e.2 else 0) + idxSum E i := by
      intro i
      simp [idxSum]
    simp only [hs, add_mul, Finset.sum_add_distrib, ih, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_range, h1, ↓reduceIte, List.map_cons, List.sum_cons]

set_option maxRecDepth 100000 in
/-- The checked dense odd sum is the sum over the odd terms of the signed half sums. -/
theorem oddChk_sum {w B : ℕ} {wt neg : Bool} {cs : List (ℕ × ℕ × ℕ)} {X : List SVec} {n : ℤ}
    (hX : TBnd w B X) (h : oddChk w B wt neg cs X n = true) :
    (((octChunkTerms cs).filter (fun p => decide (49128 ≤ p.1))).map (fun q =>
      q.2 * sval w (oddHalf w wt neg (oddJ q.1) (tcol X (oddJ q.1))) (oddD q.1))).sum = n := by
  obtain ⟨p1, p2⟩ := oddPack_spec w cs
  simp only [oddChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hB, hA⟩, hAB⟩, hv⟩ := h
  rw [p1] at hv
  rw [p2] at hA hAB
  set E := (octChunkTerms cs).flatMap oddOne with hEdef
  have hE : ∀ e ∈ E, e.1 < 65536 := by
    intro e he
    rw [hEdef, List.mem_flatMap] at he
    obtain ⟨p, _, hp⟩ := he
    unfold oddOne at hp
    split_ifs at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rw [hp]
      exact oddIdx_lt _
    · simp at hp
  obtain ⟨hP, hval⟩ := packF_spec w 65536 E hE hA
  have e12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hcs : ∀ j < 24, SBnd w 4096 (4 * B) (oddHalf w wt neg j (tcol X j)) := by
    intro j hj
    have h := (oddHalf_spec wt neg j (hX j hj) hB).1
    rw [e12] at h
    exact h
  have hlt := halfFlatA_lt w wt neg X 24
  have hfl := halfFlatA_fld w wt neg X 24
  have hpow : 2 ^ (w * (2048 * 24)) ≤ 2 ^ (w * 65536) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w (by norm_num))
  have hR : SBnd w 65536 (4 * B) (halfFlatA w wt neg X 24) := by
    refine ⟨lt_of_lt_of_le hlt.1 hpow, lt_of_lt_of_le hlt.2 hpow, fun t _ => ?_⟩
    obtain ⟨f1, f2⟩ := hfl t
    rw [f1, f2]
    split_ifs with ht
    · obtain ⟨g1, g2⟩ := halfLow_fld w wt neg X (t / 2048) (t % 2048)
      rw [g1, g2, ite_eq_left (by omega), ite_eq_left (by omega)]
      exact (hcs (t / 2048) (by omega)).2.2 (t % 2048) (by omega)
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  rw [octMidDot_eq hP hR hAB,
    Finset.sum_congr rfl (fun i hi => by rw [hval i (Finset.mem_range.mp hi)]),
    sum_idxSum 65536 (fun i => sval w (halfFlatA w wt neg X 24) (65535 - i)) E hE,
    hEdef, flatMap_oddOne, List.map_map] at hv
  rw [← hv]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  have hd : oddD q.1 < 2048 := Nat.mod_lt _ (by norm_num)
  have hj : oddJ q.1 < 24 := oddJ_lt q.1
  have ht : 65535 - oddIdx q.1 = 2048 * oddJ q.1 + oddD q.1 := by
    simp only [oddIdx]
    omega
  obtain ⟨f1, f2⟩ := hfl (2048 * oddJ q.1 + oddD q.1)
  obtain ⟨g1, g2⟩ := halfLow_fld w wt neg X (oddJ q.1) (oddD q.1)
  have h1 : 2048 * oddJ q.1 + oddD q.1 < 2048 * 24 := by omega
  have h2 : (2048 * oddJ q.1 + oddD q.1) / 2048 = oddJ q.1 := by omega
  have h3 : (2048 * oddJ q.1 + oddD q.1) % 2048 = oddD q.1 := by omega
  simp only [Function.comp_apply, ht, sval, f1, f2, h1, ↓reduceIte, h2, h3, g1, g2, hd]

/-! ## The integer odd parts -/

theorem odd_ofList (V : IdentVec) (cs : List (ℕ × ℕ × ℕ))
    (hV : V.sh = ShortData.ofList (octChunkTerms cs)) :
    V.sh.odd = (octChunkTerms cs).filter (fun p => decide (49128 ≤ p.1)) := by
  rw [hV]
  rfl

/-- The integer odd part of `W` (odd terms of `W` against the triality image of `L`). -/
theorem oddWZ_of_chk {w B : ℕ} (fwd : Bool) (L W : IdentVec) (CW : List (ℕ × ℕ × ℕ))
    {X : List SVec} {D : ℚ} (hW : W.sh = ShortData.ofList (octChunkTerms CW))
    (hLt : L.ten = tensorRat w X D) (hD : D ≠ 0) (hX : TBnd w B X) {n : ℤ}
    (h : oddChk w B fwd (!fwd) CW X n = true) : oddWZ w fwd X W = n := by
  have hB : 4 * B < 2 ^ w := by
    simp only [oddChk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1
  have hs := oddChk_sum hX h
  rw [← odd_ofList W CW hW] at hs
  have e1 := oddW_packed w fwd L W X D hLt
  have e2 : (W.sh.odd.map (fun q => (q.2 : ℚ) * triOddF fwd L q.1)).sum = (n : ℚ) / (2 * D) := by
    rw [← hs, cast_list_sum, list_sum_div_const]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    rw [triOddF_packedX fwd L hLt hX hB q.1]
    push_cast
    ring
  rw [e1] at e2
  have h2D : (2 * D) ≠ 0 := mul_ne_zero two_ne_zero hD
  exact_mod_cast (div_left_inj' h2D).mp e2

/-- The integer odd part of `L` (odd terms of `L` against the tensor of `W`). -/
theorem oddLZ_of_chk {w C : ℕ} (fwd : Bool) (L W : IdentVec) (CL : List (ℕ × ℕ × ℕ))
    {Y : List SVec} {E : ℚ} (hL : L.sh = ShortData.ofList (octChunkTerms CL))
    (hWt : W.ten = tensorRat w Y E) (hE : E ≠ 0) (hs : L.sden ≠ 0) (hY : TBnd w C Y) {n : ℤ}
    (h : oddChk w C (!fwd) fwd CL Y n = true) : oddLZ w fwd Y L = n := by
  have hC : 4 * C < 2 ^ w := by
    simp only [oddChk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1
  have hsum := oddChk_sum hY h
  rw [← odd_ofList L CL hL] at hsum
  have e1 := oddL_packed w fwd L W Y E hWt
  have e2 : (L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum =
      L.sden * (n : ℚ) / E := by
    rw [← hsum, cast_list_sum, mul_div_assoc, list_sum_div_const, const_mul_list_sum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    rw [triTCF_packedX fwd W hWt hY hC q.1]
    push_cast
    ring
  rw [e1] at e2
  exact_mod_cast mul_left_cancel₀ hs ((div_left_inj' hE).mp e2)

end OddDense

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
