/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWDense

/-! # Factory: the self octad sum of a dense target in one pass over its packed chunks (gident2)

`selfOctM` packs the octad terms by range halving; on a target given by packed chunks the kernel
re-evaluates the chunk decoding in every branch of the halving.  `selfOctChk` instead packs the
octad terms of the chunks in one sequential pass each, at the field indices `t = label - 552`
(gtenth's `OctadDense.octPackL`) and at the reversed indices `65535 - t` (`octPackR`, same
accumulator), and reads the self sum `selfOctZ` from the middle field of two products
(`selfOctZ_of_chk`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
namespace OctadDense
open scoped BigOperators
set_option autoImplicit false

/-- One term of a target: octad labels are added at the reversed field index `65535 - t`. -/
def octRStep (w l c : ℕ) (x : OctAcc) : OctAcc :=
  cond (Nat.ble 552 l && Nat.blt l 49128)
    (octAccAdd ((65535 - (l - 552)) >>> 13) (Nat.blt c 128)
      (((c - 128) + (128 - c)) <<< (w * ((65535 - (l - 552)) &&& 8191))) x.1,
      x.2 + ((c - 128) + (128 - c)))
    x

/-- The octad term of one term at its reversed field index. -/
def octRevOne (p : ℕ × ℤ) : List (ℕ × ℤ) :=
  if octLabel p = true then [(65535 - (p.1 - 552), p.2)] else []

/-- The octad terms of a term list at their reversed field indices. -/
def octRevOf (T : List (ℕ × ℤ)) : List (ℕ × ℤ) := T.flatMap octRevOne

theorem octRStep_spec (w l c : ℕ) (hc : c < 256) (x : OctAcc) :
    octAccFlat w (octRStep w l c x).1 =
      sadd (octAccFlat w x.1) (packF w (octRevOf [(l, (c : ℤ) - 128)])) ∧
    (octRStep w l c x).2 = x.2 + absSum (octRevOf [(l, (c : ℤ) - 128)]) := by
  by_cases hl : 552 ≤ l ∧ l < 49128
  · have hb : (Nat.ble 552 l && Nat.blt l 49128) = true := by
      simp [Nat.ble_eq, Nat.blt_eq, hl.1, hl.2]
    have hlab : octLabel (l, (c : ℤ) - 128) = true := by
      simp [octLabel, hl.1, hl.2]
    have hflat : octRevOf [(l, (c : ℤ) - 128)] = [(65535 - (l - 552), (c : ℤ) - 128)] := by
      simp [octRevOf, octRevOne, hlab]
    simp only [octRStep, hb, Bool.cond_true]
    rw [hflat, octAccFlat_add w _ (octRange_lt _ (by omega)), octSshl_partV, octSplit13]
    refine ⟨?_, ?_⟩
    · have hv := octPartV_eq w (65535 - (l - 552)) c false hc
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
    have hflat : octRevOf [(l, (c : ℤ) - 128)] = [] := by
      simp [octRevOf, octRevOne, hlab]
    simp only [octRStep, hb, Bool.cond_false, hflat]
    exact ⟨(octSadd_zero _).symm, by simp [absSum]⟩

/-- The packed reversed octad terms of a target and their absolute sum. -/
def octPackR (w : ℕ) (cs : List (ℕ × ℕ × ℕ)) : SVec × ℕ :=
  let x := octLoops (octRStep w) cs octAccZero
  (octAccFlat w x.1, x.2)

/-- The reversed pass is the exact packing of the reversed octad terms. -/
theorem octPackR_spec (w : ℕ) (cs : List (ℕ × ℕ × ℕ)) :
    (octPackR w cs).1 = packF w (octRevOf (octChunkTerms cs)) ∧
      (octPackR w cs).2 = absSum (octRevOf (octChunkTerms cs)) := by
  have hstep : ∀ l c x, c < 256 →
      octAccFlat w (octRStep w l c x).1 =
        sadd (octAccFlat w x.1) (packF w ([(l, (c : ℤ) - 128)].flatMap octRevOne)) ∧
      (octRStep w l c x).2 = x.2 + absSum ([(l, (c : ℤ) - 128)].flatMap octRevOne) :=
    fun l c x hc => octRStep_spec w l c hc x
  obtain ⟨h1, h2⟩ := octLoops_spec w (octRStep w) octRevOne hstep cs octAccZero
  rw [octAccFlat_zero, octZero_sadd] at h1
  exact ⟨h1, by rw [octPackR, h2]; simp [octAccZero, octRevOf]⟩

/-- The reversed octad terms are the octad terms at reversed indices. -/
theorem octRevOf_eq (T : List (ℕ × ℤ)) :
    octRevOf T = (octFlatOf T).map (fun p => (65535 - p.1, p.2)) := by
  induction T with
  | nil => rfl
  | cons p T ih =>
    unfold octRevOf octFlatOf at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]
    unfold octRevOne octFlatOne
    split_ifs <;> rfl

/-- The checked self octad sum of a target given by packed chunks: no overflow in the product,
and the middle field is `s`. -/
def selfOctChk (w : ℕ) (CW : List (ℕ × ℕ × ℕ)) (s : ℤ) : Bool :=
  let PL := octPackL w CW
  let PR := octPackR w CW
  decide (2 * (2 * 65536 * ((PL.2 + 1) * (PL.2 + 1))) < 2 ^ w) && decide (octMidDot w PL.1 PR.1 = s)

/-- The checked self octad sum is the collapsed octad self sum. -/
theorem selfOctZ_of_chk (w : ℕ) (W : IdentVec) (CW : List (ℕ × ℕ × ℕ)) (s : ℤ)
    (hW : W.sh = ShortData.ofList (octChunkTerms CW)) (h : selfOctChk w CW s = true) :
    selfOctZ W = s := by
  obtain ⟨pL1, pL2⟩ := octPackL_spec w CW
  obtain ⟨pR1, _⟩ := octPackR_spec w CW
  simp only [selfOctChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hbig, hv⟩ := h
  have hflat := octLFlat_ofList W (octChunkTerms CW) hW
  rw [pL2, ← hflat] at hbig
  rw [pL1, pR1, octRevOf_eq, ← hflat] at hv
  set S := absSum (octLFlat W) with hSdef
  have h1 : ∀ p ∈ octLFlat W, p.1 < 2 ^ 16 := by
    intro p hp
    rw [hflat] at hp
    exact lt_of_lt_of_le (octFlatOf_lt _ p hp) (by norm_num)
  have hS : S < 2 ^ w := by
    have : S < 2 * (2 * 65536 * ((S + 1) * (S + 1))) := by nlinarith
    omega
  have hrev : ∀ p ∈ octRevFlat W, p.1 < 2 ^ 16 := by
    intro p hp
    unfold octRevFlat at hp
    rw [List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    simp only
    norm_num
    omega
  have hSr : absSum (octRevFlat W) = S := by
    unfold octRevFlat absSum
    rw [List.map_map]
    rfl
  obtain ⟨a1, a2⟩ := packF_spec w (2 ^ 16) (octLFlat W) h1 hS
  obtain ⟨b1, b2⟩ := packF_spec w (2 ^ 16) (octRevFlat W) hrev (by rw [hSr]; exact hS)
  rw [hSr] at b1
  have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  rw [e16] at a1 b1 a2 b2 h1
  have hv' : octMidDot w (packF w (octLFlat W)) (packF w (octRevFlat W)) = s := hv
  rw [← hv', octMidDot_eq a1 b1 (by nlinarith)]
  have hterm : ∀ i ∈ Finset.range 65536,
      sval w (packF w (octLFlat W)) i * sval w (packF w (octRevFlat W)) (65535 - i) =
        idxSum (octLFlat W) i * idxSum (octLFlat W) i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [a2 i hi', b2 (65535 - i) (by omega)]
    unfold octRevFlat
    rw [idxSum_rev _ h1 i hi']
  rw [Finset.sum_congr rfl hterm, sum_mul_idxSum _ 65536 _ h1]
  rfl

end OctadDense
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
