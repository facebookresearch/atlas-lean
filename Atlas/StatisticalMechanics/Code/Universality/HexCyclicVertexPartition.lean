/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































import Code.Universality.HexFiniteRegion
import Code.Universality.HexInfraWinding

namespace StatMech.Universality

open Complex Function HexWalk
open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}




def hexCyclicSucc : Fin 3 → Fin 3
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | _ => 0


def hexCyclicPred : Fin 3 → Fin 3
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 0
  | _ => 1

@[simp] theorem hexCyclicSucc_pred (j : Fin 3) :
    hexCyclicSucc (hexCyclicPred j) = j := by
  fin_cases j <;> rfl

@[simp] theorem hexCyclicPred_succ (j : Fin 3) :
    hexCyclicPred (hexCyclicSucc j) = j := by
  fin_cases j <;> rfl



theorem hexCyclicSucc_mid (v du : ℂ) (j : Fin 3) :
    labelMid v du (hexCyclicSucc j) =
      v + hexOmega * (labelMid v du j - v) := by
  have hcube : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  fin_cases j
  · simp [hexCyclicSucc, labelMid]
  · simp [hexCyclicSucc, labelMid]
    ring
  · simp [hexCyclicSucc, labelMid]
    rw [show hexOmega * (hexOmega ^ 2 * du) = hexOmega ^ 3 * du by ring,
      hcube, one_mul]



theorem hexCyclicPred_mid (v du : ℂ) (j : Fin 3) :
    labelMid v du (hexCyclicPred j) =
      v + hexOmega ^ 2 * (labelMid v du j - v) := by
  have hcube : hexOmega ^ 3 = 1 := hexOmega_primRoot.pow_eq_one
  fin_cases j <;> simp [hexCyclicPred, labelMid]
  · rw [show hexOmega ^ 2 * (hexOmega * du) = hexOmega ^ 3 * du by ring,
      hcube, one_mul]
  · rw [show hexOmega ^ 2 * (hexOmega ^ 2 * du) = hexOmega * (hexOmega ^ 3 * du) by ring,
      hcube, one_mul]






structure HexCyclicTriplet (region : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) where
  baseLabel : Fin 3
  base : List ℤ
  base_valid :
    (ofTurns a h0 base).IsLegalSAW ∧
      (ofTurns a h0 base).StaysIn region ∧
      (ofTurns a h0 base).EndsAt (labelMid v du baseLabel)
  succ_valid :
    (ofTurns a h0 (base ++ [-1])).IsLegalSAW ∧
      (ofTurns a h0 (base ++ [-1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [-1])).EndsAt
        (labelMid v du (hexCyclicSucc baseLabel))
  pred_valid :
    (ofTurns a h0 (base ++ [1])).IsLegalSAW ∧
      (ofTurns a h0 (base ++ [1])).StaysIn region ∧
      (ofTurns a h0 (base ++ [1])).EndsAt
        (labelMid v du (hexCyclicPred baseLabel))




theorem HexCyclicTriplet.contribution_zero
    (C : HexCyclicTriplet region a h0 v du) :
    (labelMid v du C.baseLabel - v) *
        parafSummand region a h0 (labelMid v du C.baseLabel)
          (5 / 8) hexChi C.base
      + (labelMid v du (hexCyclicSucc C.baseLabel) - v) *
          parafSummand region a h0
            (labelMid v du (hexCyclicSucc C.baseLabel))
            (5 / 8) hexChi (C.base ++ [-1])
      + (labelMid v du (hexCyclicPred C.baseLabel) - v) *
          parafSummand region a h0
            (labelMid v du (hexCyclicPred C.baseLabel))
            (5 / 8) hexChi (C.base ++ [1]) = 0 := by
  let d : ℂ := labelMid v du C.baseLabel - v
  have hbase : v + d = labelMid v du C.baseLabel := by
    simp [d]
  have hsucc : v + hexOmega * d =
      labelMid v du (hexCyclicSucc C.baseLabel) := by
    simpa [d] using (hexCyclicSucc_mid v du C.baseLabel).symm
  have hpred : v + hexOmega ^ 2 * d =
      labelMid v du (hexCyclicPred C.baseLabel) := by
    simpa [d] using (hexCyclicPred_mid v du C.baseLabel).symm
  have hz := genuine_triplet_zero region a h0 v d C.base
    (by simpa [hbase] using C.base_valid)
    (by simpa [hsucc] using C.succ_valid)
    (by simpa [hpred] using C.pred_valid)
  simpa [hbase, hsucc, hpred] using hz




theorem hexCyclic_midAccum_append_single (m : ℂ) (h t : ℤ)
    (ts : List ℤ) :
    hexInfra_midAccum m h (ts ++ [t]) =
      hexInfra_midAccum m h ts +
        halfStep (hexInfra_headAccum h ts) +
        halfStep (hexInfra_headAccum h ts + t) := by
  induction ts generalizing m h with
  | nil => simp
  | cons u us ih =>
      simpa only [List.cons_append, hexInfra_midAccum_cons,
        hexInfra_headAccum_cons] using
        ih (m + halfStep h + halfStep (h + u)) (h + u)



theorem hexCyclic_midsAux_append_single (m : ℂ) (h t : ℤ)
    (ts : List ℤ) :
    midsAux m h (ts ++ [t]) =
      midsAux m h ts ++
        [hexInfra_midAccum m h ts +
          halfStep (hexInfra_headAccum h ts) +
          halfStep (hexInfra_headAccum h ts + t)] := by
  induction ts generalizing m h with
  | nil => simp [midsAux]
  | cons u us ih =>
      simp only [List.cons_append, midsAux_cons, List.cons_append]
      rw [ih]
      rfl




theorem hexCyclic_verticesAux_append_single (m : ℂ) (h t : ℤ)
    (ts : List ℤ) :
    verticesAux m h (ts ++ [t]) =
      verticesAux m h ts ++
        [hexInfra_midAccum m h ts +
          halfStep (hexInfra_headAccum h ts) +
          halfStep (hexInfra_headAccum h ts + t) +
          halfStep (hexInfra_headAccum h ts + t)] := by
  induction ts generalizing m h with
  | nil => simp [verticesAux]
  | cons u us ih =>
      simp only [List.cons_append, verticesAux_cons, List.cons_append]
      rw [ih]
      rfl


noncomputable def hexCyclicNewMid (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) : ℂ :=
  hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) +
    halfStep (hexInfra_headAccum h0 ts + t)



noncomputable def hexCyclicNewVertex (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (t : ℤ) : ℂ :=
  hexCyclicNewMid a h0 ts t + halfStep (hexInfra_headAccum h0 ts + t)



theorem hexCyclic_staysIn_concat_single_iff
    (region : ℂ → Prop) (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).StaysIn region ↔
      (ofTurns a h0 ts).StaysIn region ∧
        region (hexCyclicNewMid a h0 ts t) := by
  change (∀ m, m ∈ midsAux a h0 (ts ++ [t]) → region m) ↔
    (∀ m, m ∈ midsAux a h0 ts → region m) ∧
      region (hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + t))
  rw [hexCyclic_midsAux_append_single]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro m hm
      exact h m (List.mem_append_left _ hm)
    · exact h _ (List.mem_append_right _ (by simp))
  · rintro ⟨hbase, hnew⟩ m hm
    rw [List.mem_append] at hm
    rcases hm with hm | hm
    · exact hbase m hm
    · simp only [List.mem_singleton] at hm
      subst m
      exact hnew



theorem hexCyclic_isSAW_concat_single_iff
    (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).IsSAW ↔
      (ofTurns a h0 ts).IsSAW ∧
        hexCyclicNewVertex a h0 ts t ∉ (ofTurns a h0 ts).vertices := by
  change (verticesAux a h0 (ts ++ [t])).Nodup ↔
    (verticesAux a h0 ts).Nodup ∧
      (hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + t) +
        halfStep (hexInfra_headAccum h0 ts + t)) ∉ verticesAux a h0 ts
  rw [hexCyclic_verticesAux_append_single]
  rw [List.nodup_append]
  constructor
  · rintro ⟨hbase, _, hdisj⟩
    refine ⟨hbase, ?_⟩
    intro hmem
    exact hdisj _ hmem _ (by simp) rfl
  · rintro ⟨hbase, hfresh⟩
    refine ⟨hbase, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact fun hxy => hfresh (hxy ▸ hx)


theorem hexCyclic_legalTurns_concat_single
    (a : ℂ) (h0 t : ℤ) (ts : List ℤ)
    (hbase : (ofTurns a h0 ts).LegalTurns) (ht : t = 1 ∨ t = -1) :
    (ofTurns a h0 (ts ++ [t])).LegalTurns := by
  intro u hu
  simp only [ofTurns_turns, List.mem_append, List.mem_singleton] at hu ⊢
  rcases hu with hu | rfl
  · exact hbase u hu
  · exact ht





structure HexCyclicLaunch (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (j : Fin 3) (ts : List ℤ) : Prop where
  endsAt : (ofTurns a h0 ts).EndsAt (labelMid v du j)
  lastVertex :
    labelMid v du j + halfStep (hexInfra_headAccum h0 ts) = v



theorem HexCyclicLaunch.succ_newMid
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    hexCyclicNewMid a h0 ts (-1) =
      labelMid v du (hexCyclicSucc j) := by
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  rw [hexCyclicNewMid, hend,
    show hexInfra_headAccum h0 ts + (-1) =
      hexInfra_headAccum h0 ts - 1 by ring]
  have hstep : halfStep (hexInfra_headAccum h0 ts - 1) =
      -(hexOmega * halfStep (hexInfra_headAccum h0 ts)) := by
    unfold halfStep
    have key := hexUnit_add_three (hexInfra_headAccum h0 ts - 1)
    rw [show (hexInfra_headAccum h0 ts - 1 + 3 : ℤ) =
      hexInfra_headAccum h0 ts + 2 by ring, hexUnit_add_two] at key
    linear_combination (1 / 2 : ℂ) * key
  rw [hstep, hexCyclicSucc_mid]
  linear_combination (1 - hexOmega) * L.lastVertex



theorem HexCyclicLaunch.pred_newMid
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    hexCyclicNewMid a h0 ts 1 =
      labelMid v du (hexCyclicPred j) := by
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  rw [hexCyclicNewMid, hend]
  have hstep : halfStep (hexInfra_headAccum h0 ts + 1) =
      -(hexOmega ^ 2 * halfStep (hexInfra_headAccum h0 ts)) := by
    unfold halfStep
    have key := hexUnit_add_three (hexInfra_headAccum h0 ts + 1)
    rw [show (hexInfra_headAccum h0 ts + 1 + 3 : ℤ) =
      hexInfra_headAccum h0 ts + 4 by ring, hexUnit_add_four] at key
    linear_combination (1 / 2 : ℂ) * key
  rw [hstep, hexCyclicPred_mid]
  linear_combination (1 - hexOmega ^ 2) * L.lastVertex

theorem HexCyclicLaunch.succ_endsAt
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    (ofTurns a h0 (ts ++ [-1])).EndsAt
      (labelMid v du (hexCyclicSucc j)) := by
  unfold HexWalk.EndsAt
  rw [hexInfra_endMid_eq_midAccum, hexCyclic_midAccum_append_single]
  exact L.succ_newMid

theorem HexCyclicLaunch.pred_endsAt
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts) :
    (ofTurns a h0 (ts ++ [1])).EndsAt
      (labelMid v du (hexCyclicPred j)) := by
  unfold HexWalk.EndsAt
  rw [hexInfra_endMid_eq_midAccum, hexCyclic_midAccum_append_single]
  exact L.pred_newMid





def HexCyclicLaunch.toTriplet
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn region)
    (hsuccMem : region (labelMid v du (hexCyclicSucc j)))
    (hpredMem : region (labelMid v du (hexCyclicPred j)))
    (hsuccFresh : hexCyclicNewVertex a h0 ts (-1) ∉
      (ofTurns a h0 ts).vertices)
    (hpredFresh : hexCyclicNewVertex a h0 ts 1 ∉
      (ofTurns a h0 ts).vertices) :
    HexCyclicTriplet region a h0 v du where
  baseLabel := j
  base := ts
  base_valid := ⟨hlegal, hstay, L.endsAt⟩
  succ_valid := by
    refine ⟨⟨hexCyclic_legalTurns_concat_single a h0 (-1) ts hlegal.1
      (Or.inr rfl), ?_⟩, ?_, L.succ_endsAt⟩
    · exact (hexCyclic_isSAW_concat_single_iff a h0 (-1) ts).2
        ⟨hlegal.2, hsuccFresh⟩
    · exact (hexCyclic_staysIn_concat_single_iff region a h0 (-1) ts).2
        ⟨hstay, by simpa [L.succ_newMid] using hsuccMem⟩
  pred_valid := by
    refine ⟨⟨hexCyclic_legalTurns_concat_single a h0 1 ts hlegal.1
      (Or.inl rfl), ?_⟩, ?_, L.pred_endsAt⟩
    · exact (hexCyclic_isSAW_concat_single_iff a h0 1 ts).2
        ⟨hlegal.2, hpredFresh⟩
    · exact (hexCyclic_staysIn_concat_single_iff region a h0 1 ts).2
        ⟨hstay, by simpa [L.pred_newMid] using hpredMem⟩





def hexVisitClassFinset (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (k : ℕ) : Finset (List ℤ) :=
  (R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu).filter
    (fun ts => specialMidCount a h0 v du ts = k)

@[simp] theorem mem_hexVisitClassFinset (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) (k : ℕ)
    (ts : List ℤ) :
    ts ∈ hexVisitClassFinset R a h0 v du hdu k ↔
      ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧
        specialMidCount a h0 v du ts = k := by
  simp [hexVisitClassFinset]



theorem specialMidCount_le_three (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ) : specialMidCount a h0 v du ts ≤ 3 := by
  classical
  unfold specialMidCount
  split <;> split <;> split <;> omega



theorem support_specialMidCount_pos
    (ts : List ℤ)
    (hts : ts ∈ Function.support (combinedSummand region a h0 v du)) :
    0 < specialMidCount a h0 v du ts := by
  classical
  rcases support_endsAt_threeMid ts hts with hp | hq | hr
  · have hpass := hexClass_endsAt_passesThrough ts (v + du) hp
    unfold specialMidCount
    rw [if_pos hpass]
    split <;> split <;> omega
  · have hpass := hexClass_endsAt_passesThrough ts
      (v + hexOmega * du) hq
    unfold specialMidCount
    rw [if_pos hpass]
    split <;> split <;> omega
  · have hpass := hexClass_endsAt_passesThrough ts
      (v + hexOmega ^ 2 * du) hr
    unfold specialMidCount
    rw [if_pos hpass]
    split <;> split <;> omega



theorem support_specialMidCount_cases
    (ts : List ℤ)
    (hts : ts ∈ Function.support (combinedSummand region a h0 v du)) :
    specialMidCount a h0 v du ts = 1 ∨
      specialMidCount a h0 v du ts = 2 ∨
      specialMidCount a h0 v du ts = 3 := by
  have hlo := support_specialMidCount_pos ts hts
  have hhi := specialMidCount_le_three a h0 v du ts
  omega


theorem supportFinset_eq_visitClasses (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) :
    R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu =
      hexVisitClassFinset R a h0 v du hdu 1 ∪
        hexVisitClassFinset R a h0 v du hdu 2 ∪
        hexVisitClassFinset R a h0 v du hdu 3 := by
  ext ts
  constructor
  · intro hts
    have hsupp := (R.mem_supportFinset hdu ts).mp hts
    rcases support_specialMidCount_cases ts hsupp with h1 | h2 | h3
    · simp [mem_hexVisitClassFinset, hts, h1]
    · simp [mem_hexVisitClassFinset, hts, h2]
    · simp [mem_hexVisitClassFinset, hts, h3]
  · intro hts
    simp only [Finset.mem_union, mem_hexVisitClassFinset] at hts
    rcases hts with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h


theorem hexVisitClassFinset_disjoint (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (hexVisitClassFinset R a h0 v du hdu k)
      (hexVisitClassFinset R a h0 v du hdu l) := by
  rw [Finset.disjoint_left]
  intro ts hk hl
  have hk' := (mem_hexVisitClassFinset R a h0 v du hdu k ts).mp hk
  have hl' := (mem_hexVisitClassFinset R a h0 v du hdu l ts).mp hl
  exact hkl (hk'.2.symm.trans hl'.2)



def hexDecodedTurns (n : ℕ) : List ℤ :=
  (Encodable.decode n : Option (List ℤ)).getD []

@[simp] theorem hexDecodedTurns_encode (ts : List ℤ) :
    hexDecodedTurns (Encodable.encode ts) = ts := by
  rw [hexDecodedTurns, Encodable.encodek]
  rfl






noncomputable def hexKOneBaseTurns (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) : Finset (List ℤ) := by
  classical
  exact
    (R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu).filter
      (fun ts => specialMidCount a h0 v du ts = 1 ∧
        (ofTurns a h0 ts).EndsAt (labelMid v du j))

@[simp] theorem mem_hexKOneBaseTurns (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3)
    (ts : List ℤ) :
    ts ∈ hexKOneBaseTurns R a h0 v du hdu j ↔
      ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧
        specialMidCount a h0 v du ts = 1 ∧
        (ofTurns a h0 ts).EndsAt (labelMid v du j) := by
  classical
  simp [hexKOneBaseTurns]


def hexKOneBaseIndices (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) : Finset ℕ :=
  (hexKOneBaseTurns R a h0 v du hdu j).image Encodable.encode



theorem hexKOneBase_valid (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) (n : ℕ)
    (hn : n ∈ hexKOneBaseIndices R a h0 v du hdu j) :
    (ofTurns a h0 (hexDecodedTurns n)).IsLegalSAW ∧
      (ofTurns a h0 (hexDecodedTurns n)).StaysIn R.inRegion ∧
      (ofTurns a h0 (hexDecodedTurns n)).EndsAt (labelMid v du j) ∧
      specialMidCount a h0 v du (hexDecodedTurns n) = 1 := by
  rw [hexKOneBaseIndices, Finset.mem_image] at hn
  obtain ⟨ts, hts, rfl⟩ := hn
  have hparts := (mem_hexKOneBaseTurns R a h0 v du hdu j ts).mp hts
  have hsupp := (R.mem_supportFinset hdu ts).mp hparts.1
  have hvalid := R.support_isLegalSAW_staysIn hdu ts hsupp
  simpa using ⟨hvalid.1, hvalid.2, hparts.2.2, hparts.2.1⟩


theorem hexKOneBase_injective (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) :
    ∀ n₁ n₂ : hexKOneBaseIndices R a h0 v du hdu j,
      hexDecodedTurns n₁ = hexDecodedTurns n₂ → n₁ = n₂ := by
  rintro ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ heq
  rw [hexKOneBaseIndices, Finset.mem_image] at hn₁ hn₂
  obtain ⟨ts₁, _, rfl⟩ := hn₁
  obtain ⟨ts₂, _, rfl⟩ := hn₂
  simp only [hexDecodedTurns_encode] at heq
  subst ts₂
  rfl



theorem hexKOneBase_classify (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (j : Fin 3) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      specialMidCount a h0 v du ts = 1 →
      (ofTurns a h0 ts).EndsAt (labelMid v du j) →
      ∃ n : ℕ, n ∈ hexKOneBaseIndices R a h0 v du hdu j ∧
        hexDecodedTurns n = ts := by
  intro ts hts hcount hend
  refine ⟨Encodable.encode ts, ?_, hexDecodedTurns_encode ts⟩
  rw [hexKOneBaseIndices, Finset.mem_image]
  refine ⟨ts, ?_, rfl⟩
  exact (mem_hexKOneBaseTurns R a h0 v du hdu j ts).mpr
    ⟨(R.mem_supportFinset hdu ts).mpr hts, hcount, hend⟩




theorem hexVisitClass_one_eq_cyclicBases (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0) :
    hexVisitClassFinset R a h0 v du hdu 1 =
      hexKOneBaseTurns R a h0 v du hdu 0 ∪
        hexKOneBaseTurns R a h0 v du hdu 1 ∪
        hexKOneBaseTurns R a h0 v du hdu 2 := by
  ext ts
  constructor
  · intro hts
    have hparts :=
      (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mp hts
    have hsupp := (R.mem_supportFinset hdu ts).mp hparts.1
    rcases support_endsAt_threeMid ts hsupp with hp | hq | hr
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact (mem_hexKOneBaseTurns R a h0 v du hdu 0 ts).mpr
        ⟨hparts.1, hparts.2, by simpa [labelMid] using hp⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact (mem_hexKOneBaseTurns R a h0 v du hdu 1 ts).mpr
        ⟨hparts.1, hparts.2, by simpa [labelMid] using hq⟩
    · apply Finset.mem_union_right
      exact (mem_hexKOneBaseTurns R a h0 v du hdu 2 ts).mpr
        ⟨hparts.1, hparts.2, by simpa [labelMid] using hr⟩
  · intro hts
    rcases Finset.mem_union.mp hts with h01 | hb2
    · rcases Finset.mem_union.mp h01 with hb0 | hb1
      · have h := (mem_hexKOneBaseTurns R a h0 v du hdu 0 ts).mp hb0
        exact (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mpr
          ⟨h.1, h.2.1⟩
      · have h := (mem_hexKOneBaseTurns R a h0 v du hdu 1 ts).mp hb1
        exact (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mpr
          ⟨h.1, h.2.1⟩
    · have h := (mem_hexKOneBaseTurns R a h0 v du hdu 2 ts).mp hb2
      exact (mem_hexVisitClassFinset R a h0 v du hdu 1 ts).mpr
        ⟨h.1, h.2.1⟩


theorem hexKOneBaseTurns_disjoint (R : HexFiniteRegion)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (hdu : du ≠ 0)
    {j k : Fin 3} (hjk : j ≠ k) :
    Disjoint (hexKOneBaseTurns R a h0 v du hdu j)
      (hexKOneBaseTurns R a h0 v du hdu k) := by
  rw [Finset.disjoint_left]
  intro ts hj hk
  have hj' := (mem_hexKOneBaseTurns R a h0 v du hdu j ts).mp hj
  have hk' := (mem_hexKOneBaseTurns R a h0 v du hdu k ts).mp hk
  apply hjk
  apply labelMid_injective hdu
  unfold HexWalk.EndsAt at hj' hk'
  exact hj'.2.2.symm.trans hk'.2.2




noncomputable def hexPBaseTurns (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) : Finset (List ℤ) := by
  classical
  exact
    (R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu).filter
      (fun ts => (ofTurns a h0 ts).EndsAt (v + du))


def hexPBaseIndices (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) : Finset ℕ :=
  (hexPBaseTurns R a h0 v du hdu).image Encodable.encode



theorem hexPBase_valid (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) (n : ℕ)
    (hn : n ∈ hexPBaseIndices R a h0 v du hdu) :
    (ofTurns a h0 (hexDecodedTurns n)).IsLegalSAW ∧
      (ofTurns a h0 (hexDecodedTurns n)).StaysIn R.inRegion ∧
      (ofTurns a h0 (hexDecodedTurns n)).EndsAt (v + du) := by
  rw [hexPBaseIndices, Finset.mem_image] at hn
  obtain ⟨ts, hts, rfl⟩ := hn
  have hparts :
      ts ∈ R.supportFinset (a := a) (h0 := h0) (v := v) (du := du) hdu ∧
        (ofTurns a h0 ts).EndsAt (v + du) := by
    simpa [hexPBaseTurns] using hts
  have hsupp := (R.mem_supportFinset hdu ts).mp hparts.1
  have hvalid := R.support_isLegalSAW_staysIn hdu ts hsupp
  simpa using ⟨hvalid.1, hvalid.2, hparts.2⟩



theorem hexPBase_injective (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) :
    ∀ n₁ n₂ : hexPBaseIndices R a h0 v du hdu,
      hexDecodedTurns n₁ = hexDecodedTurns n₂ → n₁ = n₂ := by
  rintro ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ heq
  rw [hexPBaseIndices, Finset.mem_image] at hn₁ hn₂
  obtain ⟨ts₁, _, rfl⟩ := hn₁
  obtain ⟨ts₂, _, rfl⟩ := hn₂
  simp only [hexDecodedTurns_encode] at heq
  subst ts₂
  rfl



theorem hexPBase_classify (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ)
    (v du : ℂ) (hdu : du ≠ 0) :
    ∀ ts ∈ Function.support (combinedSummand R.inRegion a h0 v du),
      (ofTurns a h0 ts).EndsAt (v + du) →
      ∃ n : ℕ, n ∈ hexPBaseIndices R a h0 v du hdu ∧
        hexDecodedTurns n = ts := by
  intro ts hts hend
  refine ⟨Encodable.encode ts, ?_, hexDecodedTurns_encode ts⟩
  rw [hexPBaseIndices, Finset.mem_image]
  refine ⟨ts, ?_, rfl⟩
  simp only [hexPBaseTurns, Finset.mem_filter]
  exact ⟨(R.mem_supportFinset hdu ts).mpr hts, hend⟩








theorem no_fixedP_classification_of_nil_at_q
    (hsupp : ([] : List ℤ) ∈
      Function.support (combinedSummand region a h0 v du))
    (hend : (ofTurns a h0 ([] : List ℤ)).EndsAt
      (v + hexOmega * du)) :
    ¬ Nonempty (HexSawClassification region a h0 v du) := by
  rintro ⟨C⟩
  rcases C.classify_q [] hsupp hend with
    ⟨T, hT, hwalk⟩ | ⟨P, hP, hwalk⟩
  · have hlen := congrArg List.length hwalk
    simp at hlen
  · have hnil : C.pairLq P = [] := by
      have hlen := congrArg List.length hwalk
      simp only [List.length_append, List.length_nil] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hsum := C.pairLq_sum P hP
    rw [hnil] at hsum
    norm_num at hsum

end

end StatMech.Universality
