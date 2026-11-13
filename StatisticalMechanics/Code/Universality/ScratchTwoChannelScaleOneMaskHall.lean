/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding

namespace StatMech.Universality



abbrev RlcScaleOneSectionA := Fin 15 → Bool
abbrev RlcScaleOneSectionB := Fin 13 → Bool
abbrev RlcScaleOneSectionC := Fin 12 → Bool

abbrev RlcScaleOnePairBlock := Fin 2 → Bool
abbrev RlcScaleOneFiveBlock := Fin 5 → Bool
abbrev RlcScaleOneUnusedBlock := Fin 3 → Bool

def rlcScaleOnePairBlockAvoidsRoute (w : RlcScaleOnePairBlock) : Bool :=
  !(w 0 && w 1)

def rlcScaleOneFiveBlockAvoidsRoutes (w : RlcScaleOneFiveBlock) : Bool :=
  !(w 4 && w 0 && w 1) && !(w 4 && w 2 && w 3)

abbrev RlcScaleOnePairBlockFailure :=
  {w : RlcScaleOnePairBlock // rlcScaleOnePairBlockAvoidsRoute w = true}

abbrev RlcScaleOneFiveBlockFailure :=
  {w : RlcScaleOneFiveBlock // rlcScaleOneFiveBlockAvoidsRoutes w = true}

abbrev RlcScaleOneSectionAFactors :=
  RlcScaleOnePairBlockFailure × RlcScaleOneFiveBlockFailure ×
    RlcScaleOneFiveBlockFailure × RlcScaleOneUnusedBlock

def rlcScaleOneSectionAAvoidsSelectedRoutes (w : RlcScaleOneSectionA) : Bool :=
  rlcScaleOnePairBlockAvoidsRoute ![w 6, w 7] &&
  rlcScaleOneFiveBlockAvoidsRoutes ![w 0, w 1, w 2, w 3, w 4] &&
  rlcScaleOneFiveBlockAvoidsRoutes ![w 10, w 11, w 13, w 14, w 9]

def rlcScaleOneSectionBAvoidsSelectedRoutes (w : RlcScaleOneSectionB) : Bool :=
  !(w 0 && w 1 && w 4) &&
  !(w 6 && w 7 && w 10) &&
  !(w 8 && w 11 && w 12) &&
  !(w 2 && w 3 && w 4) &&
  !(w 8 && w 9 && w 10) &&
  !(w 5 && w 7 && w 10) &&
  !(w 3 && w 4 && w 5)

def rlcScaleOneSectionCAvoidsSelectedRoutes (w : RlcScaleOneSectionC) : Bool :=
  !(w 7 && w 8) &&
  !(w 0 && w 1 && w 4) &&
  !(w 2 && w 3 && w 4) &&
  !(w 7 && w 10 && w 11) &&
  !(w 3 && w 4 && w 5) &&
  !(w 3 && w 4 && w 6)

abbrev RlcScaleOneSectionAFailure :=
  {w : RlcScaleOneSectionA // rlcScaleOneSectionAAvoidsSelectedRoutes w = true}

abbrev RlcScaleOneSectionBFailure :=
  {w : RlcScaleOneSectionB // rlcScaleOneSectionBAvoidsSelectedRoutes w = true}

abbrev RlcScaleOneSectionCFailure :=
  {w : RlcScaleOneSectionC // rlcScaleOneSectionCAvoidsSelectedRoutes w = true}

def rlcScaleOneSectionAFactorEquiv :
    Equiv RlcScaleOneSectionAFailure RlcScaleOneSectionAFactors where
  toFun w :=
    (⟨![w.1 6, w.1 7], by
      simpa [rlcScaleOneSectionAAvoidsSelectedRoutes] using
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp w.2).1).1⟩,
    ⟨![w.1 0, w.1 1, w.1 2, w.1 3, w.1 4], by
      simpa [rlcScaleOneSectionAAvoidsSelectedRoutes] using
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp w.2).1).2⟩,
    ⟨![w.1 10, w.1 11, w.1 13, w.1 14, w.1 9], by
      simpa [rlcScaleOneSectionAAvoidsSelectedRoutes] using
        (Bool.and_eq_true_iff.mp w.2).2⟩,
    ![w.1 5, w.1 8, w.1 12])
  invFun blocks :=
    ⟨![blocks.2.1.1 0, blocks.2.1.1 1, blocks.2.1.1 2,
        blocks.2.1.1 3, blocks.2.1.1 4, blocks.2.2.2 0,
        blocks.1.1 0, blocks.1.1 1, blocks.2.2.2 1,
        blocks.2.2.1.1 4, blocks.2.2.1.1 0, blocks.2.2.1.1 1,
        blocks.2.2.2 2, blocks.2.2.1.1 2, blocks.2.2.1.1 3], by
      change (rlcScaleOnePairBlockAvoidsRoute blocks.1.1 &&
        rlcScaleOneFiveBlockAvoidsRoutes blocks.2.1.1 &&
        rlcScaleOneFiveBlockAvoidsRoutes blocks.2.2.1.1) = true
      rw [blocks.1.2, blocks.2.1.2, blocks.2.2.1.2]
      decide⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv blocks := by
    rcases blocks with ⟨pair, left, right, unused⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      · apply Prod.ext
        · apply Subtype.ext
          funext i
          fin_cases i <;> rfl
        · funext i
          fin_cases i <;> rfl

theorem rlcScaleOnePairBlockFailure_card :
    Fintype.card RlcScaleOnePairBlockFailure = 3 := by
  decide

theorem rlcScaleOneFiveBlockFailure_card :
    Fintype.card RlcScaleOneFiveBlockFailure = 25 := by
  decide

theorem rlcScaleOneSectionAFailure_card :
    Fintype.card RlcScaleOneSectionAFailure = 15000 := by
  rw [Fintype.card_congr rlcScaleOneSectionAFactorEquiv]
  simp only [RlcScaleOneSectionAFactors, Fintype.card_prod,
    rlcScaleOnePairBlockFailure_card, rlcScaleOneFiveBlockFailure_card,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem rlcScaleOneSectionBFailure_card :
    Fintype.card RlcScaleOneSectionBFailure = 3941 := by
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem rlcScaleOneSectionCFailure_card :
    Fintype.card RlcScaleOneSectionCFailure = 2002 := by
  decide

noncomputable def rlcScaleOneSectionBList : List RlcScaleOneSectionB :=
  (Finset.univ.filter fun w =>
    rlcScaleOneSectionBAvoidsSelectedRoutes w = true).toList

noncomputable def rlcScaleOneSectionCList : List RlcScaleOneSectionC :=
  (Finset.univ.filter fun w =>
    rlcScaleOneSectionCAvoidsSelectedRoutes w = true).toList

theorem rlcScaleOneSectionBList_mem (w : RlcScaleOneSectionB) :
    w ∈ rlcScaleOneSectionBList ↔
      rlcScaleOneSectionBAvoidsSelectedRoutes w = true := by
  rw [rlcScaleOneSectionBList, Finset.mem_toList, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem rlcScaleOneSectionCList_mem (w : RlcScaleOneSectionC) :
    w ∈ rlcScaleOneSectionCList ↔
      rlcScaleOneSectionCAvoidsSelectedRoutes w = true := by
  rw [rlcScaleOneSectionCList, Finset.mem_toList, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

noncomputable def rlcScaleOneSectionBListEquiv :
    Equiv (Fin rlcScaleOneSectionBList.length) RlcScaleOneSectionBFailure :=
  ((Finset.nodup_toList _).getEquiv _).trans
    { toFun := fun w => ⟨w.1, (rlcScaleOneSectionBList_mem w.1).mp w.2⟩
      invFun := fun w => ⟨w.1, (rlcScaleOneSectionBList_mem w.1).mpr w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def rlcScaleOneSectionCListEquiv :
    Equiv (Fin rlcScaleOneSectionCList.length) RlcScaleOneSectionCFailure :=
  ((Finset.nodup_toList _).getEquiv _).trans
    { toFun := fun w => ⟨w.1, (rlcScaleOneSectionCList_mem w.1).mp w.2⟩
      invFun := fun w => ⟨w.1, (rlcScaleOneSectionCList_mem w.1).mpr w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rlcScaleOneSectionBList_length :
    rlcScaleOneSectionBList.length = 3941 := by
  unfold rlcScaleOneSectionBList
  rw [Finset.length_toList]
  exact rlcScaleOneSectionBFailure_card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rlcScaleOneSectionCList_length :
    rlcScaleOneSectionCList.length = 2002 := by
  unfold rlcScaleOneSectionCList
  rw [Finset.length_toList]
  exact rlcScaleOneSectionCFailure_card

noncomputable def rlcScaleOnePairBlockEquivFin :
    Equiv RlcScaleOnePairBlockFailure (Fin 3) :=
  Fintype.equivFinOfCardEq rlcScaleOnePairBlockFailure_card

noncomputable def rlcScaleOneFiveBlockEquivFin :
    Equiv RlcScaleOneFiveBlockFailure (Fin 25) :=
  Fintype.equivFinOfCardEq rlcScaleOneFiveBlockFailure_card

noncomputable def rlcScaleOneUnusedBlockEquivFin :
    Equiv RlcScaleOneUnusedBlock (Fin 8) :=
  Fintype.equivFinOfCardEq (by
    simp only [RlcScaleOneUnusedBlock, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
    norm_num)

noncomputable def rlcScaleOneSectionAFactorsEquivFin :
    Equiv RlcScaleOneSectionAFactors (Fin 15000) :=
  (Equiv.prodCongr rlcScaleOnePairBlockEquivFin
    (Equiv.prodCongr rlcScaleOneFiveBlockEquivFin
      (Equiv.prodCongr rlcScaleOneFiveBlockEquivFin
        rlcScaleOneUnusedBlockEquivFin))).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 3))
      ((Equiv.prodCongr (Equiv.refl (Fin 25)) finProdFinEquiv).trans
        finProdFinEquiv)).trans finProdFinEquiv)

noncomputable def rlcScaleOneSectionAEncoder :
    RlcScaleOneSectionAFailure ↪ Fin (2 ^ 14) :=
  (rlcScaleOneSectionAFactorEquiv.trans
    rlcScaleOneSectionAFactorsEquivFin).toEmbedding.trans
      (Fin.castLEEmb (by norm_num))

noncomputable def rlcScaleOneSectionBEncoder :
    RlcScaleOneSectionBFailure ↪ Fin (2 ^ 12) :=
  rlcScaleOneSectionBListEquiv.symm.toEmbedding |>.trans
    (Fin.castLEEmb (by rw [rlcScaleOneSectionBList_length]; norm_num))

noncomputable def rlcScaleOneSectionCEncoder :
    RlcScaleOneSectionCFailure ↪ Fin (2 ^ 11) :=
  rlcScaleOneSectionCListEquiv.symm.toEmbedding |>.trans
    (Fin.castLEEmb (by rw [rlcScaleOneSectionCList_length]; norm_num))

abbrev RlcScaleOneEdgeConfig := Fin 16 → Bool

def rlcScaleOneRouteClass (omega : RlcScaleOneEdgeConfig) : Fin 4 :=
  if omega 6 = false then 0
  else if omega 11 = false ∧ omega 7 = false then 1
  else if omega 9 = false ∧ omega 7 = false then 2
  else 3

def rlcScaleOneRestrictA (omega : RlcScaleOneEdgeConfig) :
    RlcScaleOneSectionA :=
  ![omega 0, omega 1, omega 2, omega 3, omega 4, omega 5,
    omega 7, omega 8, omega 9, omega 10, omega 11, omega 12,
    omega 13, omega 14, omega 15]

def rlcScaleOneRestrictB (omega : RlcScaleOneEdgeConfig) :
    RlcScaleOneSectionB :=
  ![omega 0, omega 1, omega 2, omega 3, omega 4, omega 5,
    omega 8, omega 9, omega 10, omega 12, omega 13, omega 14,
    omega 15]

def rlcScaleOneRestrictC (omega : RlcScaleOneEdgeConfig) :
    RlcScaleOneSectionC :=
  ![omega 0, omega 1, omega 2, omega 3, omega 4, omega 5,
    omega 8, omega 10, omega 12, omega 13, omega 14, omega 15]

def rlcScaleOneRestrictD (omega : RlcScaleOneEdgeConfig) : Fin 12 → Bool :=
  ![omega 0, omega 1, omega 3, omega 4, omega 7, omega 9,
    omega 10, omega 11, omega 12, omega 13, omega 14, omega 15]

abbrev RlcScaleOneFiberA :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 0 ∧
      rlcScaleOneSectionAAvoidsSelectedRoutes
        (rlcScaleOneRestrictA omega) = true}

abbrev RlcScaleOneFiberB :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 1 ∧
      rlcScaleOneSectionBAvoidsSelectedRoutes
        (rlcScaleOneRestrictB omega) = true}

abbrev RlcScaleOneFiberC :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 2 ∧
      rlcScaleOneSectionCAvoidsSelectedRoutes
        (rlcScaleOneRestrictC omega) = true}

abbrev RlcScaleOneFiberD :=
  {omega : RlcScaleOneEdgeConfig //
    rlcScaleOneRouteClass omega = 3 ∧ omega 2 = false ∧
      omega 5 = false ∧ omega 6 = true ∧ omega 8 = false}

theorem rlcScaleOneRouteClass_zero_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 0) : omega 6 = false := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

theorem rlcScaleOneRouteClass_one_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 1) :
    omega 6 = true ∧ omega 11 = false ∧ omega 7 = false := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

theorem rlcScaleOneRouteClass_two_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 2) :
    omega 6 = true ∧ omega 11 = true ∧ omega 7 = false ∧
      omega 9 = false := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

theorem rlcScaleOneRouteClass_three_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 3) :
    omega 6 = true ∧ (omega 11 = true ∨ omega 7 = true) ∧
      (omega 9 = true ∨ omega 7 = true) := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

def rlcScaleOneFiberARestrict :
    RlcScaleOneFiberA ↪ RlcScaleOneSectionAFailure where
  toFun omega := ⟨rlcScaleOneRestrictA omega.1, omega.2.2⟩
  inj' omega omega' h := by
    apply Subtype.ext
    have hfun : rlcScaleOneRestrictA omega.1 =
        rlcScaleOneRestrictA omega'.1 := congrArg Subtype.val h
    have h6 := rlcScaleOneRouteClass_zero_fixed omega.1 omega.2.1
    have h6' := rlcScaleOneRouteClass_zero_fixed omega'.1 omega'.2.1
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictA]

def rlcScaleOneFiberBRestrict :
    RlcScaleOneFiberB ↪ RlcScaleOneSectionBFailure where
  toFun omega := ⟨rlcScaleOneRestrictB omega.1, omega.2.2⟩
  inj' omega omega' h := by
    apply Subtype.ext
    have hfun : rlcScaleOneRestrictB omega.1 =
        rlcScaleOneRestrictB omega'.1 := congrArg Subtype.val h
    have hfix := rlcScaleOneRouteClass_one_fixed omega.1 omega.2.1
    have hfix' := rlcScaleOneRouteClass_one_fixed omega'.1 omega'.2.1
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictB]

def rlcScaleOneFiberCRestrict :
    RlcScaleOneFiberC ↪ RlcScaleOneSectionCFailure where
  toFun omega := ⟨rlcScaleOneRestrictC omega.1, omega.2.2⟩
  inj' omega omega' h := by
    apply Subtype.ext
    have hfun : rlcScaleOneRestrictC omega.1 =
        rlcScaleOneRestrictC omega'.1 := congrArg Subtype.val h
    have hfix := rlcScaleOneRouteClass_two_fixed omega.1 omega.2.1
    have hfix' := rlcScaleOneRouteClass_two_fixed omega'.1 omega'.2.1
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictC]

def rlcScaleOneFiberDRestrict :
    RlcScaleOneFiberD ↪ (Fin 12 → Bool) where
  toFun omega := rlcScaleOneRestrictD omega.1
  inj' omega omega' h := by
    apply Subtype.ext
    have h2 := omega.2.2.1
    have h5 := omega.2.2.2.1
    have h6 := omega.2.2.2.2.1
    have h8 := omega.2.2.2.2.2
    have h2' := omega'.2.2.1
    have h5' := omega'.2.2.2.1
    have h6' := omega'.2.2.2.2.1
    have h8' := omega'.2.2.2.2.2
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictD]

def rlcScaleOneBoolCubeToBitVec : (n : Nat) → (Fin n → Bool) → BitVec n
  | 0, _ => BitVec.nil
  | n + 1, bits =>
      BitVec.concat (rlcScaleOneBoolCubeToBitVec n (Fin.tail bits)) (bits 0)

@[simp] theorem rlcScaleOneBoolCubeToBitVec_getLsb
    {n : Nat} (bits : Fin n → Bool) (i : Fin n) :
    (rlcScaleOneBoolCubeToBitVec n bits).getLsb i = bits i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [rlcScaleOneBoolCubeToBitVec]
      · change
          (BitVec.concat (rlcScaleOneBoolCubeToBitVec n (Fin.tail bits))
            (bits 0)).getLsbD (j.val + 1) = bits j.succ
        rw [BitVec.getLsbD_concat_succ]
        simpa [Fin.tail] using ih (Fin.tail bits) j

def rlcScaleOneFinPowTwoEquivBoolCube (n : Nat) :
    Equiv (Fin (2 ^ n)) (Fin n → Bool) :=
  BitVec.equivFin.symm.toEquiv.trans
    { toFun := fun bits => bits.getLsb
      invFun := rlcScaleOneBoolCubeToBitVec n
      left_inv := fun bits => by
        apply BitVec.eq_of_getElem_eq
        intro i hi
        simpa using rlcScaleOneBoolCubeToBitVec_getLsb
          (fun j : Fin n => bits.getLsb j) ⟨i, hi⟩
      right_inv := fun bits => by
        funext i
        exact rlcScaleOneBoolCubeToBitVec_getLsb bits i }

noncomputable def rlcScaleOneFiberAPayload :
    RlcScaleOneFiberA ↪ (Fin 14 → Bool) :=
  (rlcScaleOneFiberARestrict.trans rlcScaleOneSectionAEncoder).trans
    (rlcScaleOneFinPowTwoEquivBoolCube 14).toEmbedding

noncomputable def rlcScaleOneFiberBPayload :
    RlcScaleOneFiberB ↪ (Fin 12 → Bool) :=
  (rlcScaleOneFiberBRestrict.trans rlcScaleOneSectionBEncoder).trans
    (rlcScaleOneFinPowTwoEquivBoolCube 12).toEmbedding

noncomputable def rlcScaleOneFiberCPayload :
    RlcScaleOneFiberC ↪ (Fin 11 → Bool) :=
  (rlcScaleOneFiberCRestrict.trans rlcScaleOneSectionCEncoder).trans
    (rlcScaleOneFinPowTwoEquivBoolCube 11).toEmbedding

def rlcScaleOneCodeA (payload : Fin 14 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, payload 2, payload 3, payload 4, payload 5,
    payload 6, true, true, payload 7, payload 8, payload 9,
    payload 10, payload 11, payload 12, payload 13]

def rlcScaleOneCodeB (payload : Fin 12 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, true, payload 2, payload 3, payload 4,
    true, true, false, payload 5, payload 6, payload 7,
    payload 8, payload 9, payload 10, payload 11]

def rlcScaleOneCodeC (payload : Fin 11 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, false, payload 2, payload 3, true,
    true, true, false, payload 4, payload 5, payload 6,
    payload 7, payload 8, payload 9, payload 10]

def rlcScaleOneCodeD (payload : Fin 12 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, payload 2, payload 3, payload 4, payload 5,
    payload 6, false, payload 7, payload 8, true, true,
    true, payload 9, payload 10, payload 11]

def rlcScaleOneCodeAEmbedding :
    (Fin 14 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeA
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeA]

def rlcScaleOneCodeBEmbedding :
    (Fin 12 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeB
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeB]

def rlcScaleOneCodeCEmbedding :
    (Fin 11 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeC
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeC]

def rlcScaleOneCodeDEmbedding :
    (Fin 12 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeD
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeD]

noncomputable def rlcScaleOneFiberATarget :
    RlcScaleOneFiberA ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberAPayload.trans rlcScaleOneCodeAEmbedding

noncomputable def rlcScaleOneFiberBTarget :
    RlcScaleOneFiberB ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberBPayload.trans rlcScaleOneCodeBEmbedding

noncomputable def rlcScaleOneFiberCTarget :
    RlcScaleOneFiberC ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberCPayload.trans rlcScaleOneCodeCEmbedding

def rlcScaleOneFiberDTarget :
    RlcScaleOneFiberD ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberDRestrict.trans rlcScaleOneCodeDEmbedding

theorem rlcScaleOneCodeA_ne_codeB (a : Fin 14 → Bool)
    (b : Fin 12 → Bool) : rlcScaleOneCodeA a ≠ rlcScaleOneCodeB b := by
  intro h
  have h8 := congrFun h (8 : Fin 16)
  simp [rlcScaleOneCodeA, rlcScaleOneCodeB] at h8

theorem rlcScaleOneCodeA_ne_codeC (a : Fin 14 → Bool)
    (c : Fin 11 → Bool) : rlcScaleOneCodeA a ≠ rlcScaleOneCodeC c := by
  intro h
  have h8 := congrFun h (8 : Fin 16)
  simp [rlcScaleOneCodeA, rlcScaleOneCodeC] at h8

theorem rlcScaleOneCodeA_ne_codeD (a : Fin 14 → Bool)
    (d : Fin 12 → Bool) : rlcScaleOneCodeA a ≠ rlcScaleOneCodeD d := by
  intro h
  have h7 := congrFun h (7 : Fin 16)
  simp [rlcScaleOneCodeA, rlcScaleOneCodeD] at h7

theorem rlcScaleOneCodeB_ne_codeC (b : Fin 12 → Bool)
    (c : Fin 11 → Bool) : rlcScaleOneCodeB b ≠ rlcScaleOneCodeC c := by
  intro h
  have h2 := congrFun h (2 : Fin 16)
  simp [rlcScaleOneCodeB, rlcScaleOneCodeC] at h2

theorem rlcScaleOneCodeB_ne_codeD (b d : Fin 12 → Bool) :
    rlcScaleOneCodeB b ≠ rlcScaleOneCodeD d := by
  intro h
  have h7 := congrFun h (7 : Fin 16)
  simp [rlcScaleOneCodeB, rlcScaleOneCodeD] at h7

theorem rlcScaleOneCodeC_ne_codeD (c : Fin 11 → Bool)
    (d : Fin 12 → Bool) : rlcScaleOneCodeC c ≠ rlcScaleOneCodeD d := by
  intro h
  have h7 := congrFun h (7 : Fin 16)
  simp [rlcScaleOneCodeC, rlcScaleOneCodeD] at h7

abbrev RlcScaleOneRoutedFailure :=
  RlcScaleOneFiberA ⊕ (RlcScaleOneFiberB ⊕
    (RlcScaleOneFiberC ⊕ RlcScaleOneFiberD))

noncomputable def rlcScaleOneTaggedTarget
    (rho : RlcScaleOneRoutedFailure) : RlcScaleOneEdgeConfig :=
  match rho with
  | Sum.inl a => rlcScaleOneFiberATarget a
  | Sum.inr (Sum.inl b) => rlcScaleOneFiberBTarget b
  | Sum.inr (Sum.inr (Sum.inl c)) => rlcScaleOneFiberCTarget c
  | Sum.inr (Sum.inr (Sum.inr d)) => rlcScaleOneFiberDTarget d

noncomputable def rlcScaleOneTaggedTargetEmbedding :
    RlcScaleOneRoutedFailure ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneTaggedTarget
  inj' rho rho' h := by
    rcases rho with a | bcd
    · rcases rho' with a' | bcd'
      · exact congrArg Sum.inl (rlcScaleOneFiberATarget.injective h)
      · rcases bcd' with b' | cd'
        · exact (rlcScaleOneCodeA_ne_codeB
            (rlcScaleOneFiberAPayload a)
            (rlcScaleOneFiberBPayload b') h).elim
        · rcases cd' with c' | d'
          · exact (rlcScaleOneCodeA_ne_codeC
              (rlcScaleOneFiberAPayload a)
              (rlcScaleOneFiberCPayload c') h).elim
          · exact (rlcScaleOneCodeA_ne_codeD
              (rlcScaleOneFiberAPayload a)
              (rlcScaleOneFiberDRestrict d') h).elim
    · rcases bcd with b | cd
      · rcases rho' with a' | bcd'
        · exact (rlcScaleOneCodeA_ne_codeB
            (rlcScaleOneFiberAPayload a')
            (rlcScaleOneFiberBPayload b) h.symm).elim
        · rcases bcd' with b' | cd'
          · exact congrArg (fun z => Sum.inr (Sum.inl z))
              (rlcScaleOneFiberBTarget.injective h)
          · rcases cd' with c' | d'
            · exact (rlcScaleOneCodeB_ne_codeC
                (rlcScaleOneFiberBPayload b)
                (rlcScaleOneFiberCPayload c') h).elim
            · exact (rlcScaleOneCodeB_ne_codeD
                (rlcScaleOneFiberBPayload b)
                (rlcScaleOneFiberDRestrict d') h).elim
      · rcases cd with c | d
        · rcases rho' with a' | bcd'
          · exact (rlcScaleOneCodeA_ne_codeC
              (rlcScaleOneFiberAPayload a')
              (rlcScaleOneFiberCPayload c) h.symm).elim
          · rcases bcd' with b' | cd'
            · exact (rlcScaleOneCodeB_ne_codeC
                (rlcScaleOneFiberBPayload b')
                (rlcScaleOneFiberCPayload c) h.symm).elim
            · rcases cd' with c' | d'
              · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z)))
                  (rlcScaleOneFiberCTarget.injective h)
              · exact (rlcScaleOneCodeC_ne_codeD
                  (rlcScaleOneFiberCPayload c)
                  (rlcScaleOneFiberDRestrict d') h).elim
        · rcases rho' with a' | bcd'
          · exact (rlcScaleOneCodeA_ne_codeD
              (rlcScaleOneFiberAPayload a')
              (rlcScaleOneFiberDRestrict d) h.symm).elim
          · rcases bcd' with b' | cd'
            · exact (rlcScaleOneCodeB_ne_codeD
                (rlcScaleOneFiberBPayload b')
                (rlcScaleOneFiberDRestrict d) h.symm).elim
            · rcases cd' with c' | d'
              · exact (rlcScaleOneCodeC_ne_codeD
                  (rlcScaleOneFiberCPayload c')
                  (rlcScaleOneFiberDRestrict d) h.symm).elim
              · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inr z)))
                  (rlcScaleOneFiberDTarget.injective h)

def rlcScaleOneFourRouteSuccess (eta : RlcScaleOneEdgeConfig) : Bool :=
  (eta 7 && eta 8) || (eta 2 && eta 6 && eta 7) ||
    (eta 5 && eta 6 && eta 7) || (eta 10 && eta 11 && eta 12)

theorem rlcScaleOneTaggedTarget_success (rho : RlcScaleOneRoutedFailure) :
    rlcScaleOneFourRouteSuccess (rlcScaleOneTaggedTarget rho) = true := by
  rcases rho with a | bcd
  · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberATarget,
      rlcScaleOneCodeAEmbedding, rlcScaleOneFourRouteSuccess,
      rlcScaleOneCodeA]
  · rcases bcd with b | cd
    · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberBTarget,
        rlcScaleOneCodeBEmbedding, rlcScaleOneFourRouteSuccess,
        rlcScaleOneCodeB]
    · rcases cd with c | d
      · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberCTarget,
          rlcScaleOneCodeCEmbedding, rlcScaleOneFourRouteSuccess,
          rlcScaleOneCodeC]
      · simp [rlcScaleOneTaggedTarget, rlcScaleOneFiberDTarget,
          rlcScaleOneCodeDEmbedding, rlcScaleOneFourRouteSuccess,
          rlcScaleOneCodeD]

def rlcScaleOneRouteMasks : List Nat :=
  [384, 19, 28, 196, 56, 224, 2816, 8960, 7168, 13312, 50176,
    2628, 8772, 344, 2656, 8800, 5760, 203, 54016, 2635, 8779,
    53828, 5720, 53856, 53835]

def RlcScaleOneRouteOpen (omega : RlcScaleOneEdgeConfig) (mask : Nat) : Prop :=
  ∀ i : Fin 16, mask.testBit i → omega i = true

def RlcScaleOneConnectorSuccess (omega : RlcScaleOneEdgeConfig) : Prop :=
  ∃ mask ∈ rlcScaleOneRouteMasks, RlcScaleOneRouteOpen omega mask

abbrev RlcScaleOneConnectorFailure :=
  {omega : RlcScaleOneEdgeConfig // ¬RlcScaleOneConnectorSuccess omega}

theorem rlcScaleOneFailure_route_not_open
    (rho : RlcScaleOneConnectorFailure) {mask : Nat}
    (hmask : mask ∈ rlcScaleOneRouteMasks) :
    ¬RlcScaleOneRouteOpen rho.1 mask := by
  intro hopen
  exact rho.2 ⟨mask, hmask, hopen⟩

theorem rlcScaleOne_exists_closed_edge_of_route_not_open
    (omega : RlcScaleOneEdgeConfig) (mask : Nat)
    (h : ¬RlcScaleOneRouteOpen omega mask) :
    ∃ i : Fin 16, mask.testBit i ∧ omega i = false := by
  by_contra hex
  push Not at hex
  apply h
  intro i hi
  have hne := hex i hi
  cases homega : omega i <;> simp_all

theorem rlcScaleOneFailure_closed_edge
    (rho : RlcScaleOneConnectorFailure) {mask : Nat}
    (hmask : mask ∈ rlcScaleOneRouteMasks) :
    ∃ i : Fin 16, mask.testBit i ∧ rho.1 i = false :=
  rlcScaleOne_exists_closed_edge_of_route_not_open rho.1 mask
    (rlcScaleOneFailure_route_not_open rho hmask)

theorem rlcScaleOneMask384_support (i : Fin 16) (h : Nat.testBit 384 i) :
    i = 7 ∨ i = 8 := by revert i; decide
theorem rlcScaleOneMask19_support (i : Fin 16) (h : Nat.testBit 19 i) :
    i = 0 ∨ i = 1 ∨ i = 4 := by revert i; decide
theorem rlcScaleOneMask7168_support (i : Fin 16) (h : Nat.testBit 7168 i) :
    i = 10 ∨ i = 11 ∨ i = 12 := by revert i; decide
theorem rlcScaleOneMask28_support (i : Fin 16) (h : Nat.testBit 28 i) :
    i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide
theorem rlcScaleOneMask50176_support (i : Fin 16) (h : Nat.testBit 50176 i) :
    i = 10 ∨ i = 14 ∨ i = 15 := by revert i; decide
theorem rlcScaleOneMask8960_support (i : Fin 16) (h : Nat.testBit 8960 i) :
    i = 8 ∨ i = 9 ∨ i = 13 := by revert i; decide
theorem rlcScaleOneMask13312_support (i : Fin 16) (h : Nat.testBit 13312 i) :
    i = 10 ∨ i = 12 ∨ i = 13 := by revert i; decide
theorem rlcScaleOneMask8800_support (i : Fin 16) (h : Nat.testBit 8800 i) :
    i = 5 ∨ i = 6 ∨ i = 9 ∨ i = 13 := by revert i; decide
theorem rlcScaleOneMask56_support (i : Fin 16) (h : Nat.testBit 56 i) :
    i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide
theorem rlcScaleOneMask344_support (i : Fin 16) (h : Nat.testBit 344 i) :
    i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 8 := by revert i; decide
theorem rlcScaleOneMask224_support (i : Fin 16) (h : Nat.testBit 224 i) :
    i = 5 ∨ i = 6 ∨ i = 7 := by revert i; decide
theorem rlcScaleOneMask196_support (i : Fin 16) (h : Nat.testBit 196 i) :
    i = 2 ∨ i = 6 ∨ i = 7 := by revert i; decide
theorem rlcScaleOneMask2816_support (i : Fin 16) (h : Nat.testBit 2816 i) :
    i = 8 ∨ i = 9 ∨ i = 11 := by revert i; decide
theorem rlcScaleOneMask2628_support (i : Fin 16) (h : Nat.testBit 2628 i) :
    i = 2 ∨ i = 6 ∨ i = 9 ∨ i = 11 := by revert i; decide
theorem rlcScaleOneMask2656_support (i : Fin 16) (h : Nat.testBit 2656 i) :
    i = 5 ∨ i = 6 ∨ i = 9 ∨ i = 11 := by revert i; decide

theorem rlcScaleOneFailure_closed384 (rho : RlcScaleOneConnectorFailure) :
    rho.1 7 = false ∨ rho.1 8 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 384) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask384_support i hi with rfl | rfl
  · exact Or.inl hc
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed19 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 0 = false ∨ rho.1 1 = false) ∨ rho.1 4 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 19) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask19_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed7168 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 10 = false ∨ rho.1 11 = false) ∨ rho.1 12 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 7168) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask7168_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed28 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 2 = false ∨ rho.1 3 = false) ∨ rho.1 4 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 28) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask28_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed50176 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 10 = false ∨ rho.1 14 = false) ∨ rho.1 15 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 50176) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask50176_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed8960 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 8 = false ∨ rho.1 9 = false) ∨ rho.1 13 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 8960) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask8960_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed13312 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 10 = false ∨ rho.1 12 = false) ∨ rho.1 13 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 13312) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask13312_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed8800 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨
      rho.1 13 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 8800) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask8800_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed56 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 3 = false ∨ rho.1 4 = false) ∨ rho.1 5 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 56) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask56_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed344 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 3 = false ∨ rho.1 4 = false) ∨ rho.1 6 = false) ∨
      rho.1 8 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 344) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask344_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed224 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 7 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 224) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask224_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed196 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 2 = false ∨ rho.1 6 = false) ∨ rho.1 7 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 196) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask196_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed2816 (rho : RlcScaleOneConnectorFailure) :
    (rho.1 8 = false ∨ rho.1 9 = false) ∨ rho.1 11 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 2816) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask2816_support i hi with rfl | rfl | rfl
  · exact Or.inl (Or.inl hc)
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed2628 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 2 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨
      rho.1 11 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 2628) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask2628_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_closed2656 (rho : RlcScaleOneConnectorFailure) :
    ((rho.1 5 = false ∨ rho.1 6 = false) ∨ rho.1 9 = false) ∨
      rho.1 11 = false := by
  rcases rlcScaleOneFailure_closed_edge rho (mask := 2656) (by decide) with ⟨i, hi, hc⟩
  rcases rlcScaleOneMask2656_support i hi with rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr hc)
  · exact Or.inr hc

theorem rlcScaleOneFailure_fiberA
    (rho : RlcScaleOneConnectorFailure)
    (_hclass : rlcScaleOneRouteClass rho.1 = 0) :
    rlcScaleOneSectionAAvoidsSelectedRoutes
      (rlcScaleOneRestrictA rho.1) = true := by
  have h384 := rlcScaleOneFailure_closed384 rho
  have h19 := rlcScaleOneFailure_closed19 rho
  have h7168 := rlcScaleOneFailure_closed7168 rho
  have h28 := rlcScaleOneFailure_closed28 rho
  have h50176 := rlcScaleOneFailure_closed50176 rho
  simp [rlcScaleOneSectionAAvoidsSelectedRoutes,
    rlcScaleOnePairBlockAvoidsRoute, rlcScaleOneFiveBlockAvoidsRoutes,
    rlcScaleOneRestrictA]
  tauto

theorem rlcScaleOneBool_false_of_true_of_false {b : Bool}
    (htrue : b = true) (hfalse : b = false) : False :=
  Bool.false_ne_true (hfalse.symm.trans htrue)

theorem rlcScaleOneFailure_fiberB
    (rho : RlcScaleOneConnectorFailure)
    (hclass : rlcScaleOneRouteClass rho.1 = 1) :
    rlcScaleOneSectionBAvoidsSelectedRoutes
      (rlcScaleOneRestrictB rho.1) = true := by
  have hfix := rlcScaleOneRouteClass_one_fixed rho.1 hclass
  have h19 := rlcScaleOneFailure_closed19 rho
  have h8960 := rlcScaleOneFailure_closed8960 rho
  have h50176 := rlcScaleOneFailure_closed50176 rho
  have h28 := rlcScaleOneFailure_closed28 rho
  have h13312 := rlcScaleOneFailure_closed13312 rho
  have h8800 := rlcScaleOneFailure_closed8800 rho
  have h56 := rlcScaleOneFailure_closed56 rho
  have h8800' : (rho.1 5 = false ∨ rho.1 9 = false) ∨
      rho.1 13 = false := by
    rcases h8800 with h5or6or9 | h13
    · rcases h5or6or9 with h5or6 | h9
      · rcases h5or6 with h5 | h6false
        · exact Or.inl (Or.inl h5)
        · exact (rlcScaleOneBool_false_of_true_of_false hfix.1 h6false).elim
      · exact Or.inl (Or.inr h9)
    · exact Or.inr h13
  simp [rlcScaleOneSectionBAvoidsSelectedRoutes, rlcScaleOneRestrictB]
  exact ⟨⟨⟨⟨⟨⟨h19, h8960⟩, h50176⟩, h28⟩, h13312⟩,
    h8800'⟩, h56⟩

theorem rlcScaleOneFailure_fiberC
    (rho : RlcScaleOneConnectorFailure)
    (hclass : rlcScaleOneRouteClass rho.1 = 2) :
    rlcScaleOneSectionCAvoidsSelectedRoutes
      (rlcScaleOneRestrictC rho.1) = true := by
  have hfix := rlcScaleOneRouteClass_two_fixed rho.1 hclass
  have h7168 := rlcScaleOneFailure_closed7168 rho
  have h19 := rlcScaleOneFailure_closed19 rho
  have h28 := rlcScaleOneFailure_closed28 rho
  have h50176 := rlcScaleOneFailure_closed50176 rho
  have h56 := rlcScaleOneFailure_closed56 rho
  have h344 := rlcScaleOneFailure_closed344 rho
  have h7168' : rho.1 10 = false ∨ rho.1 12 = false := by
    rcases h7168 with h10or11 | h12
    · rcases h10or11 with h10 | h11false
      · exact Or.inl h10
      · exact (rlcScaleOneBool_false_of_true_of_false hfix.2.1 h11false).elim
    · exact Or.inr h12
  have h344' : (rho.1 3 = false ∨ rho.1 4 = false) ∨
      rho.1 8 = false := by
    rcases h344 with h3or4or6 | h8
    · rcases h3or4or6 with h3or4 | h6false
      · exact Or.inl h3or4
      · exact (rlcScaleOneBool_false_of_true_of_false hfix.1 h6false).elim
    · exact Or.inr h8
  simp [rlcScaleOneSectionCAvoidsSelectedRoutes, rlcScaleOneRestrictC]
  exact ⟨⟨⟨⟨⟨h7168', h19⟩, h28⟩, h50176⟩, h56⟩, h344'⟩

theorem rlcScaleOneFailure_fiberD
    (rho : RlcScaleOneConnectorFailure)
    (hclass : rlcScaleOneRouteClass rho.1 = 3) :
    rho.1 2 = false ∧ rho.1 5 = false ∧ rho.1 6 = true ∧
      rho.1 8 = false := by
  have h384 := rlcScaleOneFailure_closed384 rho
  have h224 := rlcScaleOneFailure_closed224 rho
  have h196 := rlcScaleOneFailure_closed196 rho
  have h2816 := rlcScaleOneFailure_closed2816 rho
  have h2628 := rlcScaleOneFailure_closed2628 rho
  have h2656 := rlcScaleOneFailure_closed2656 rho
  have hfix := rlcScaleOneRouteClass_three_fixed rho.1 hclass
  rcases hfix with ⟨h6, h11or7, h9or7⟩
  by_cases h7 : rho.1 7 = false
  · have h11 : rho.1 11 = true := by
      rcases h11or7 with h11 | h7true
      · exact h11
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7).elim
    have h9 : rho.1 9 = true := by
      rcases h9or7 with h9 | h7true
      · exact h9
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7).elim
    have h2 : rho.1 2 = false := by
      rcases h2628 with h2or6or9 | h11false
      · rcases h2or6or9 with h2or6 | h9false
        · rcases h2or6 with h2 | h6false
          · exact h2
          · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
        · exact (rlcScaleOneBool_false_of_true_of_false h9 h9false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h11 h11false).elim
    have h5 : rho.1 5 = false := by
      rcases h2656 with h5or6or9 | h11false
      · rcases h5or6or9 with h5or6 | h9false
        · rcases h5or6 with h5 | h6false
          · exact h5
          · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
        · exact (rlcScaleOneBool_false_of_true_of_false h9 h9false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h11 h11false).elim
    have h8 : rho.1 8 = false := by
      rcases h2816 with h8or9 | h11false
      · rcases h8or9 with h8 | h9false
        · exact h8
        · exact (rlcScaleOneBool_false_of_true_of_false h9 h9false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h11 h11false).elim
    exact ⟨h2, h5, h6, h8⟩
  · have h7true : rho.1 7 = true := by
      cases h7value : rho.1 7
      · exact (h7 h7value).elim
      · rfl
    have h2 : rho.1 2 = false := by
      rcases h196 with h2or6 | h7false
      · rcases h2or6 with h2 | h6false
        · exact h2
        · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7false).elim
    have h5 : rho.1 5 = false := by
      rcases h224 with h5or6 | h7false
      · rcases h5or6 with h5 | h6false
        · exact h5
        · exact (rlcScaleOneBool_false_of_true_of_false h6 h6false).elim
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7false).elim
    have h8 : rho.1 8 = false := by
      rcases h384 with h7false | h8
      · exact (rlcScaleOneBool_false_of_true_of_false h7true h7false).elim
      · exact h8
    exact ⟨h2, h5, h6, h8⟩

def rlcScaleOneRoutedFailureConfig
    (rho : RlcScaleOneRoutedFailure) : RlcScaleOneEdgeConfig :=
  match rho with
  | Sum.inl a => a.1
  | Sum.inr (Sum.inl b) => b.1
  | Sum.inr (Sum.inr (Sum.inl c)) => c.1
  | Sum.inr (Sum.inr (Sum.inr d)) => d.1

def rlcScaleOneFailureClassify
    (rho : RlcScaleOneConnectorFailure) : RlcScaleOneRoutedFailure :=
  if h0 : rlcScaleOneRouteClass rho.1 = 0 then
    Sum.inl ⟨rho.1, h0, rlcScaleOneFailure_fiberA rho h0⟩
  else if h1 : rlcScaleOneRouteClass rho.1 = 1 then
    Sum.inr (Sum.inl ⟨rho.1, h1, rlcScaleOneFailure_fiberB rho h1⟩)
  else if h2 : rlcScaleOneRouteClass rho.1 = 2 then
    Sum.inr (Sum.inr (Sum.inl
      ⟨rho.1, h2, rlcScaleOneFailure_fiberC rho h2⟩))
  else
    have h3 : rlcScaleOneRouteClass rho.1 = 3 := by
      apply Fin.eq_of_val_eq
      have hlt := (rlcScaleOneRouteClass rho.1).isLt
      have hn0 : (rlcScaleOneRouteClass rho.1).val ≠ 0 := by
        intro hval
        exact h0 (Fin.eq_of_val_eq hval)
      have hn1 : (rlcScaleOneRouteClass rho.1).val ≠ 1 := by
        intro hval
        exact h1 (Fin.eq_of_val_eq hval)
      have hn2 : (rlcScaleOneRouteClass rho.1).val ≠ 2 := by
        intro hval
        exact h2 (Fin.eq_of_val_eq hval)
      omega
    Sum.inr (Sum.inr (Sum.inr
      ⟨rho.1, h3, rlcScaleOneFailure_fiberD rho h3⟩))

theorem rlcScaleOneFailureClassify_config
    (rho : RlcScaleOneConnectorFailure) :
    rlcScaleOneRoutedFailureConfig (rlcScaleOneFailureClassify rho) = rho.1 := by
  unfold rlcScaleOneFailureClassify
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

def rlcScaleOneFailureClassifyEmbedding :
    RlcScaleOneConnectorFailure ↪ RlcScaleOneRoutedFailure where
  toFun := rlcScaleOneFailureClassify
  inj' rho rho' h := by
    apply Subtype.ext
    have hconfig := congrArg rlcScaleOneRoutedFailureConfig h
    simpa only [rlcScaleOneFailureClassify_config] using hconfig

theorem rlcScaleOneTaggedTarget_connectorSuccess
    (rho : RlcScaleOneRoutedFailure) :
    RlcScaleOneConnectorSuccess (rlcScaleOneTaggedTarget rho) := by
  have h := rlcScaleOneTaggedTarget_success rho
  simp only [rlcScaleOneFourRouteSuccess, Bool.or_eq_true,
    Bool.and_eq_true] at h
  rcases h with habc | h7168
  · rcases habc with hab | h224
    · rcases hab with h384 | h196
      · refine ⟨384, by decide, ?_⟩
        intro i hi
        rcases rlcScaleOneMask384_support i hi with rfl | rfl
        · exact h384.1
        · exact h384.2
      · refine ⟨196, by decide, ?_⟩
        intro i hi
        rcases rlcScaleOneMask196_support i hi with rfl | rfl | rfl
        · exact h196.1.1
        · exact h196.1.2
        · exact h196.2
    · refine ⟨224, by decide, ?_⟩
      intro i hi
      rcases rlcScaleOneMask224_support i hi with rfl | rfl | rfl
      · exact h224.1.1
      · exact h224.1.2
      · exact h224.2
  · refine ⟨7168, by decide, ?_⟩
    intro i hi
    rcases rlcScaleOneMask7168_support i hi with rfl | rfl | rfl
    · exact h7168.1.1
    · exact h7168.1.2
    · exact h7168.2

abbrev RlcScaleOneConnectorSuccessConfig :=
  {eta : RlcScaleOneEdgeConfig // RlcScaleOneConnectorSuccess eta}

noncomputable def rlcScaleOneConnectorFailureEmbedding :
    RlcScaleOneConnectorFailure ↪ RlcScaleOneConnectorSuccessConfig where
  toFun rho :=
    ⟨rlcScaleOneTaggedTarget (rlcScaleOneFailureClassify rho),
      rlcScaleOneTaggedTarget_connectorSuccess
        (rlcScaleOneFailureClassify rho)⟩
  inj' rho rho' h := by
    apply rlcScaleOneFailureClassifyEmbedding.injective
    apply rlcScaleOneTaggedTargetEmbedding.injective
    exact congrArg Subtype.val h




theorem rlcScaleOneFiberA_reservedBit_not_pointwise :
    ∃ rho sigma : RlcScaleOneFiberA, rho.1 7 ≠ sigma.1 7 := by
  let rho : RlcScaleOneFiberA := ⟨fun _ => false, by decide⟩
  let sigma : RlcScaleOneFiberA :=
    ⟨fun i => decide (i = (7 : Fin 16)), by decide⟩
  exact ⟨rho, sigma, by simp [rho, sigma]⟩

#print axioms rlcScaleOneConnectorFailureEmbedding
#print axioms rlcScaleOneFiberA_reservedBit_not_pointwise

end StatMech.Universality
