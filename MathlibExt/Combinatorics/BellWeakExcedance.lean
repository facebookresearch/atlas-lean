/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

@[expose] public section

section

namespace MetaMathlibExt

private def wexSet (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ≤ σ i)

private theorem exists_hit (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∃ t, ⇑(σ ^ t) i ∈ wexSet n σ := by
  by_contra h
  simp only [not_exists] at h
  have desc : ∀ t, (⇑(σ ^ (t + 1)) i).val < (⇑(σ ^ t) i).val := by
    intro t
    have hmem := h t
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hlt : ⇑σ (⇑(σ ^ t) i) < ⇑(σ ^ t) i := lt_of_not_ge hmem
    have hpow : ⇑(σ ^ (t + 1)) i = ⇑σ (⇑(σ ^ t) i) := by
      rw [pow_succ']
      rfl
    rw [hpow]
    exact hlt
  have bound : ∀ t, (⇑(σ ^ t) i).val + t ≤ i.val := by
    intro t
    induction t with
    | zero => simp
    | succ k ih =>
      have dk := desc k
      omega
  have hlast := bound (i.val + 1)
  omega

private def root (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  ⇑(σ ^ (Nat.find (exists_hit n σ i))) i

private theorem root_mem (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    root n σ i ∈ wexSet n σ :=
  Nat.find_spec (exists_hit n σ i)

private theorem root_eq_self (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (hi : i ∈ wexSet n σ) : root n σ i = i := by
  unfold root
  have h0 : (⇑(σ ^ 0) i) ∈ wexSet n σ := by simpa using hi
  have hfind : Nat.find (exists_hit n σ i) = 0 :=
    (Nat.find_eq_zero _).mpr h0
  rw [hfind]
  simp

private theorem root_le (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    root n σ i ≤ i := by
  unfold root
  suffices h : (⇑(σ ^ (Nat.find (exists_hit n σ i))) i).val ≤ i.val by
    exact Fin.mk_le_mk.mpr h
  have key : ∀ t, t ≤ Nat.find (exists_hit n σ i) →
      (⇑(σ ^ t) i).val + t ≤ i.val := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ k ih =>
      intro hle
      have hlt : k < Nat.find (exists_hit n σ i) := by omega
      have hnot : (⇑(σ ^ k) i) ∉ wexSet n σ :=
        Nat.find_min (exists_hit n σ i) hlt
      simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      have hlt2 : ⇑σ (⇑(σ ^ k) i) < ⇑(σ ^ k) i := lt_of_not_ge hnot
      have hpow : ⇑(σ ^ (k + 1)) i = ⇑σ (⇑(σ ^ k) i) := by
        rw [pow_succ']
        rfl
      have ih' := ih (by omega)
      rw [hpow]
      omega
  have := key _ le_rfl
  omega

private theorem root_idem (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    root n σ (root n σ i) = root n σ i :=
  root_eq_self n σ _ (root_mem n σ i)

/-! ## Part A: Finpartitions are counted by Bell numbers -/

private def removeBlock {n : ℕ} {S B : Finset (Fin n)} (P : Finpartition S)
    (hBmem : B ∈ P.parts) : Finpartition (S \ B) :=
  Finpartition.ofExistsUnique (P.parts.erase B)
    (by
      intro p hp
      rw [Finset.mem_erase] at hp
      have hdisj : Disjoint p B := by
        rw [Finset.disjoint_left]
        intro x hx hxB
        exact hp.1 (P.eq_of_mem_parts hp.2 hBmem hx hxB)
      exact Finset.subset_sdiff.mpr ⟨P.subset hp.2, hdisj⟩)
    (by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      have haS : a ∈ S := ha.1
      have haB : a ∉ B := ha.2
      obtain ⟨t, ⟨ht, hat⟩, huniq⟩ := P.existsUnique_mem haS
      have htB : t ≠ B := by
        intro h
        rw [h] at hat
        exact haB hat
      refine ⟨t, ⟨Finset.mem_erase.mpr ⟨htB, ht⟩, hat⟩, ?_⟩
      intro y hy
      obtain ⟨hy_erase, hay⟩ := hy
      rw [Finset.mem_erase] at hy_erase
      exact huniq y ⟨hy_erase.2, hay⟩)
    (by
      intro h
      exact P.empty_notMem_parts (Finset.mem_of_mem_erase h))

private def addBlock {n : ℕ} {S : Finset (Fin n)} {B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B)) :
    Finpartition S :=
  Finpartition.ofExistsUnique (insert B Q.parts)
    (by
      intro p hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hQ
      · exact hBsub
      · exact (Q.subset hQ).trans Finset.sdiff_subset)
    (by
      intro a haS
      by_cases haB : a ∈ B
      · refine ⟨B, ⟨Finset.mem_insert_self B Q.parts, haB⟩, ?_⟩
        intro y hy
        obtain ⟨hy_ins, hay⟩ := hy
        rw [Finset.mem_insert] at hy_ins
        rcases hy_ins with rfl | hQ
        · rfl
        · have hsub : y ⊆ S \ B := Q.subset hQ
          have hayS : a ∈ S \ B := hsub hay
          rw [Finset.mem_sdiff] at hayS
          exact absurd haB hayS.2
      · have haQ : a ∈ S \ B := Finset.mem_sdiff.mpr ⟨haS, haB⟩
        obtain ⟨t, ⟨ht, hat⟩, huniq⟩ := Q.existsUnique_mem haQ
        refine ⟨t, ⟨Finset.mem_insert_of_mem ht, hat⟩, ?_⟩
        intro y hy
        obtain ⟨hy_ins, hay⟩ := hy
        rw [Finset.mem_insert] at hy_ins
        rcases hy_ins with rfl | hQ
        · exact absurd hay haB
        · exact huniq y ⟨hQ, hay⟩)
    (by
      simp only [Finset.mem_insert, not_or]
      constructor
      · intro h
        rw [← h] at hBne
        exact Finset.not_nonempty_empty hBne
      · exact Q.empty_notMem_parts)

private theorem removeBlock_parts {n : ℕ} {S B : Finset (Fin n)}
    (P : Finpartition S) (hBmem : B ∈ P.parts) :
    (removeBlock P hBmem).parts = P.parts.erase B := rfl

private theorem addBlock_parts {n : ℕ} {S B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B)) :
    (addBlock hBsub hBne Q).parts = insert B Q.parts := rfl

private theorem addBlock_part {n : ℕ} {S B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B))
    (m0 : Fin n) (hmB : m0 ∈ B) :
    (addBlock hBsub hBne Q).part m0 = B := by
  have hmS : m0 ∈ S := hBsub hmB
  have hmem : B ∈ (addBlock hBsub hBne Q).parts := by
    rw [addBlock_parts]
    exact Finset.mem_insert_self B Q.parts
  exact (addBlock hBsub hBne Q).part_eq_of_mem hmem hmB

private theorem block_notMem_parts {n : ℕ} {S B : Finset (Fin n)}
    (m0 : Fin n) (hmB : m0 ∈ B) (Q : Finpartition (S \ B)) :
    B ∉ Q.parts := by
  intro h
  have hsub : B ⊆ S \ B := Q.subset h
  have hmem : m0 ∈ S \ B := hsub hmB
  rw [Finset.mem_sdiff] at hmem
  exact hmem.2 hmB

private theorem finpartition_eq_of_parts_eq {α : Type*} [Lattice α] [OrderBot α]
    {a : α} {P Q : Finpartition a} (h : P.parts = Q.parts) : P = Q := by
  obtain ⟨p1, s1, u1, b1⟩ := P
  obtain ⟨p2, s2, u2, b2⟩ := Q
  simp only at h
  subst h
  rfl

private theorem add_remove_cancel {n : ℕ} {S B : Finset (Fin n)}
    (P : Finpartition S) (hBmem : B ∈ P.parts)
    (hBsub : B ⊆ S) (hBne : B.Nonempty) :
    addBlock hBsub hBne (removeBlock P hBmem) = P := by
  apply finpartition_eq_of_parts_eq
  rw [addBlock_parts, removeBlock_parts]
  exact Finset.insert_erase hBmem

private theorem remove_add_cancel {n : ℕ} {S B : Finset (Fin n)}
    (hBsub : B ⊆ S) (hBne : B.Nonempty) (Q : Finpartition (S \ B))
    (m0 : Fin n) (hmB : m0 ∈ B) :
    removeBlock (addBlock hBsub hBne Q)
      (by rw [addBlock_parts]; exact Finset.mem_insert_self B Q.parts) = Q := by
  apply finpartition_eq_of_parts_eq
  rw [removeBlock_parts, addBlock_parts]
  have hnot : B ∉ Q.parts := block_notMem_parts m0 hmB Q
  exact Finset.erase_insert hnot

private def fiberEquiv {n : ℕ} {S B : Finset (Fin n)} (m0 : Fin n)
    (hmB : m0 ∈ B) (hBsub : B ⊆ S) :
    { P : Finpartition S // P.part m0 = B } ≃ Finpartition (S \ B) where
  toFun x :=
    removeBlock x.1
      (by
        have hmem : x.1.part m0 ∈ x.1.parts :=
          x.1.part_mem.mpr (hBsub hmB)
        rw [x.2] at hmem
        exact hmem)
  invFun Q :=
    ⟨addBlock hBsub ⟨m0, hmB⟩ Q,
      addBlock_part hBsub ⟨m0, hmB⟩ Q m0 hmB⟩
  left_inv x := by
    obtain ⟨P, hP⟩ := x
    have hBmem : B ∈ P.parts := by
      have hmem : P.part m0 ∈ P.parts := P.part_mem.mpr (hBsub hmB)
      rw [hP] at hmem
      exact hmem
    have hEq : addBlock hBsub ⟨m0, hmB⟩ (removeBlock P hBmem) = P :=
      add_remove_cancel P hBmem hBsub ⟨m0, hmB⟩
    exact Subtype.ext hEq
  right_inv Q := remove_add_cancel hBsub ⟨m0, hmB⟩ Q m0 hmB

private theorem card_finpartition_empty (n : ℕ) :
    Fintype.card (Finpartition (∅ : Finset (Fin n))) = 1 := by
  have hU : Unique (Finpartition (∅ : Finset (Fin n))) := inferInstanceAs
    (Unique (Finpartition (⊥ : Finset (Fin n))))
  exact Fintype.card_unique

private theorem card_finpartition_eq_bell_aux (n : ℕ) (m : ℕ) :
    ∀ T : Finset (Fin n), T.card = m →
      Fintype.card (Finpartition T) = Nat.bell m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro T hcard
    by_cases hT0 : T.card = 0
    · have hTe : T = ∅ := Finset.card_eq_zero.mp hT0
      subst hTe
      rw [card_finpartition_empty]
      rw [hT0] at hcard
      rw [← hcard]
      exact Nat.bell_zero.symm
    · obtain ⟨m0, hm0⟩ : T.Nonempty := by
        rw [← Finset.card_pos]
        exact Nat.pos_of_ne_zero hT0
      have hcard_eq : Fintype.card (Finpartition T) =
          ∑ B : Finset (Fin n),
            Fintype.card { P : Finpartition T // P.part m0 = B } := by
        have hEquiv : Finpartition T ≃
            (Σ B : Finset (Fin n), { P : Finpartition T // P.part m0 = B }) :=
          (Equiv.sigmaFiberEquiv (fun P : Finpartition T => P.part m0)).symm
        rw [Fintype.card_congr hEquiv, Fintype.card_sigma]
      have hfiber : ∀ B : Finset (Fin n),
          Fintype.card { P : Finpartition T // P.part m0 = B } =
            (if m0 ∈ B ∧ B ⊆ T then Nat.bell (T.card - B.card) else 0) := by
        intro B
        by_cases hB : m0 ∈ B ∧ B ⊆ T
        · have hmB : m0 ∈ B := hB.1
          have hsub : B ⊆ T := hB.2
          have hEquiv := fiberEquiv m0 hmB hsub
          have hcard2 : Fintype.card { P : Finpartition T // P.part m0 = B } =
              Fintype.card (Finpartition (T \ B)) :=
            Fintype.card_congr hEquiv
          have hlt : (T \ B).card < m := by
            have hpos : 0 < B.card := Finset.card_pos.mpr ⟨m0, hmB⟩
            have hle : B.card ≤ T.card := Finset.card_le_card hsub
            have hsd : (T \ B).card = T.card - B.card :=
              Finset.card_sdiff_of_subset hsub
            omega
          have hIH := ih ((T \ B).card) hlt (T \ B) rfl
          have hsd : (T \ B).card = T.card - B.card :=
            Finset.card_sdiff_of_subset hsub
          rw [hcard2, hIH, hsd]
          simp [hB]
        · have hEmpty : IsEmpty { P : Finpartition T // P.part m0 = B } :=
            ⟨fun ⟨P, hP⟩ => by
              have hmB : m0 ∈ B := by
                have hmem : m0 ∈ P.part m0 := P.mem_part hm0
                rw [hP] at hmem
                exact hmem
              have hsub : B ⊆ T := by
                have hss : P.part m0 ⊆ T := P.part_subset m0
                rw [hP] at hss
                exact hss
              exact hB ⟨hmB, hsub⟩⟩
          rw [Fintype.card_eq_zero]
          simp [hB]
      rw [hcard_eq]
      simp only [hfiber]
      have hsum : (∑ B : Finset (Fin n),
          (if m0 ∈ B ∧ B ⊆ T then Nat.bell (T.card - B.card) else 0)) =
          ∑ B ∈ Finset.univ.filter (fun B => m0 ∈ B ∧ B ⊆ T),
            Nat.bell (T.card - B.card) := by
        rw [Finset.sum_filter]
      have hfilter_eq : Finset.univ.filter (fun B : Finset (Fin n) => m0 ∈ B ∧ B ⊆ T) =
          (T.powerset.filter (fun B => m0 ∈ B)) := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powerset]
        constructor
        · intro h
          exact ⟨h.2, h.1⟩
        · intro h
          exact ⟨h.2, h.1⟩
      rw [hsum, hfilter_eq]
      set E : Finset (Fin n) := T.erase m0 with hE
      have hm0E : m0 ∉ E := Finset.notMem_erase m0 T
      have hTE : T = insert m0 E := (Finset.insert_erase hm0).symm
      have hcardE : E.card + 1 = m := by
        have hce : E.card = T.card - 1 := Finset.card_erase_of_mem hm0
        omega
      have himage : T.powerset.filter (fun B => m0 ∈ B) =
          E.powerset.image (fun U => insert m0 U) := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
        constructor
        · intro h
          obtain ⟨hsub, hmB⟩ := h
          refine ⟨B.erase m0, ?_, Finset.insert_erase hmB⟩
          intro x hx
          rw [Finset.mem_erase] at hx
          rw [hE, Finset.mem_erase]
          exact ⟨hx.1, hsub hx.2⟩
        · intro h
          obtain ⟨U, hU, rfl⟩ := h
          constructor
          · intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hUx
            · exact hm0
            · exact Finset.mem_of_mem_erase (hE ▸ hU hUx)
          · exact Finset.mem_insert_self m0 U
      rw [himage]
      have hinj : ∀ U1 ∈ E.powerset, ∀ U2 ∈ E.powerset,
          insert m0 U1 = insert m0 U2 → U1 = U2 := by
        intro U1 hU1 U2 hU2 hEq
        have h1 : m0 ∉ U1 := by
          have hsub1 : U1 ⊆ E := Finset.mem_powerset.mp hU1
          exact fun h => hm0E (hE ▸ hsub1 h)
        have h2 : m0 ∉ U2 := by
          have hsub2 : U2 ⊆ E := Finset.mem_powerset.mp hU2
          exact fun h => hm0E (hE ▸ hsub2 h)
        have hc := congrArg (fun S => S.erase m0) hEq
        simp only [Finset.erase_insert h1, Finset.erase_insert h2] at hc
        exact hc
      rw [Finset.sum_image hinj]
      have hterm : ∀ U ∈ E.powerset,
          T.card - (insert m0 U).card = E.card - U.card := by
        intro U hU
        have hsub : U ⊆ E := Finset.mem_powerset.mp hU
        have hnot : m0 ∉ U := fun h => hm0E (hE ▸ hsub h)
        have hcIns : (insert m0 U).card = U.card + 1 :=
          Finset.card_insert_of_notMem hnot
        have hle : U.card ≤ E.card := Finset.card_le_card hsub
        omega
      have hsum2 : (∑ U ∈ E.powerset, Nat.bell (T.card - (insert m0 U).card)) =
          ∑ U ∈ E.powerset, Nat.bell (E.card - U.card) := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [hterm U hU]
      rw [hsum2]
      have hmaps : ∀ U ∈ E.powerset, U.card ∈ Finset.range (E.card + 1) := by
        intro U hU
        rw [Finset.mem_range]
        have hsub : U ⊆ E := Finset.mem_powerset.mp hU
        have hle : U.card ≤ E.card := Finset.card_le_card hsub
        omega
      have hfib := Finset.sum_fiberwise_of_maps_to hmaps
        (fun U => Nat.bell (E.card - U.card))
      rw [← hfib]
      have hinner : ∀ i ∈ Finset.range (E.card + 1),
          (∑ U ∈ E.powerset.filter (fun U => U.card = i),
            Nat.bell (E.card - U.card)) =
            Nat.choose E.card i * Nat.bell (E.card - i) := by
        intro i hi
        have hfilter : E.powerset.filter (fun U => U.card = i) =
            E.powersetCard i := by
          ext U
          simp only [Finset.mem_filter, Finset.mem_powerset,
            Finset.mem_powersetCard]
        rw [hfilter]
        have hconst : ∀ U ∈ E.powersetCard i,
            Nat.bell (E.card - U.card) = Nat.bell (E.card - i) := by
          intro U hU
          rw [Finset.mem_powersetCard] at hU
          rw [hU.2]
        rw [Finset.sum_congr rfl hconst]
        rw [Finset.sum_const, Finset.card_powersetCard]
        simp only [smul_eq_mul]
      rw [Finset.sum_congr rfl hinner]
      have hbell := Nat.bell_succ E.card
      rw [← hcardE] at hcard ⊢
      -- hcard : T.card = E.card + 1, goal: ∑ i ∈ range, ... = bell (E.card+1)
      rw [hbell]
      rw [← Nat.range_succ_eq_Iic]

private theorem card_finpartition_univ (n : ℕ) :
    Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) = Nat.bell n := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by
    simp only [Finset.card_univ, Fintype.card_fin]
  exact card_finpartition_eq_bell_aux n n _ hcard

/-! ## Part B: Valid perms biject with Finpartitions -/

private noncomputable def toPart (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Finpartition (Finset.univ : Finset (Fin n)) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker (root n σ))

private theorem mem_toPart_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {a b : Fin n} :
    b ∈ (toPart n σ).part a ↔ root n σ a = root n σ b := by
  unfold toPart
  classical
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

private theorem root_eq_self_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    root n σ i = i ↔ i ∈ wexSet n σ := by
  constructor
  · intro h
    rw [← h]
    exact root_mem n σ i
  · intro h
    exact root_eq_self n σ i h

private noncomputable def mins {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.image fun a =>
    (P.part a).min' (P.part_nonempty.mpr (Finset.mem_univ a))

private noncomputable def maxs {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ.image fun a =>
    (P.part a).max' (P.part_nonempty.mpr (Finset.mem_univ a))

private theorem mem_mins_iff {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n} :
    m ∈ mins P ↔ ∃ t ∈ P.parts, m ∈ t ∧ ∀ x ∈ t, m ≤ x := by
  constructor
  · intro h
    rw [mins, Finset.mem_image] at h
    obtain ⟨a, _, rfl⟩ := h
    refine ⟨P.part a, P.part_mem.mpr (Finset.mem_univ a), ?_, ?_⟩
    · exact Finset.min'_mem _ _
    · intro x hx
      exact Finset.min'_le _ _ hx
  · intro h
    obtain ⟨t, ht, hm, hle⟩ := h
    have hpart : P.part m = t := P.part_eq_of_mem ht hm
    have hmin : (P.part m).min' (P.part_nonempty.mpr (Finset.mem_univ m)) = m := by
      subst hpart
      apply le_antisymm
      · exact Finset.min'_le _ _ hm
      · have hmem : (P.part m).min' (P.part_nonempty.mpr (Finset.mem_univ m)) ∈
            P.part m :=
          Finset.min'_mem _ _
        exact hle _ hmem
    rw [mins, Finset.mem_image]
    exact ⟨m, Finset.mem_univ m, hmin⟩

private theorem mem_maxs_iff {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n} :
    m ∈ maxs P ↔ ∃ t ∈ P.parts, m ∈ t ∧ ∀ x ∈ t, x ≤ m := by
  constructor
  · intro h
    rw [maxs, Finset.mem_image] at h
    obtain ⟨a, _, rfl⟩ := h
    refine ⟨P.part a, P.part_mem.mpr (Finset.mem_univ a), ?_, ?_⟩
    · exact Finset.max'_mem _ _
    · intro x hx
      exact Finset.le_max' _ _ hx
  · intro h
    obtain ⟨t, ht, hm, hle⟩ := h
    have hpart : P.part m = t := P.part_eq_of_mem ht hm
    have hmax : (P.part m).max' (P.part_nonempty.mpr (Finset.mem_univ m)) = m := by
      subst hpart
      apply le_antisymm
      · have hmem : (P.part m).max' (P.part_nonempty.mpr (Finset.mem_univ m)) ∈
            P.part m :=
          Finset.max'_mem _ _
        exact hle _ hmem
      · exact Finset.le_max' _ _ hm
    rw [maxs, Finset.mem_image]
    exact ⟨m, Finset.mem_univ m, hmax⟩

private theorem card_mins_eq {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (mins P).card = P.parts.card := by
  have himg : (mins P).image (fun m => P.part m) = P.parts := by
    ext t
    simp only [Finset.mem_image]
    constructor
    · intro h
      obtain ⟨m, hm, rfl⟩ := h
      have hmU : m ∈ (Finset.univ : Finset (Fin n)) :=
        Finset.mem_univ m
      exact P.part_mem.mpr hmU
    · intro ht
      have hne : t.Nonempty := P.nonempty_of_mem_parts ht
      have hm : t.min' hne ∈ mins P := by
        rw [mem_mins_iff]
        exact ⟨t, ht, Finset.min'_mem _ _, fun x hx => Finset.min'_le _ _ hx⟩
      refine ⟨t.min' hne, hm, ?_⟩
      exact P.part_eq_of_mem ht (Finset.min'_mem _ _)
  have hinj : Set.InjOn (fun m => P.part m) (mins P) := by
    intro m1 hm1 m2 hm2 hEq
    rw [Finset.mem_coe] at hm1 hm2
    rw [mem_mins_iff] at hm1 hm2
    obtain ⟨t1, ht1, hmem1, hle1⟩ := hm1
    obtain ⟨t2, ht2, hmem2, hle2⟩ := hm2
    have hp1 : P.part m1 = t1 := P.part_eq_of_mem ht1 hmem1
    have hp2 : P.part m2 = t2 := P.part_eq_of_mem ht2 hmem2
    have htEq : t1 = t2 := hp1.symm.trans (hEq.trans hp2)
    subst htEq
    apply le_antisymm
    · exact hle1 m2 hmem2
    · exact hle2 m1 hmem1
  have hcard := Finset.card_image_of_injOn hinj
  rw [himg] at hcard
  exact hcard.symm

private theorem card_maxs_eq {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (maxs P).card = P.parts.card := by
  have himg : (maxs P).image (fun m => P.part m) = P.parts := by
    ext t
    simp only [Finset.mem_image]
    constructor
    · intro h
      obtain ⟨m, hm, rfl⟩ := h
      have hmU : m ∈ (Finset.univ : Finset (Fin n)) :=
        Finset.mem_univ m
      exact P.part_mem.mpr hmU
    · intro ht
      have hne : t.Nonempty := P.nonempty_of_mem_parts ht
      have hm : t.max' hne ∈ maxs P := by
        rw [mem_maxs_iff]
        exact ⟨t, ht, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx⟩
      refine ⟨t.max' hne, hm, ?_⟩
      exact P.part_eq_of_mem ht (Finset.max'_mem _ _)
  have hinj : Set.InjOn (fun m => P.part m) (maxs P) := by
    intro m1 hm1 m2 hm2 hEq
    rw [Finset.mem_coe] at hm1 hm2
    rw [mem_maxs_iff] at hm1 hm2
    obtain ⟨t1, ht1, hmem1, hle1⟩ := hm1
    obtain ⟨t2, ht2, hmem2, hle2⟩ := hm2
    have hp1 : P.part m1 = t1 := P.part_eq_of_mem ht1 hmem1
    have hp2 : P.part m2 = t2 := P.part_eq_of_mem ht2 hmem2
    have htEq : t1 = t2 := hp1.symm.trans (hEq.trans hp2)
    subst htEq
    apply le_antisymm
    · exact hle2 m1 hmem1
    · exact hle1 m2 hmem2
  have hcard := Finset.card_image_of_injOn hinj
  rw [himg] at hcard
  exact hcard.symm

private theorem wexSet_eq_mins_toPart (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    wexSet n σ = mins (toPart n σ) := by
  ext m
  rw [mem_mins_iff]
  constructor
  · intro hm
    have hroot : root n σ m = m := root_eq_self n σ m hm
    refine ⟨(toPart n σ).part m, (toPart n σ).part_mem.mpr (Finset.mem_univ m),
      (toPart n σ).mem_part (Finset.mem_univ m), ?_⟩
    intro x hx
    rw [mem_toPart_iff] at hx
    have hle : root n σ x ≤ x := root_le n σ x
    calc m = root n σ m := hroot.symm
      _ = root n σ x := hx
      _ ≤ x := hle
  · intro h
    obtain ⟨t, ht, hmem, hle⟩ := h
    have hroot_eq : root n σ m = m := by
      have hne : t.Nonempty := (toPart n σ).nonempty_of_mem_parts ht
      obtain ⟨a, ha⟩ := hne
      have hpartEq : (toPart n σ).part a = t :=
        (toPart n σ).part_eq_of_mem ht ha
      have hrootA_mem : root n σ a ∈ t := by
        have hmem2 : root n σ a ∈ (toPart n σ).part a := by
          rw [mem_toPart_iff]
          exact (root_idem n σ a).symm
        rw [hpartEq] at hmem2
        exact hmem2
      have hle_root := hle _ hrootA_mem
      have hroot_m_eq : root n σ m = root n σ a := by
        have hm_part : m ∈ (toPart n σ).part a := by
          rw [hpartEq]
          exact hmem
        rw [mem_toPart_iff] at hm_part
        exact hm_part.symm
      have hle_m : root n σ m ≤ m := root_le n σ m
      have hge : m ≤ root n σ m := hroot_m_eq.symm ▸ hle_root
      exact le_antisymm hle_m hge
    exact root_eq_self_iff.mp hroot_eq

private noncomputable def pred {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (u : Fin n)
    (hu : u ∉ mins P) : Fin n :=
  ((P.part u).filter (fun x => x < u)).max'
    (by
      have hpart_mem : P.part u ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u)
      have hne : (P.part u).Nonempty := P.nonempty_of_mem_parts hpart_mem
      have hmin_mem : (P.part u).min' hne ∈ P.part u := Finset.min'_mem _ _
      have hmin_le : ∀ x ∈ P.part u, (P.part u).min' hne ≤ x :=
        fun x hx => Finset.min'_le _ _ hx
      have hmin_eq : (P.part u).min' hne ∈ mins P := by
        rw [mem_mins_iff]
        exact ⟨P.part u, hpart_mem, hmin_mem, hmin_le⟩
      have hne_min : (P.part u).min' hne ≠ u := fun h => hu (h ▸ hmin_eq)
      have hlt : (P.part u).min' hne < u :=
        lt_of_le_of_ne (hmin_le u (P.mem_part (Finset.mem_univ u))) hne_min
      exact ⟨(P.part u).min' hne, Finset.mem_filter.mpr ⟨hmin_mem, hlt⟩⟩)

private theorem pred_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : pred P u hu ∈ P.part u := by
  have hmem : pred P u hu ∈ (P.part u).filter (fun x => x < u) := by
    unfold pred
    exact Finset.max'_mem _ _
  exact Finset.mem_of_mem_filter _ hmem

private theorem pred_lt {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : pred P u hu < u := by
  have hmem : pred P u hu ∈ (P.part u).filter (fun x => x < u) := by
    unfold pred
    exact Finset.max'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

private theorem le_pred_of_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u x : Fin n}
    (hu : u ∉ mins P) (hxB : x ∈ P.part u) (hxu : x < u) :
    x ≤ pred P u hu := by
  have hmem : x ∈ (P.part u).filter (fun y => y < u) :=
    Finset.mem_filter.mpr ⟨hxB, hxu⟩
  unfold pred
  exact Finset.le_max' _ _ hmem

private noncomputable def succ {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (y : Fin n)
    (hy : y ∉ maxs P) : Fin n :=
  ((P.part y).filter (fun x => y < x)).min'
    (by
      have hpart_mem : P.part y ∈ P.parts := P.part_mem.mpr (Finset.mem_univ y)
      have hne : (P.part y).Nonempty := P.nonempty_of_mem_parts hpart_mem
      have hmax_mem : (P.part y).max' hne ∈ P.part y := Finset.max'_mem _ _
      have hmax_le : ∀ x ∈ P.part y, x ≤ (P.part y).max' hne :=
        fun x hx => Finset.le_max' _ _ hx
      have hmax_eq : (P.part y).max' hne ∈ maxs P := by
        rw [mem_maxs_iff]
        exact ⟨P.part y, hpart_mem, hmax_mem, hmax_le⟩
      have hne_max : (P.part y).max' hne ≠ y := fun h => hy (h ▸ hmax_eq)
      have hlt : y < (P.part y).max' hne :=
        lt_of_le_of_ne (hmax_le y (P.mem_part (Finset.mem_univ y))) (Ne.symm hne_max)
      exact ⟨(P.part y).max' hne, Finset.mem_filter.mpr ⟨hmax_mem, hlt⟩⟩)

private theorem succ_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) : succ P y hy ∈ P.part y := by
  have hmem : succ P y hy ∈ (P.part y).filter (fun x => y < x) := by
    unfold succ
    exact Finset.min'_mem _ _
  exact Finset.mem_of_mem_filter _ hmem

private theorem lt_succ {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) : y < succ P y hy := by
  have hmem : succ P y hy ∈ (P.part y).filter (fun x => y < x) := by
    unfold succ
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

private theorem succ_le_of_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y x : Fin n}
    (hy : y ∉ maxs P) (hxB : x ∈ P.part y) (hyx : y < x) :
    succ P y hy ≤ x := by
  have hmem : x ∈ (P.part y).filter (fun z => y < z) :=
    Finset.mem_filter.mpr ⟨hxB, hyx⟩
  unfold succ
  exact Finset.min'_le _ _ hmem

private theorem succ_not_mem_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) : succ P y hy ∉ mins P := by
  intro hmem
  rw [mem_mins_iff] at hmem
  obtain ⟨t, ht, hmem2, hle⟩ := hmem
  have hsucc_mem : succ P y hy ∈ P.part y := succ_mem hy
  have hpart_eq : P.part (succ P y hy) = P.part y := by
    have h1 : P.part (succ P y hy) ∈ P.parts :=
      P.part_mem.mpr (Finset.mem_univ _)
    have h2 : P.part y ∈ P.parts := P.part_mem.mpr (Finset.mem_univ y)
    exact P.eq_of_mem_parts h1 h2
      (P.mem_part (Finset.mem_univ _)) hsucc_mem
  have ht_eq : t = P.part y := by
    have h1 : P.part (succ P y hy) = t :=
      P.part_eq_of_mem ht hmem2
    rw [hpart_eq] at h1
    exact h1.symm
  subst ht_eq
  have hne : (P.part y).Nonempty := P.part_nonempty.mpr (Finset.mem_univ y)
  have hmin_le : succ P y hy ≤ (P.part y).min' hne := by
    have hmem_min : (P.part y).min' hne ∈ P.part y := Finset.min'_mem _ _
    exact hle _ hmem_min
  have hmin_lt : (P.part y).min' hne < succ P y hy := by
    have hle_min : (P.part y).min' hne ≤ y := by
      have hy_mem : y ∈ P.part y := P.mem_part (Finset.mem_univ y)
      exact Finset.min'_le _ _ hy_mem
    have hlt : y < succ P y hy := lt_succ hy
    exact lt_of_le_of_lt hle_min hlt
  exact absurd hmin_le (not_le_of_gt hmin_lt)

private theorem pred_succ_eq {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) :
    pred P (succ P y hy) (succ_not_mem_mins hy) = y := by
  have hsucc_mem : succ P y hy ∈ P.part y := succ_mem hy
  have hpart_eq : P.part (succ P y hy) = P.part y := by
    have h1 : P.part (succ P y hy) ∈ P.parts :=
      P.part_mem.mpr (Finset.mem_univ _)
    have h2 : P.part y ∈ P.parts := P.part_mem.mpr (Finset.mem_univ y)
    exact P.eq_of_mem_parts h1 h2
      (P.mem_part (Finset.mem_univ _)) hsucc_mem
  have hy_mem_part_succ : y ∈ P.part (succ P y hy) := by
    rw [hpart_eq]
    exact P.mem_part (Finset.mem_univ y)
  have hlt_y : y < succ P y hy := lt_succ hy
  have hle1 : y ≤ pred P (succ P y hy) (succ_not_mem_mins hy) := by
    apply le_pred_of_mem _ hy_mem_part_succ hlt_y
  have hle2 : pred P (succ P y hy) (succ_not_mem_mins hy) ≤ y := by
    have hpred_mem : pred P (succ P y hy) (succ_not_mem_mins hy) ∈
        P.part (succ P y hy) :=
      pred_mem _
    have hpred_lt : pred P (succ P y hy) (succ_not_mem_mins hy) < succ P y hy :=
      pred_lt _
    rw [hpart_eq] at hpred_mem
    rcases lt_trichotomy (pred P (succ P y hy) (succ_not_mem_mins hy)) y with
      hlt | heq | hgt
    · exact le_of_lt hlt
    · exact le_of_eq heq
    · have hsucc_le : succ P y hy ≤ pred P (succ P y hy) (succ_not_mem_mins hy) := by
        apply succ_le_of_mem hy hpred_mem hgt
      have hcontra : succ P y hy < succ P y hy :=
        lt_of_le_of_lt hsucc_le hpred_lt
      exact absurd hcontra (lt_irrefl _)
  exact le_antisymm hle2 hle1

private theorem pred_injective {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))}
    {u1 u2 : Fin n} {hu1 : u1 ∉ mins P} {hu2 : u2 ∉ mins P}
    (hEq : pred P u1 hu1 = pred P u2 hu2) : u1 = u2 := by
  have hB1mem : P.part u1 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u1)
  have hB2mem : P.part u2 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u2)
  have hpred1_mem : pred P u1 hu1 ∈ P.part u1 := pred_mem hu1
  have hpred2_mem : pred P u2 hu2 ∈ P.part u2 := pred_mem hu2
  have hBeq : P.part u1 = P.part u2 := by
    have hmem1 : pred P u1 hu1 ∈ P.part u1 := hpred1_mem
    have hmem2 : pred P u1 hu1 ∈ P.part u2 := hEq ▸ hpred2_mem
    exact P.eq_of_mem_parts hB1mem hB2mem hmem1 hmem2
  have hu1_mem : u1 ∈ P.part u2 := by
    rw [← hBeq]
    exact P.mem_part (Finset.mem_univ u1)
  have hu2_mem : u2 ∈ P.part u1 := by
    rw [hBeq]
    exact P.mem_part (Finset.mem_univ u2)
  rcases lt_trichotomy u1 u2 with hlt | heq | hgt
  · have hle : u1 ≤ pred P u2 hu2 :=
      le_pred_of_mem hu2 hu1_mem hlt
    have hlt2 : pred P u1 hu1 < u1 := pred_lt hu1
    rw [hEq] at hlt2
    exact absurd (lt_of_lt_of_le hlt2 hle) (lt_irrefl _)
  · exact heq
  · have hle : u2 ≤ pred P u1 hu1 :=
      le_pred_of_mem hu1 hu2_mem hgt
    have hlt2 : pred P u2 hu2 < u2 := pred_lt hu2
    rw [← hEq] at hlt2
    exact absurd (lt_of_lt_of_le hlt2 hle) (lt_irrefl _)

private theorem pred_not_mem_maxs {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : pred P u hu ∉ maxs P := by
  intro hmem
  rw [mem_maxs_iff] at hmem
  obtain ⟨t, ht, hmem2, hle⟩ := hmem
  have hpred_mem : pred P u hu ∈ P.part u := pred_mem hu
  have hpart_mem : P.part u ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u)
  have htEq : t = P.part u := by
    have h1 : P.part (pred P u hu) = t :=
      P.part_eq_of_mem ht hmem2
    have h2 : P.part (pred P u hu) = P.part u := by
      have h1' : P.part (pred P u hu) ∈ P.parts :=
        P.part_mem.mpr (Finset.mem_univ _)
      exact P.eq_of_mem_parts h1' hpart_mem
        (P.mem_part (Finset.mem_univ _)) hpred_mem
    rw [h2] at h1
    exact h1.symm
  subst htEq
  have hu_le : u ≤ pred P u hu := hle u (P.mem_part (Finset.mem_univ u))
  have hlt : pred P u hu < u := pred_lt hu
  exact absurd hu_le (not_le_of_gt hlt)

private noncomputable def minOfBlock {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (x : Fin n) : Fin n :=
  (P.part x).min' (P.part_nonempty.mpr (Finset.mem_univ x))

private theorem minOfBlock_mem_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x : Fin n} :
    minOfBlock P x ∈ mins P := by
  rw [mem_mins_iff]
  refine ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x), ?_, ?_⟩
  · unfold minOfBlock
    exact Finset.min'_mem _ _
  · intro y hy
    unfold minOfBlock
    exact Finset.min'_le _ _ hy

private theorem minOfBlock_le {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x : Fin n} :
    minOfBlock P x ≤ x := by
  unfold minOfBlock
  exact Finset.min'_le _ _ (P.mem_part (Finset.mem_univ x))

private theorem maxs_le_mins_card {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (t : Fin n) :
    ((maxs P).filter (fun x => x ≤ t)).card ≤
      ((mins P).filter (fun m => m ≤ t)).card := by
  have hmaps : Set.MapsTo (minOfBlock P)
      ((maxs P).filter (fun x => x ≤ t)) ((mins P).filter (fun m => m ≤ t)) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    obtain ⟨hxmax, hxt⟩ := hx
    constructor
    · exact minOfBlock_mem_mins
    · exact le_trans (minOfBlock_le) hxt
  have hinj : Set.InjOn (minOfBlock P) ((maxs P).filter (fun x => x ≤ t)) := by
    intro x1 hx1 x2 hx2 hEq
    rw [Finset.mem_coe, Finset.mem_filter] at hx1 hx2
    obtain ⟨hx1max, -⟩ := hx1
    obtain ⟨hx2max, -⟩ := hx2
    rw [mem_maxs_iff] at hx1max hx2max
    obtain ⟨t1, ht1, hmem1, hle1⟩ := hx1max
    obtain ⟨t2, ht2, hmem2, hle2⟩ := hx2max
    have hpart1 : P.part x1 = t1 := P.part_eq_of_mem ht1 hmem1
    have hpart2 : P.part x2 = t2 := P.part_eq_of_mem ht2 hmem2
    have hmin1_mem : minOfBlock P x1 ∈ P.part x1 := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    have hmin2_mem : minOfBlock P x2 ∈ P.part x2 := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    have htEq : t1 = t2 := by
      have h1 : P.part x1 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ x1)
      have h2 : P.part x2 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ x2)
      have hmem1' : minOfBlock P x1 ∈ P.part x1 := hmin1_mem
      have hmem2' : minOfBlock P x1 ∈ P.part x2 := hEq ▸ hmin2_mem
      have hpeq : P.part x1 = P.part x2 :=
        P.eq_of_mem_parts h1 h2 hmem1' hmem2'
      rw [hpart1, hpart2] at hpeq
      exact hpeq
    subst htEq
    apply le_antisymm
    · exact hle2 x1 hmem1
    · exact hle1 x2 hmem2
  exact Finset.card_le_card_of_injOn _ hmaps hinj

private theorem interlacing {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    ∀ i : Fin P.parts.card,
      (mins P).orderEmbOfFin (card_mins_eq P) i ≤
        (maxs P).orderEmbOfFin (card_maxs_eq P) i := by
  intro i
  by_contra hlt
  have hgt : (maxs P).orderEmbOfFin (card_maxs_eq P) i <
      (mins P).orderEmbOfFin (card_mins_eq P) i :=
    lt_of_not_ge hlt
  set t : Fin n := (maxs P).orderEmbOfFin (card_maxs_eq P) i with ht
  have hdom := maxs_le_mins_card P t
  -- lower bound for maxs filter via Iic i
  have hmaps_max : Set.MapsTo ((maxs P).orderEmbOfFin (card_maxs_eq P))
      (Finset.Iic i) ((maxs P).filter (fun x => x ≤ t)) := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_Iic] at hj
    rw [Finset.mem_coe, Finset.mem_filter]
    constructor
    · exact Finset.orderEmbOfFin_mem _ _ _
    · have hle : j ≤ i := hj
      have hmono : (maxs P).orderEmbOfFin (card_maxs_eq P) j ≤
          (maxs P).orderEmbOfFin (card_maxs_eq P) i :=
        (OrderEmbedding.monotone _ hle)
      rw [ht]
      exact hmono
  have hinj_max : Set.InjOn ((maxs P).orderEmbOfFin (card_maxs_eq P))
      (Finset.Iic i) := by
    intro j1 hj1 j2 hj2 hEq
    have hle1 : j1 ≤ j2 := by
      have hle : (maxs P).orderEmbOfFin (card_maxs_eq P) j1 ≤
          (maxs P).orderEmbOfFin (card_maxs_eq P) j2 := le_of_eq hEq
      exact ((maxs P).orderEmbOfFin (card_maxs_eq P)).le_iff_le.mp hle
    have hle2 : j2 ≤ j1 := by
      have hle : (maxs P).orderEmbOfFin (card_maxs_eq P) j2 ≤
          (maxs P).orderEmbOfFin (card_maxs_eq P) j1 := le_of_eq hEq.symm
      exact ((maxs P).orderEmbOfFin (card_maxs_eq P)).le_iff_le.mp hle
    exact le_antisymm hle1 hle2
  have hcard_ge : (Finset.Iic i).card ≤
      ((maxs P).filter (fun x => x ≤ t)).card :=
    Finset.card_le_card_of_injOn _ hmaps_max hinj_max
  -- upper bound: filter_min ⊆ image eM (Iio i)
  have hsub_min : (mins P).filter (fun m => m ≤ t) ⊆
      (Finset.Iio i).image ((mins P).orderEmbOfFin (card_mins_eq P)) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmM, hmt⟩ := hm
    have ht_lt : t < (mins P).orderEmbOfFin (card_mins_eq P) i := by
      rw [ht]
      exact hgt
    have hm_lt : m < (mins P).orderEmbOfFin (card_mins_eq P) i :=
      lt_of_le_of_lt hmt ht_lt
    have hj : ∃ j : Fin P.parts.card,
        j ∈ Finset.Iio i ∧
          (mins P).orderEmbOfFin (card_mins_eq P) j = m := by
      have hmem : m ∈ mins P := hmM
      refine ⟨((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩, ?_, ?_⟩
      · rw [Finset.mem_Iio]
        have heq : (mins P).orderEmbOfFin (card_mins_eq P)
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) = m := by
          have h1 : ((mins P).orderIsoOfFin (card_mins_eq P))
              (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) =
              ⟨m, hmem⟩ :=
            OrderIso.apply_symm_apply _ _
          have h2 : ↑(((mins P).orderIsoOfFin (card_mins_eq P))
              (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩)) = m := by
            rw [h1]
          rw [Finset.coe_orderIsoOfFin_apply] at h2
          exact h2
        have hlt : (mins P).orderEmbOfFin (card_mins_eq P)
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) <
            (mins P).orderEmbOfFin (card_mins_eq P) i := by
          rw [heq]
          exact hm_lt
        exact ((mins P).orderEmbOfFin (card_mins_eq P)).lt_iff_lt.mp hlt
      · have h1 : ((mins P).orderIsoOfFin (card_mins_eq P))
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩) =
            ⟨m, hmem⟩ :=
          OrderIso.apply_symm_apply _ _
        have h2 : ↑(((mins P).orderIsoOfFin (card_mins_eq P))
            (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hmem⟩)) = m := by
          rw [h1]
        rw [Finset.coe_orderIsoOfFin_apply] at h2
        exact h2
    obtain ⟨j, hjIio, heq⟩ := hj
    rw [Finset.mem_image]
    exact ⟨j, hjIio, heq⟩
  have hinj_min : Set.InjOn ((mins P).orderEmbOfFin (card_mins_eq P))
      (Finset.Iio i) := by
    intro j1 hj1 j2 hj2 hEq
    have hle1 : j1 ≤ j2 := by
      have hle : (mins P).orderEmbOfFin (card_mins_eq P) j1 ≤
          (mins P).orderEmbOfFin (card_mins_eq P) j2 := le_of_eq hEq
      exact ((mins P).orderEmbOfFin (card_mins_eq P)).le_iff_le.mp hle
    have hle2 : j2 ≤ j1 := by
      have hle : (mins P).orderEmbOfFin (card_mins_eq P) j2 ≤
          (mins P).orderEmbOfFin (card_mins_eq P) j1 := le_of_eq hEq.symm
      exact ((mins P).orderEmbOfFin (card_mins_eq P)).le_iff_le.mp hle
    exact le_antisymm hle1 hle2
  have hcard_image : ((Finset.Iio i).image
      ((mins P).orderEmbOfFin (card_mins_eq P))).card = (Finset.Iio i).card :=
    Finset.card_image_of_injOn hinj_min
  have hcard_le : ((mins P).filter (fun m => m ≤ t)).card ≤
      (Finset.Iio i).card := by
    calc ((mins P).filter (fun m => m ≤ t)).card ≤
          ((Finset.Iio i).image
            ((mins P).orderEmbOfFin (card_mins_eq P))).card :=
          Finset.card_le_card hsub_min
      _ = (Finset.Iio i).card := hcard_image
  have hIic : (Finset.Iic i).card = i.val + 1 := by simp
  have hIio : (Finset.Iio i).card = i.val := by simp
  omega

private noncomputable def ofPartFun {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Fin n → Fin n :=
  fun u =>
    if h : u ∈ mins P then
      (maxs P).orderEmbOfFin (card_maxs_eq P)
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, h⟩)
    else pred P u h

private theorem ofPartFun_mem_maxs {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n}
    (hm : m ∈ mins P) :
    ofPartFun P m ∈ maxs P := by
  unfold ofPartFun
  simp [hm]

private theorem ofPartFun_eq_pred {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : ofPartFun P u = pred P u hu := by
  unfold ofPartFun
  simp [hu]

private theorem ofPartFun_eq_ofMem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∈ mins P) : ofPartFun P u =
      (maxs P).orderEmbOfFin (card_maxs_eq P)
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩) := by
  unfold ofPartFun
  simp only [hu, dite_true]

private theorem ofPartFun_injective {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Function.Injective (ofPartFun P) := by
  intro a b hab
  by_cases ha : a ∈ mins P <;> by_cases hb : b ∈ mins P
  · rw [ofPartFun_eq_ofMem ha, ofPartFun_eq_ofMem hb] at hab
    have hIdx := ((maxs P).orderEmbOfFin (card_maxs_eq P)).injective hab
    have hSub := ((mins P).orderIsoOfFin (card_mins_eq P)).symm.injective hIdx
    exact Subtype.ext_iff.mp hSub
  · have haX : ofPartFun P a ∈ maxs P := ofPartFun_mem_maxs ha
    have hbX : ofPartFun P b ∉ maxs P := by
      rw [ofPartFun_eq_pred hb]
      exact pred_not_mem_maxs hb
    rw [hab] at haX
    exact absurd haX hbX
  · have haX : ofPartFun P a ∉ maxs P := by
      rw [ofPartFun_eq_pred ha]
      exact pred_not_mem_maxs ha
    have hbX : ofPartFun P b ∈ maxs P := ofPartFun_mem_maxs hb
    rw [← hab] at hbX
    exact absurd hbX haX
  · rw [ofPartFun_eq_pred ha, ofPartFun_eq_pred hb] at hab
    exact pred_injective hab

private noncomputable def ofPartPerm {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (ofPartFun P) (ofPartFun_injective P).bijective_of_finite

private theorem ofPartPerm_apply {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n} :
    ofPartPerm P u = ofPartFun P u := rfl

private theorem orderEmb_symm_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∈ mins P) :
    (mins P).orderEmbOfFin (card_mins_eq P)
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩) = u := by
  have h1 : ((mins P).orderIsoOfFin (card_mins_eq P))
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩) =
        ⟨u, hu⟩ :=
    OrderIso.apply_symm_apply _ _
  have h2 : ↑(((mins P).orderIsoOfFin (card_mins_eq P))
        (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨u, hu⟩)) = u := by
    rw [h1]
  rw [Finset.coe_orderIsoOfFin_apply] at h2
  exact h2

private theorem ofPartPerm_le_ofMem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n}
    (hm : m ∈ mins P) : m ≤ ofPartPerm P m := by
  rw [ofPartPerm_apply, ofPartFun_eq_ofMem hm]
  calc m = (mins P).orderEmbOfFin (card_mins_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hm⟩) :=
          (orderEmb_symm_mins hm).symm
    _ ≤ (maxs P).orderEmbOfFin (card_maxs_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨m, hm⟩) :=
          interlacing P _

private theorem mem_wexSet_ofPartPerm_iff {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n} :
    u ∈ wexSet n (ofPartPerm P) ↔ u ∈ mins P := by
  constructor
  · intro h
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
    by_contra hu
    have hlt : ofPartPerm P u < u := by
      rw [ofPartPerm_apply, ofPartFun_eq_pred hu]
      exact pred_lt hu
    exact absurd h (not_le_of_gt hlt)
  · intro h
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ofPartPerm_le_ofMem h

private theorem ofPartPerm_valid {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    ∀ i j : Fin n, i < j → i ≤ ofPartPerm P i → j ≤ ofPartPerm P j →
      ofPartPerm P i < ofPartPerm P j := by
  intro i j hij hi hj
  have hiM : i ∈ mins P := by
    have hmem : i ∈ wexSet n (ofPartPerm P) := by
      simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    exact (mem_wexSet_ofPartPerm_iff).mp hmem
  have hjM : j ∈ mins P := by
    have hmem : j ∈ wexSet n (ofPartPerm P) := by
      simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    exact (mem_wexSet_ofPartPerm_iff).mp hmem
  simp only [ofPartPerm_apply, ofPartFun_eq_ofMem hiM, ofPartFun_eq_ofMem hjM]
  have hIdx : ((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨i, hiM⟩ <
      ((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨j, hjM⟩ := by
    have hEmb : (mins P).orderEmbOfFin (card_mins_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨i, hiM⟩) <
        (mins P).orderEmbOfFin (card_mins_eq P)
          (((mins P).orderIsoOfFin (card_mins_eq P)).symm ⟨j, hjM⟩) := by
      rw [orderEmb_symm_mins hiM, orderEmb_symm_mins hjM]
      exact hij
    exact ((mins P).orderEmbOfFin (card_mins_eq P)).lt_iff_lt.mp hEmb
  exact ((maxs P).orderEmbOfFin (card_maxs_eq P)).strictMono hIdx

private theorem find_pos_of_notMem {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {i : Fin n} (hi : i ∉ wexSet n σ) :
    0 < Nat.find (exists_hit n σ i) := by
  by_contra h
  push Not at h
  have h0 : Nat.find (exists_hit n σ i) = 0 := by omega
  have hspec := Nat.find_spec (exists_hit n σ i)
  rw [h0] at hspec
  have hmem : i ∈ wexSet n σ := by simpa using hspec
  exact hi hmem

private theorem pow_apply_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n)
    (m : ℕ) : ⇑(σ ^ m) (⇑σ i) = ⇑(σ ^ (m + 1)) i := by
  rw [pow_succ]
  rfl

private theorem root_step {n : ℕ} {σ : Equiv.Perm (Fin n)} {i : Fin n}
    (hi : i ∉ wexSet n σ) : root n σ i = root n σ (⇑σ i) := by
  unfold root
  have hTpos := find_pos_of_notMem hi
  set T := Nat.find (exists_hit n σ i) with hT
  set S := Nat.find (exists_hit n σ (⇑σ i)) with hS
  have hmem : ⇑(σ ^ (T - 1)) (⇑σ i) ∈ wexSet n σ := by
    rw [pow_apply_succ, Nat.sub_add_cancel hTpos]
    exact Nat.find_spec (exists_hit n σ i)
  have hle1 : S ≤ T - 1 := Nat.find_min' _ hmem
  have hle2 : T - 1 ≤ S := by
    by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec (exists_hit n σ (⇑σ i))
    rw [pow_apply_succ] at hspec
    have hmin := Nat.find_min (exists_hit n σ i) (by omega : S + 1 < T)
    exact hmin hspec
  have hEq : S = T - 1 := le_antisymm hle1 hle2
  have hT : T = S + 1 := by omega
  rw [hT, ← pow_apply_succ]

private theorem min'_congr {α : Type*} [LinearOrder α] {s t : Finset α}
    (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst h
  rfl

private theorem minOfBlock_eq_of_mem_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∈ mins P) : minOfBlock P u = u := by
  rw [mem_mins_iff] at hu
  obtain ⟨t, ht, hmem, hle⟩ := hu
  have hpart : P.part u = t := P.part_eq_of_mem ht hmem
  have hmin : t.min' (P.nonempty_of_mem_parts ht) = u := by
    apply le_antisymm
    · exact Finset.min'_le _ _ hmem
    · exact hle _ (Finset.min'_mem _ _)
  have hEq : minOfBlock P u = t.min' (P.nonempty_of_mem_parts ht) := by
    unfold minOfBlock
    exact min'_congr hpart _ _
  rw [hEq]
  exact hmin

private theorem part_eq_of_mem_part {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x y : Fin n}
    (h : y ∈ P.part x) : P.part y = P.part x :=
  P.eq_of_mem_parts (P.part_mem.mpr (Finset.mem_univ y))
    (P.part_mem.mpr (Finset.mem_univ x)) (P.mem_part (Finset.mem_univ y)) h

private theorem minOfBlock_eq_of_mem_part {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {x y : Fin n}
    (h : y ∈ P.part x) : minOfBlock P y = minOfBlock P x := by
  have hEq := part_eq_of_mem_part h
  unfold minOfBlock
  exact min'_congr hEq _ _

private theorem minOfBlock_eq_iff_part_eq {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {a b : Fin n} :
    minOfBlock P a = minOfBlock P b ↔ P.part a = P.part b := by
  constructor
  · intro h
    have ha : minOfBlock P a ∈ P.part a := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    have hb : minOfBlock P b ∈ P.part b := by
      unfold minOfBlock
      exact Finset.min'_mem _ _
    rw [h] at ha
    exact P.eq_of_mem_parts (P.part_mem.mpr (Finset.mem_univ a))
      (P.part_mem.mpr (Finset.mem_univ b)) ha hb
  · intro h
    unfold minOfBlock
    exact min'_congr h _ _

private theorem root_ofPart_eq_minOfBlock {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (u : Fin n) :
    root n (ofPartPerm P) u = minOfBlock P u := by
  have h : ∀ v : ℕ, ∀ w : Fin n, w.val = v →
      root n (ofPartPerm P) w = minOfBlock P w := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro w hw
      by_cases hwM : w ∈ mins P
      · have hwW : w ∈ wexSet n (ofPartPerm P) :=
          mem_wexSet_ofPartPerm_iff.mpr hwM
        rw [root_eq_self _ _ _ hwW, minOfBlock_eq_of_mem_mins hwM]
      · have hwW : w ∉ wexSet n (ofPartPerm P) := fun h =>
          hwM (mem_wexSet_ofPartPerm_iff.mp h)
        have hEq : ofPartPerm P w = pred P w hwM := by
          rw [ofPartPerm_apply, ofPartFun_eq_pred hwM]
        have hlt : ofPartPerm P w < w := hEq ▸ pred_lt hwM
        have hval : (ofPartPerm P w).val < v := by
          have hltV : (ofPartPerm P w).val < w.val := hlt
          omega
        have hIH := ih (ofPartPerm P w).val hval (ofPartPerm P w) rfl
        have hmem : ofPartPerm P w ∈ P.part w := hEq ▸ pred_mem hwM
        have hminEq := minOfBlock_eq_of_mem_part hmem
        calc root n (ofPartPerm P) w
            = root n (ofPartPerm P) (⇑(ofPartPerm P) w) := root_step hwW
          _ = minOfBlock P w := by rw [hIH]; exact hminEq
  exact h u.val u rfl

private theorem part_eq_toPart_ofPartPerm {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (a : Fin n) :
    (toPart n (ofPartPerm P)).part a = P.part a := by
  ext b
  rw [mem_toPart_iff, root_ofPart_eq_minOfBlock, root_ofPart_eq_minOfBlock,
    minOfBlock_eq_iff_part_eq]
  exact eq_comm.trans
    (P.mem_part_iff_part_eq_part (Finset.mem_univ b)
      (Finset.mem_univ a)).symm

private theorem toPart_ofPartPerm {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    toPart n (ofPartPerm P) = P := by
  apply finpartition_eq_of_parts_eq
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := (toPart n (ofPartPerm P)).nonempty_of_mem_parts ht
    have hEq := part_eq_toPart_ofPartPerm P a
    have hpart : (toPart n (ofPartPerm P)).part a = t :=
      (toPart n (ofPartPerm P)).part_eq_of_mem ht ha
    rw [hEq] at hpart
    rw [← hpart]
    exact P.part_mem.mpr (Finset.mem_univ a)
  · intro ht
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts ht
    have hEq := part_eq_toPart_ofPartPerm P a
    have hpart : P.part a = t := P.part_eq_of_mem ht ha
    have hQ : (toPart n (ofPartPerm P)).part a = t := hEq.trans hpart
    rw [← hQ]
    exact (toPart n (ofPartPerm P)).part_mem.mpr (Finset.mem_univ a)

private theorem pred_eq_of_injective {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (g : Fin n → Fin n)
    (hinj : Function.Injective g)
    (hmem : ∀ u : Fin n, u ∉ mins P → g u ∈ P.part u)
    (hlt : ∀ u : Fin n, u ∉ mins P → g u < u)
    (u : Fin n) (hu : u ∉ mins P) : g u = pred P u hu := by
  have h : ∀ v : ℕ, ∀ w : Fin n, w.val = v → ∀ hw : w ∉ mins P,
      g w = pred P w hw := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro w hw hwM
      have hle : g w ≤ pred P w hwM :=
        le_pred_of_mem hwM (hmem w hwM) (hlt w hwM)
      rcases lt_or_eq_of_le hle with hlt2 | hEq
      · have hgu : g w ∈ P.part w := hmem w hwM
        have hpartEq : P.part (g w) = P.part w :=
          part_eq_of_mem_part hgu
        have hy : g w ∉ maxs P := by
          intro hmax
          rw [mem_maxs_iff] at hmax
          obtain ⟨t, ht, hmem2, hle2⟩ := hmax
          have htEq : t = P.part w :=
            ((P.part_eq_of_mem ht hmem2).symm.trans hpartEq)
          have hmemP : pred P w hwM ∈ t := by
            rw [htEq]
            exact pred_mem hwM
          have hle3 : pred P w hwM ≤ g w := hle2 _ hmemP
          exact absurd hle3 (not_le_of_gt hlt2)
        have hpu : pred P w hwM ∈ P.part (g w) := by
          rw [hpartEq]
          exact pred_mem hwM
        set vv : Fin n := succ P (g w) hy with hvv
        have hleV : vv ≤ pred P w hwM := succ_le_of_mem hy hpu hlt2
        have hltV : vv < w :=
          lt_of_le_of_lt hleV (pred_lt hwM)
        have hvU : vv ∈ P.part w := by
          rw [← hpartEq]
          exact succ_mem hy
        have hvM : vv ∉ mins P := by
          intro hmemM
          have hEq1 : minOfBlock P vv = vv :=
            minOfBlock_eq_of_mem_mins hmemM
          have hEq2 : minOfBlock P vv = minOfBlock P w :=
            minOfBlock_eq_of_mem_part hvU
          have hleMin : minOfBlock P w ≤ g w := by
            unfold minOfBlock
            exact Finset.min'_le _ _ hgu
          have hvvEq : vv = minOfBlock P w := hEq1.symm.trans hEq2
          have hcon : vv ≤ g w := by
            rw [hvvEq]
            exact hleMin
          have hltS : g w < vv := lt_succ hy
          exact absurd hcon (not_le_of_gt hltS)
        have hval : vv.val < v := by
          have hltW : vv.val < w.val := hltV
          omega
        have hgv : g vv = pred P vv hvM := ih vv.val hval vv rfl hvM
        have hps : pred P vv hvM = g w := pred_succ_eq hy
        have hcon : g vv = g w := hgv.trans hps
        exact absurd (hinj hcon) (ne_of_lt hltV)
      · exact hEq
  exact h u.val u rfl hu

private theorem perm_eq_pred_of_notMem {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {u : Fin n} (hu : u ∉ mins (toPart n σ)) :
    ⇑σ u = pred (toPart n σ) u hu := by
  have hW : wexSet n σ = mins (toPart n σ) := wexSet_eq_mins_toPart n σ
  have hinj : Function.Injective ⇑σ := σ.injective
  have hmem : ∀ v : Fin n, v ∉ mins (toPart n σ) →
      ⇑σ v ∈ (toPart n σ).part v := by
    intro v hv
    have hvW : v ∉ wexSet n σ := fun h => hv (hW ▸ h)
    rw [mem_toPart_iff]
    exact root_step hvW
  have hlt : ∀ v : Fin n, v ∉ mins (toPart n σ) → ⇑σ v < v := by
    intro v hv
    have hvW : v ∉ wexSet n σ := fun h => hv (hW ▸ h)
    simp only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvW
    exact lt_of_not_ge hvW
  exact pred_eq_of_injective (toPart n σ) ⇑σ hinj hmem hlt u hu

private theorem perm_maps_wex_to_maxs {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {r : Fin n} (hr : r ∈ wexSet n σ) :
    ⇑σ r ∈ maxs (toPart n σ) := by
  have hW : wexSet n σ = mins (toPart n σ) := wexSet_eq_mins_toPart n σ
  set P : Finpartition (Finset.univ : Finset (Fin n)) := toPart n σ with hP
  set A : Finset (Fin n) := Finset.univ \ wexSet n σ with hA
  set B : Finset (Fin n) := Finset.univ \ maxs P with hB
  have hmaps : ∀ u ∈ A, ⇑σ u ∈ B := by
    intro u hu
    simp only [hA, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu
    have huM : u ∉ mins P := by
      intro hcon
      apply hu
      rw [hW]
      exact hcon
    have hEq : ⇑σ u = pred P u huM := perm_eq_pred_of_notMem huM
    rw [hB, Finset.mem_sdiff]
    constructor
    · exact Finset.mem_univ _
    · rw [hEq]
      exact pred_not_mem_maxs huM
  have hcardW : (wexSet n σ).card = P.parts.card := by
    rw [hW]
    exact card_mins_eq P
  have hcardM : (maxs P).card = P.parts.card := card_maxs_eq P
  have hcardA : A.card = n - P.parts.card := by
    rw [hA, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hcardW]
  have hcardB : B.card = n - P.parts.card := by
    rw [hB, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hcardM]
  have himg_sub : A.image ⇑σ ⊆ B := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact hmaps u hu
  have himg_card : (A.image ⇑σ).card = B.card := by
    rw [Finset.card_image_of_injective A σ.injective, hcardA, hcardB]
  have himg_eq : A.image ⇑σ = B :=
    Finset.eq_of_subset_of_card_le himg_sub himg_card.ge
  by_contra hnot
  have hrB : ⇑σ r ∈ B := by
    rw [hB, Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, hnot⟩
  rw [← himg_eq, Finset.mem_image] at hrB
  obtain ⟨u, hu, hEq⟩ := hrB
  have hEq2 : u = r := σ.injective hEq
  subst hEq2
  rw [hA, Finset.mem_sdiff] at hu
  exact hu.2 hr

private theorem bwe_perm_mins_to_maxs {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j) :
    (fun x : Fin (toPart n σ).parts.card =>
      σ ((mins (toPart n σ)).orderEmbOfFin (card_mins_eq (toPart n σ)) x)) =
      (maxs (toPart n σ)).orderEmbOfFin (card_maxs_eq (toPart n σ)) := by
  apply Finset.orderEmbOfFin_unique (card_maxs_eq (toPart n σ))
  · intro x
    apply perm_maps_wex_to_maxs
    rw [wexSet_eq_mins_toPart]
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro a b hab
    apply hσ
    · exact ((mins (toPart n σ)).orderEmbOfFin
        (card_mins_eq (toPart n σ))).strictMono hab
    · have ha : (mins (toPart n σ)).orderEmbOfFin
          (card_mins_eq (toPart n σ)) a ∈ wexSet n σ := by
        rw [wexSet_eq_mins_toPart]
        exact Finset.orderEmbOfFin_mem _ _ _
      simpa only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    · have hb : (mins (toPart n σ)).orderEmbOfFin
          (card_mins_eq (toPart n σ)) b ∈ wexSet n σ := by
        rw [wexSet_eq_mins_toPart]
        exact Finset.orderEmbOfFin_mem _ _ _
      simpa only [wexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hb

private theorem bwe_ofPartPerm_toPart {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j) :
    ofPartPerm (toPart n σ) = σ := by
  apply Equiv.ext
  intro u
  rw [ofPartPerm_apply]
  by_cases hu : u ∈ mins (toPart n σ)
  · rw [ofPartFun_eq_ofMem hu]
    have hEq := congrFun (bwe_perm_mins_to_maxs hσ)
      (((mins (toPart n σ)).orderIsoOfFin (card_mins_eq (toPart n σ))).symm
        ⟨u, hu⟩)
    rw [orderEmb_symm_mins hu] at hEq
    exact hEq.symm
  · rw [ofPartFun_eq_pred hu, ← perm_eq_pred_of_notMem hu]

private noncomputable def bwe_validPermEquivFinpartition (n : ℕ) :
    { σ : Equiv.Perm (Fin n) //
      ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } ≃
      Finpartition (Finset.univ : Finset (Fin n)) where
  toFun σ := toPart n σ
  invFun P := ⟨ofPartPerm P, ofPartPerm_valid P⟩
  left_inv σ := by
    apply Subtype.ext
    exact bwe_ofPartPerm_toPart σ.property
  right_inv P := toPart_ofPartPerm P

/--
**Bell numbers count permutations with increasing weak excedance letters.** A position $i$ is a
weak excedance of a permutation $\sigma$ when $i \le \sigma(i)$. For every $n$, the number of
permutations $\sigma$ of $\{0, 1, \dots, n-1\}$ such that $\sigma(i) < \sigma(j)$ whenever
$i < j$ are both weak excedances of $\sigma$ is the Bell number $B_n$.

Proves `Wanted` entry `bell_count_perm_increasing_weakExcedance_letters`.

Source: Fufa Beyene, Jörgen Backelin, Roberto Mantaci, and Samuel A.
Fufa, "Set Partitions and Other Bell Number Enumerated Objects,"
Journal of Integer Sequences 26 (2023), Article 23.1.8, Theorem,
lines 434–436,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Beyene/beyene13.tex
-/
public theorem bell_count_perm_increasing_weakExcedance_letters (n : ℕ) :
    Fintype.card { σ : Equiv.Perm (Fin n) //
      ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } = Nat.bell n := by
  exact (Fintype.card_congr (bwe_validPermEquivFinpartition n)).trans
    (card_finpartition_univ n)

end MetaMathlibExt
end
