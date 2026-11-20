/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Walls.gc16core
import Code.Walls.gc7core
import Code.Walls.gc6_munonneg
import Code.Ising.HdomNativeWeight
import Code.Ising.AizenmanSignDominance
import Code.Ising.TwoReplicaWeighted

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.FieldGhostDict
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (S : SimpleGraph V) [DecidableRel S.Adj]













noncomputable def gc19_eref (p : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V))
    (K : ↥S.edgeFinset → ℕ) : ↥S.edgeFinset → ℕ :=
  fun e => if (e.1 : Sym2 V) ∈ P then p e - K e else K e


lemma gc19_eref_le (p : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) {K : ↥S.edgeFinset → ℕ}
    (hK : ∀ e, K e ≤ p e) : ∀ e, gc19_eref S p P K e ≤ p e := by
  intro e; unfold gc19_eref
  by_cases h : (e.1 : Sym2 V) ∈ P
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; exact hK e


lemma gc19_eref_involutive (p : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) {K : ↥S.edgeFinset → ℕ}
    (hK : ∀ e, K e ≤ p e) : gc19_eref S p P (gc19_eref S p P K) = K := by
  funext e; unfold gc19_eref
  by_cases h : (e.1 : Sym2 V) ∈ P
  · simp only [if_pos h]; have := hK e; omega
  · simp only [if_neg h]



lemma gc19_ofEdgeFun_eref (p K : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) :
    ofEdgeFun S (gc19_eref S p P K)
      = StatMech.Ising.reflect (ofEdgeFun S p) P (ofEdgeFun S K) := by
  funext e
  unfold gc19_eref StatMech.Ising.reflect ofEdgeFun
  by_cases he : e ∈ S.edgeFinset
  · by_cases hP : e ∈ P <;> simp [he, hP]
  · by_cases hP : e ∈ P <;> simp [he, hP]



noncomputable def gc19_ref2 (m : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V))
    (K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) :
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} :=
  ⟨(K.1.1, gc19_eref S (fun e => m e - K.1.1 e) P K.1.2), by
    intro e
    have hK := K.2 e
    have hbudget : ∀ e', K.1.2 e' ≤ (fun e => m e - K.1.1 e) e' := fun e' => by
      have := K.2 e'; simp only; omega
    have hle : gc19_eref S (fun e => m e - K.1.1 e) P K.1.2 e ≤ m e - K.1.1 e :=
      gc19_eref_le S (fun e => m e - K.1.1 e) P hbudget e
    simp only at hle ⊢
    omega⟩





noncomputable def gc19_ref2Equiv (m : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) :
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} ≃
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} where
  toFun := gc19_ref2 S m P
  invFun := gc19_ref2 S m P
  left_inv K := by
    apply Subtype.ext
    have hbudget : ∀ e, K.1.2 e ≤ m e - K.1.1 e := fun e => by have := K.2 e; omega
    have hinv := gc19_eref_involutive S (fun e => m e - K.1.1 e) P hbudget
    show ((K.1.1, gc19_eref S (fun e => m e - K.1.1 e) P
        (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2)) : (_ × _)) = K.1
    rw [hinv]
  right_inv K := by
    apply Subtype.ext
    have hbudget : ∀ e, K.1.2 e ≤ m e - K.1.1 e := fun e => by have := K.2 e; omega
    have hinv := gc19_eref_involutive S (fun e => m e - K.1.1 e) P hbudget
    show ((K.1.1, gc19_eref S (fun e => m e - K.1.1 e) P
        (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2)) : (_ × _)) = K.1
    rw [hinv]


lemma gc19_ofEdgeFun_sub (p K : ↥S.edgeFinset → ℕ) :
    ofEdgeFun S (fun e => p e - K e) = (fun e => ofEdgeFun S p e - ofEdgeFun S K e) := by
  funext e; unfold ofEdgeFun
  by_cases he : e ∈ S.edgeFinset <;> simp [he]




lemma gc19_ref2_weight (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V))
    (K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) :
    weight S β J (ofEdgeFun S (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2))
        * weight S β J (ofEdgeFun S (fun e => m e - K.1.1 e
            - gc19_eref S (fun e => m e - K.1.1 e) P K.1.2 e))
      = weight S β J (ofEdgeFun S K.1.2)
          * weight S β J (ofEdgeFun S (fun e => m e - K.1.1 e - K.1.2 e)) := by
  set p : ↥S.edgeFinset → ℕ := fun e => m e - K.1.1 e with hp
  have hbudget : ∀ e, K.1.2 e ≤ p e := fun e => by have := K.2 e; simp only [hp]; omega
  have h3 : (fun e => m e - K.1.1 e - K.1.2 e) = (fun e => p e - K.1.2 e) := by
    funext e; simp only [hp]
  have h3' : (fun e => m e - K.1.1 e - gc19_eref S (fun e => m e - K.1.1 e) P K.1.2 e)
      = (fun e => p e - gc19_eref S p P K.1.2 e) := by
    funext e; simp only [hp]
  rw [h3, h3']
  rw [gc19_ofEdgeFun_sub S p (gc19_eref S p P K.1.2),
      gc19_ofEdgeFun_sub S p K.1.2,
      gc19_ofEdgeFun_eref S p K.1.2 P]
  have hnb : ∀ e, (ofEdgeFun S K.1.2) e ≤ (ofEdgeFun S p) e := by
    intro e; unfold ofEdgeFun; by_cases he : e ∈ S.edgeFinset <;> simp [he, hbudget]
  exact weight_reflect_split_eq S β J (ofEdgeFun S p) P hnb




lemma gc19_ref2_sources (m : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V))
    (K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e})
    (hPE : P ⊆ S.edgeFinset)
    (hPodd : ∀ e ∈ P, Odd ((ofEdgeFun S (fun e => m e - K.1.1 e)) e)) :
    sources S (ofEdgeFun S (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2))
      = sources S (ofEdgeFun S K.1.2) ∆ srcP P := by
  set p : ↥S.edgeFinset → ℕ := fun e => m e - K.1.1 e with hp
  rw [gc19_ofEdgeFun_eref S p K.1.2 P]
  have hnb : ∀ e, (ofEdgeFun S K.1.2) e ≤ (ofEdgeFun S p) e := by
    intro e; unfold ofEdgeFun
    by_cases he : e ∈ S.edgeFinset
    · simp only [he, dif_pos]; have := K.2 ⟨e, he⟩; simp only [hp]; omega
    · simp [he]
  exact sources_reflect S.edgeFinset (ofEdgeFun S p) P (ofEdgeFun S K.1.2) hnb hPE hPodd
















theorem gc19_tpsum_firstSlot_switch (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ)
    (A B : Finset V) {u v : V} (huv : u ≠ v)
    (hconn : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₂.1) = B →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) u v) :
    gc15_tpsum S β J m (A ∆ {u, v}) B = gc15_tpsum S β J m A B := by
  rw [gc16_tpsum_bridge S β J m (A ∆ {u, v}) B, gc16_tpsum_bridge S β J m A B]
  refine Finset.sum_congr rfl (fun K₂ _ => ?_)
  by_cases hB : sources S (ofEdgeFun S K₂.1) = B
  · rw [if_pos hB]
    congr 1
    exact ising_switching_weighted S β J (ofEdgeFun S (fun e => m e - K₂.1 e)) huv
      (hconn K₂ hB) 1 A
  · rw [if_neg hB, zero_mul, zero_mul]




theorem gc19_tpsum_secondSlot_switch (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ)
    (A B : Finset V) {u v : V} (huv : u ≠ v)
    (hconn : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₁.1) = A →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) u v) :
    gc15_tpsum S β J m A (B ∆ {u, v}) = gc15_tpsum S β J m A B := by
  rw [gc16_tpsum_symm S β J m A (B ∆ {u, v}), gc16_tpsum_symm S β J m A B]
  exact gc19_tpsum_firstSlot_switch S β J m B A huv hconn







theorem gc19_tpsum_secondSlot_directSwitch (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ)
    (A B : Finset V) (P : Finset (Sym2 V)) (hPE : P ⊆ S.edgeFinset)
    (hPodd : ∀ K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
        ∀ e ∈ P, Odd ((ofEdgeFun S (fun e => m e - K.1.1 e)) e)) :
    gc15_tpsum S β J m A (B ∆ srcP P) = gc15_tpsum S β J m A B := by
  unfold gc15_tpsum
  rw [← Equiv.sum_comp (gc19_ref2Equiv S m P)]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  simp only [gc19_ref2Equiv, gc19_ref2, Equiv.coe_fn_mk]
  have hsrc : sources S (ofEdgeFun S (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2))
      = sources S (ofEdgeFun S K.1.2) ∆ srcP P :=
    gc19_ref2_sources S m P K hPE (hPodd K)
  have hw := gc19_ref2_weight S β J m P K
  rw [hsrc]
  by_cases hB : sources S (ofEdgeFun S K.1.2) = B
  · rw [if_pos hB,
      if_pos (show sources S (ofEdgeFun S K.1.2) ∆ srcP P = B ∆ srcP P from by rw [hB]),
      mul_assoc, mul_assoc, hw]
  · have hBne : sources S (ofEdgeFun S K.1.2) ∆ srcP P ≠ B ∆ srcP P := by
      intro hh; exact hB (symmDiff_left_injective (srcP P) hh)
    rw [if_neg hB, if_neg hBne]; ring














theorem gc19_tpsum_starPair_collapse (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ)
    {u v : V} (huv : u ≠ v)
    (hconn : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₂.1) = ∅ →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) u v) :
    gc15_tpsum S β J m ∅ {u, v} = gc15_tpsum S β J m ∅ ∅ := by
  have h := gc19_tpsum_secondSlot_switch S β J m ∅ ∅ huv ?_
  · rwa [show (∅ : Finset V) ∆ {u, v} = {u, v} from by simp] at h
  · intro K₁ hK₁; exact hconn K₁ hK₁










theorem gc19_tpsum_fifth_reduce_to_base (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ)
    {o x g : V} (hog : o ≠ g) (hxg : x ≠ g)
    (hcr1 : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₂.1) = {x, g} →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) o g)
    (hcr2 : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₁.1) = ∅ →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) x g) :
    gc15_tpsum S β J m {o, g} {x, g} = gc15_tpsum S β J m ∅ ∅ := by
  have e1 : gc15_tpsum S β J m ({o, g} ∆ {o, g}) {x, g} = gc15_tpsum S β J m {o, g} {x, g} :=
    gc19_tpsum_firstSlot_switch S β J m {o, g} {x, g} hog hcr1
  rw [show ({o, g} : Finset V) ∆ {o, g} = ∅ from by simp] at e1
  have e2 : gc15_tpsum S β J m ∅ ({x, g} ∆ {x, g}) = gc15_tpsum S β J m ∅ {x, g} :=
    gc19_tpsum_secondSlot_switch S β J m ∅ {x, g} hxg hcr2
  rw [show ({x, g} : Finset V) ∆ {x, g} = ∅ from by simp] at e2
  rw [← e1, ← e2]










theorem gc19_cert_zero_of_allConn (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ)
    {o x y g : V} (hog : o ≠ g) (hox : o ≠ x) (hoy : o ≠ y) (hxg : x ≠ g)
    (hOg : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₁.1) = ∅ →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) o g)
    (hOx : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₁.1) = ∅ →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) o x)
    (hOy : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₁.1) = ∅ →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) o y)
    (hcr1 : ∀ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₂.1) = {x, g} →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) o g)
    (hcr2 : ∀ K₁ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        sources S (ofEdgeFun S K₁.1) = ∅ →
        connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₁.1 e))) x g) :
    gc15_tpsum S β J m ∅ ∅
        - gc15_tpsum S β J m ∅ {o, g} - gc15_tpsum S β J m ∅ {o, x}
        - gc15_tpsum S β J m ∅ {o, y}
        + 2 * gc15_tpsum S β J m {o, g} {x, g} = 0 := by
  rw [gc19_tpsum_starPair_collapse S β J m hog hOg,
      gc19_tpsum_starPair_collapse S β J m hox hOx,
      gc19_tpsum_starPair_collapse S β J m hoy hOy,
      gc19_tpsum_fifth_reduce_to_base S β J m hog hxg hcr1 hcr2]
  ring













theorem gc19_conn_of_sourcePair (m : ↥S.edgeFinset → ℕ)
    (hnd : ∀ e ∈ S.edgeFinset, ¬ e.IsDiag) {u v : V} (huv : u ≠ v)
    (K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e})
    (hsrc : sources S (ofEdgeFun S (fun e => m e - K₂.1 e)) = {u, v}) :
    connP (oddEdges S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e))) u v :=
  connOdd_of_sources S.edgeFinset (ofEdgeFun S (fun e => m e - K₂.1 e)) hnd huv hsrc

variable {V' : Type*} [Fintype V'] [DecidableEq V']
variable (G : SimpleGraph V') [DecidableRel G.Adj]





theorem gc19_cert_of_allConn (β h : ℝ) (o x y : V') (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V')) →
      (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
          connP (oddEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) none)
        ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some x))
        ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some y))
        ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none} →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none)
        ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some x) none)) :
    gc16_PerConfigCert G β h o x y := by
  intro m hm
  obtain ⟨hOg, hOx, hOy, hcr1, hcr2⟩ := hall m hm
  have hzero := gc19_cert_zero_of_allConn (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
    (o := some o) (x := some x) (y := some y) (g := none)
    (by simp) (by simpa using hox) (by simpa using hoy) (by simp)
    hOg hOx hOy hcr1 hcr2
  rw [hzero]



theorem gc19_ursell_nonpos_of_allConn (β h : ℝ) (o x y : V') (hox : o ≠ x) (hoy : o ≠ y)
    (hxy : x ≠ y)
    (hall : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V')) →
      (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
          sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
          connP (oddEdges (withGhost G).edgeFinset
              (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) none)
        ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some x))
        ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some o) (some y))
        ∧ (∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = {some x, none} →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none)
        ∧ (∀ K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e},
            sources (withGhost G) (ofEdgeFun (withGhost G) K₁.1) = ∅ →
            connP (oddEdges (withGhost G).edgeFinset
                (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) (some x) none)) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy (gc19_cert_of_allConn G β h o x y hox hoy hxy hall)

end StatMech.Walls
