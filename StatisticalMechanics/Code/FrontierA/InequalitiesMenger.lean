/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Walls.bc19menger

open Finset SimpleGraph

namespace StatMech.FrontierA

open Walls

variable {V : Type*} [Fintype V]


noncomputable def finiteABSeparators (G : SimpleGraph V) (A B : Set V) :
    Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun C => bc16_IsSeparator G A B (C : Set V)

theorem finiteABSeparators_nonempty (G : SimpleGraph V) (A B : Set V) :
    (finiteABSeparators G A B).Nonempty := by
  classical
  refine ⟨Finset.univ, ?_⟩
  simp only [finiteABSeparators, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using bc16_univ_isSeparator G A B


noncomputable def vertexSeparatorNumber (G : SimpleGraph V) (A B : Set V) : ℕ :=
  (finiteABSeparators G A B).inf' (finiteABSeparators_nonempty G A B) Finset.card


noncomputable def finiteABPackingSizes (G : SimpleGraph V) (A B : Set V) :
    Finset (Fin (Fintype.card V + 1)) := by
  classical
  exact Finset.univ.filter fun k =>
    Nonempty (bc16_DisjointPathFamily G A B (Fin k.val))

theorem finiteABPackingSizes_nonempty (G : SimpleGraph V) (A B : Set V) :
    (finiteABPackingSizes G A B).Nonempty := by
  classical
  let k : Fin (Fintype.card V + 1) := ⟨0, Nat.zero_lt_succ _⟩
  refine ⟨k, ?_⟩
  simp only [finiteABPackingSizes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact bc17_hard_zero G A B


noncomputable def vertexDisjointPathNumber (G : SimpleGraph V) (A B : Set V) : ℕ :=
  (finiteABPackingSizes G A B).sup' (finiteABPackingSizes_nonempty G A B) Fin.val



theorem finite_vertex_menger_threshold (G : SimpleGraph V) (A B : Set V)
    (_hAB : Disjoint A B) (k : ℕ) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin k)) ↔
      ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard := by
  classical
  constructor
  · rintro ⟨F⟩ C hC
    simpa using bc16_card_le_ncard_separator F hC
  · exact bc19_hardDir_all G A B k




theorem finite_vertex_menger (G : SimpleGraph V) (A B : Set V)
    (_hAB : Disjoint A B) :
    vertexDisjointPathNumber G A B = vertexSeparatorNumber G A B := by
  classical
  apply Nat.le_antisymm
  · unfold vertexDisjointPathNumber
    apply Finset.sup'_le
    intro k hk
    have hfamily : Nonempty (bc16_DisjointPathFamily G A B (Fin k.val)) := by
      simpa [finiteABPackingSizes] using hk
    obtain ⟨C, hC, hmin⟩ := Finset.exists_mem_eq_inf'
      (finiteABSeparators_nonempty G A B) Finset.card
    have hsep : bc16_IsSeparator G A B (C : Set V) := by
      simpa [finiteABSeparators] using hC
    calc
      k.val = Fintype.card (Fin k.val) := (Fintype.card_fin k.val).symm
      _ ≤ (C : Set V).ncard := bc16_card_le_ncard_separator hfamily.some hsep
      _ = C.card := Set.ncard_coe_finset C
      _ = vertexSeparatorNumber G A B := by
        rw [vertexSeparatorNumber, hmin]
  · have hmin : ∀ C, bc16_IsSeparator G A B C →
        vertexSeparatorNumber G A B ≤ C.ncard := by
      intro C hC
      let hCfin : C.Finite := Set.toFinite C
      let Cf : Finset V := hCfin.toFinset
      have hmem : Cf ∈ finiteABSeparators G A B := by
        simp only [finiteABSeparators, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [Cf] using hC
      have hle := Finset.inf'_le Finset.card hmem
      calc
        vertexSeparatorNumber G A B ≤ Cf.card := by
          simpa only [vertexSeparatorNumber] using hle
        _ = C.ncard := (Set.ncard_eq_toFinset_card C hCfin).symm
    obtain ⟨F⟩ := bc19_hardDir_all G A B (vertexSeparatorNumber G A B) hmin
    have hkcard : vertexSeparatorNumber G A B ≤ Fintype.card V := by
      have hle := bc16_card_le_ncard_separator F (bc16_univ_isSeparator G A B)
      simpa using hle
    let k : Fin (Fintype.card V + 1) :=
      ⟨vertexSeparatorNumber G A B, Nat.lt_succ_of_le hkcard⟩
    have hk : k ∈ finiteABPackingSizes G A B := by
      simp only [finiteABPackingSizes, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨F⟩
    exact Finset.le_sup' Fin.val hk

end StatMech.FrontierA
