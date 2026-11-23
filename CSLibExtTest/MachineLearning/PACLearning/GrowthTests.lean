/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.Growth

/-! Kernel-checked clients of the canonical VC-to-growth API. -/

open Cslib.MachineLearning.PACLearning

namespace CSLibExtTest.MachineLearning.PACLearning

private def constants : ConceptClass ℕ Bool :=
  {c | ∃ b, c = fun _ => b}

private theorem constants_card_le_one (W : Finset ℕ)
    (hW : SetShatters constants ↑W) : W.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨c, ⟨v, rfl⟩, hv⟩ := hW {a} (Set.singleton_subset_iff.mpr ha)
  have hva := (Set.ext_iff.mp hv a).mpr (Set.mem_singleton a)
  have hvb := (Set.ext_iff.mp hv b).mp ⟨hva.1, hb⟩
  exact hvb.symm

private theorem constants_finite : HasFiniteVCDim constants :=
  hasFiniteVCDim_iff.mpr ⟨1, constants_card_le_one⟩

private theorem constants_shatters_singleton :
    SetShatters constants ({0} : Set ℕ) := by
  classical
  intro V hV
  refine ⟨fun _ => decide (0 ∈ V), ⟨_, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq]
  constructor
  · rintro ⟨h, rfl⟩
    exact h
  · intro hx
    have hx0 : x = 0 := hV hx
    subst x
    exact ⟨hx, rfl⟩

private theorem constants_vcDim : vcDim constants = 1 := by
  unfold vcDim
  apply Nat.le_antisymm
  · apply csSup_le
    · exact ⟨1, {0}, by simp,
        by simpa using constants_shatters_singleton⟩
    · rintro n ⟨W, rfl, hW⟩
      exact constants_card_le_one W hW
  · exact le_csSup constants_finite ⟨({0} : Finset ℕ), by simp,
      by simpa using constants_shatters_singleton⟩

private theorem constants_as_list : constants =
    {c : ℕ → Bool | c ∈ [fun _ => false, fun _ => true]} := by
  ext c
  simp [constants, Bool.exists_bool]

-- The public bound gives 4 on three points, strictly below the generic 8.
private theorem constants_growth_bound :
    (traceFamily constants {0, 1, 2}).card ≤ 4 := by
  calc
    _ ≤ ∑ k ∈ Finset.Iic (vcDim constants),
        ({0, 1, 2} : Finset ℕ).card.choose k :=
      card_traceFamily_le_sum_vcDim constants_finite _
    _ = 4 := by rw [constants_vcDim]; decide

-- Computation and the representation theorem identify the actual count.
private theorem constants_trace_count :
    (traceFamily constants {0, 1, 2}).card = 2 := by
  rw [constants_as_list, ← finiteTraces_eq_traceFamily]
  decide

private theorem constants_empty_sample :
    (traceFamily constants ∅).card = 1 := by
  rw [constants_as_list, ← finiteTraces_eq_traceFamily]
  decide

private theorem constants_shatters_traces :
    (traceFamily constants {0}).Shatters Finset.univ := by
  apply shatters_traceFamily_iff.mpr
  simpa using constants_shatters_singleton

private theorem constants_finite_trace_dimension :
    (finiteTraces [fun _ : ℕ => false, fun _ => true]
      {0, 1, 2}).vcDim = 1 := by decide

private theorem empty_class_traces {α : Type*} (s : Finset α) :
    traceFamily (∅ : ConceptClass α Bool) s = ∅ := by
  ext t
  simp

-- Empty classes satisfy the exact canonical premise, without a nonempty
-- convention smuggled into the definition of shattering.
private theorem empty_class_finite {α : Type*} :
    HasFiniteVCDim (∅ : ConceptClass α Bool) := by
  apply hasFiniteVCDim_iff.mpr
  refine ⟨0, fun W hW => ?_⟩
  obtain ⟨c, hc, _⟩ := hW ∅ (Set.empty_subset _)
  exact False.elim hc

private theorem full_three_finite :
    HasFiniteVCDim (Set.univ : ConceptClass (Fin 3) Bool) := by
  apply hasFiniteVCDim_iff.mpr
  exact ⟨3, fun W _ => (Finset.card_le_univ W).trans_eq (by simp)⟩

private theorem full_three_shatters :
    SetShatters (Set.univ : ConceptClass (Fin 3) Bool)
      ↑(Finset.univ : Finset (Fin 3)) := by
  have h : @Finset.Shatters (Fin 3) (Classical.decEq _) Finset.univ
      Finset.univ := by
    convert (Finset.univ_shatters (s := (Finset.univ : Finset (Fin 3)))) using 1
  exact h.toSetShatters.superset (Set.subset_univ _)

private theorem full_three_vcDim :
    vcDim (Set.univ : ConceptClass (Fin 3) Bool) = 3 := by
  unfold vcDim
  apply Nat.le_antisymm
  · apply csSup_le
    · exact ⟨3, Finset.univ, by simp, full_three_shatters⟩
    · rintro n ⟨W, rfl, _⟩
      exact (Finset.card_le_univ W).trans_eq (by simp)
  · exact le_csSup full_three_finite
      ⟨Finset.univ, by simp, full_three_shatters⟩

private theorem full_three_growth_bound :
    (traceFamily (Set.univ : ConceptClass (Fin 3) Bool) Finset.univ).card
      ≤ 8 := by
  calc
    _ ≤ ∑ k ∈ Finset.Iic (vcDim (Set.univ : ConceptClass (Fin 3) Bool)),
        (Finset.univ : Finset (Fin 3)).card.choose k :=
      card_traceFamily_le_sum_vcDim full_three_finite _
    _ = 8 := by rw [full_three_vcDim]; decide

private theorem full_three_trace_count :
    (traceFamily (Set.univ : ConceptClass (Fin 3) Bool) Finset.univ).card
      = 8 := by
  classical
  have h : traceFamily (Set.univ : ConceptClass (Fin 3) Bool)
      Finset.univ = Finset.univ := by
    ext t
    simp only [mem_traceFamily, Finset.mem_univ, iff_true]
    exact ⟨fun x => decide (⟨x, Finset.mem_univ x⟩ ∈ t),
      Set.mem_univ _, fun x => by simp⟩
  rw [h]
  simp

end CSLibExtTest.MachineLearning.PACLearning
