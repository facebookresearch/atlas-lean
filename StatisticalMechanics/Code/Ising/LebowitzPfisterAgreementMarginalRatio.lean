/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterAgreementComplementRatio
import Mathlib.Combinatorics.SetFamily.FourFunctions










open Finset

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem ghsiSubsetMass_mul_compl_le_interCompl_mul_union
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (A B : Finset V) :
    ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf Bᶜ <=
      ghsiSubsetMass G K hf (A ∩ B)ᶜ *
        ghsiSubsetMass G K hf (A ∪ B) := by
  have hratio := ghsiSubsetMass_compl_ratio_mono G K hf hK hhf
    (show Bᶜ ⊆ (A ∩ B)ᶜ by
      intro x hx
      simp only [mem_compl, mem_inter] at hx ⊢
      exact fun h => hx h.2)
  have hlog := ghsiSubsetMass_logSupermodular G K hf hK hhf A B
  have hB : 0 < ghsiSubsetMass G K hf B := by
    unfold ghsiSubsetMass
    exact mul_pos (ZJ_pos _ _ _) (ZJ_pos _ _ _)
  have hI : 0 < ghsiSubsetMass G K hf (A ∩ B) := by
    unfold ghsiSubsetMass
    exact mul_pos (ZJ_pos _ _ _) (ZJ_pos _ _ _)
  simp only [compl_compl] at hratio
  have hprod := mul_le_mul hlog hratio
    (mul_nonneg (ghsiSubsetMass_nonneg G K hf Bᶜ)
      (ghsiSubsetMass_nonneg G K hf (A ∩ B)))
    (mul_nonneg (ghsiSubsetMass_nonneg G K hf (A ∪ B))
      (ghsiSubsetMass_nonneg G K hf (A ∩ B)))
  nlinarith [hprod, mul_pos hB hI]



noncomputable def ghsiSubsetMarginalMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (M P : Finset V) : Real :=
  ∑ S ∈ Mᶜ.powerset, ghsiSubsetMass G K hf (P ∪ S)

theorem ghsiSubsetMarginalMass_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real) (M P : Finset V) :
    0 <= ghsiSubsetMarginalMass G K hf M P := by
  unfold ghsiSubsetMarginalMass
  apply Finset.sum_nonneg
  intro S _
  exact ghsiSubsetMass_nonneg G K hf _



theorem sum_ghsiSubsetMass_compl_eq_marginal_sdiff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    {M P : Finset V} (hPM : P ⊆ M) :
    (∑ S ∈ Mᶜ.powerset, ghsiSubsetMass G K hf (P ∪ S)ᶜ) =
      ghsiSubsetMarginalMass G K hf M (M \ P) := by
  unfold ghsiSubsetMarginalMass
  let U := Mᶜ
  apply Finset.sum_nbij' (fun S => U \ S) (fun S => U \ S)
  · intro S hS
    simp only [mem_powerset] at hS ⊢
    exact sdiff_subset
  · intro S hS
    simp only [mem_powerset] at hS ⊢
    exact sdiff_subset
  · intro S hS
    simp only [mem_powerset] at hS
    exact Finset.sdiff_sdiff_eq_self hS
  · intro S hS
    simp only [mem_powerset] at hS
    exact Finset.sdiff_sdiff_eq_self hS
  · intro S hS
    simp only [mem_powerset] at hS
    congr 1
    ext x
    simp only [mem_compl, mem_union, mem_sdiff]
    constructor
    · intro hx
      by_cases hxM : x ∈ M
      · left
        exact ⟨hxM, fun hxP => hx (Or.inl hxP)⟩
      · right
        exact ⟨mem_compl.mpr hxM, fun hxS => hx (Or.inr hxS)⟩
    · rintro (hx | hx)
      · exact fun h => hx.2 (h.resolve_right (fun hxS =>
          (mem_compl.mp (hS hxS)) hx.1))
      · exact fun h => hx.2 (h.resolve_left (fun hxP =>
          (mem_compl.mp hx.1) (hPM hxP)))



theorem ghsiSubsetMarginalMass_compl_ratio_mono
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {M P Q : Finset V} (hPQ : P ⊆ Q) (hQM : Q ⊆ M) :
    ghsiSubsetMarginalMass G K hf M P *
        ghsiSubsetMarginalMass G K hf M (M \ Q) <=
      ghsiSubsetMarginalMass G K hf M Q *
        ghsiSubsetMarginalMass G K hf M (M \ P) := by
  let U := Mᶜ
  let f1 : Finset V -> Real := fun S => ghsiSubsetMass G K hf (P ∪ S)
  let f2 : Finset V -> Real := fun S => ghsiSubsetMass G K hf (Q ∪ S)ᶜ
  let f3 : Finset V -> Real := fun S => ghsiSubsetMass G K hf (P ∪ S)ᶜ
  let f4 : Finset V -> Real := fun S => ghsiSubsetMass G K hf (Q ∪ S)
  have hPM : P ⊆ M := hPQ.trans hQM
  have hfour : ∀ A, A ⊆ U → ∀ B, B ⊆ U →
      f1 A * f2 B <= f3 (A ∩ B) * f4 (A ∪ B) := by
    intro A hA B hB
    have hPA : Disjoint P A := by
      rw [disjoint_left]
      intro x hxP hxA
      exact (mem_compl.mp (hA hxA)) (hPM hxP)
    have hQB : Disjoint Q B := by
      rw [disjoint_left]
      intro x hxQ hxB
      exact (mem_compl.mp (hB hxB)) (hQM hxQ)
    have hinter : (P ∪ A) ∩ (Q ∪ B) = P ∪ (A ∩ B) := by
      ext x
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hxP | hxA, hxQ | hxB⟩
        · exact Or.inl hxP
        · exact Or.inl hxP
        · exact False.elim ((mem_compl.mp (hA hxA)) (hQM hxQ))
        · exact Or.inr ⟨hxA, hxB⟩
      · rintro (hxP | ⟨hxA, hxB⟩)
        · exact ⟨Or.inl hxP, Or.inl (hPQ hxP)⟩
        · exact ⟨Or.inr hxA, Or.inr hxB⟩
    have hunion : (P ∪ A) ∪ (Q ∪ B) = Q ∪ (A ∪ B) := by
      ext x
      simp only [mem_union]
      constructor
      · rintro ((hxP | hxA) | hxQ | hxB)
        · exact Or.inl (hPQ hxP)
        · exact Or.inr (Or.inl hxA)
        · exact Or.inl hxQ
        · exact Or.inr (Or.inr hxB)
      · rintro (hxQ | hxA | hxB)
        · exact Or.inr (Or.inl hxQ)
        · exact Or.inl (Or.inr hxA)
        · exact Or.inr (Or.inr hxB)
    simpa only [f1, f2, f3, f4, hinter, hunion] using
      ghsiSubsetMass_mul_compl_le_interCompl_mul_union
        G K hf hK hhf (P ∪ A) (Q ∪ B)
  have hff := U.four_functions_theorem
    (f₁ := f1) (f₂ := f2) (f₃ := f3) (f₄ := f4)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    (by intro S; exact ghsiSubsetMass_nonneg G K hf _)
    hfour (show U.powerset ⊆ U.powerset from Subset.rfl)
    (show U.powerset ⊆ U.powerset from Subset.rfl)
  simp only [powerset_infs_powerset_self, powerset_sups_powerset_self] at hff
  have hcompP := sum_ghsiSubsetMass_compl_eq_marginal_sdiff
    G K hf hPM
  have hcompQ := sum_ghsiSubsetMass_compl_eq_marginal_sdiff
    G K hf hQM
  rw [← hcompQ, ← hcompP]
  simpa only [ghsiSubsetMarginalMass, U, f1, f2, f3, f4, mul_comm]
    using hff



theorem ghsiSubsetMarginalMass_rank_zero_three_le_one_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (M : Finset V) :
    ghsiSubsetMarginalMass G K hf M ∅ *
        (∑ x ∈ M, ghsiSubsetMarginalMass G K hf M (M \ {x})) <=
      (∑ x ∈ M, ghsiSubsetMarginalMass G K hf M {x}) *
        ghsiSubsetMarginalMass G K hf M M := by
  have hpoint (x : V) (hx : x ∈ M) :
      ghsiSubsetMarginalMass G K hf M ∅ *
          ghsiSubsetMarginalMass G K hf M (M \ {x}) <=
        ghsiSubsetMarginalMass G K hf M {x} *
          ghsiSubsetMarginalMass G K hf M M := by
    have h := ghsiSubsetMarginalMass_compl_ratio_mono
      G K hf hK hhf (M := M) (P := ∅) (Q := {x})
      (empty_subset _) (singleton_subset_iff.mpr hx)
    simpa using h
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun x hx => hpoint x hx

end

end StatMech.Ising
