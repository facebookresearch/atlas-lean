/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.GHSInhomogeneous











open Finset

namespace StatMech.Ising

open StatMech.Sharpness StatMech.Sharpness.FieldGhostDict

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem ghsiSubsetMass_agreeFinset_eq_mul_fibreMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (q : ConfigSpace V) :
    ghsiSubsetMass G K hf (ghsLAgreeFinset q) =
      (4 * Fintype.card (ConfigSpace V)) * ghsiFibreMass G K hf q := by
  classical
  let T := (v : {v : V // q v = true}) -> Bool
  let U := (v : {v : V // ¬ q v = true}) -> Bool
  let fT : T -> Real := fun st =>
    ghsiTWeight G K hf q (ghsLTComplete q st)
  let fU : U -> Real := fun su =>
    ghsiUWeight G K q (ghsLUComplete q su)
  have hmass : ghsiFibreMass G K hf q =
      (∑ st : T, fT st) * ∑ su : U, fU su := by
    unfold ghsiFibreMass ghsiFibreWeight
    calc
      (∑ a : ConfigSpace V,
          wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) =
          ∑ a : ConfigSpace V,
            fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
          ghsiTWeight_split, ghsiUWeight_split]
      _ = _ := ghsL_split_sum_product q fT fU
  have ht : ghsiTZ G K hf (ghsLAgreeFinset q) =
      (∑ st : T, fT st) * Fintype.card U := by
    unfold ghsiTZ ZJ
    have hs := ghsL_split_sum_product (V := V) q fT
      (fun _ : U => (1 : Real))
    rw [show (∑ a : ConfigSpace V,
        wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
          (fun e => 2 * K e)
          (fun x => if x ∈ ghsLAgreeFinset q then 2 * hf x else 0) a) =
        ∑ a : ConfigSpace V,
          fT (ghsLSplitEquiv q a).1 * (1 : Real) by
      apply Finset.sum_congr rfl
      intro a _
      rw [← ghsiTWeight_eq_wJ_restricted, ghsiTWeight_split]
      simp [fT]]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
  have hu : ghsiUZ G K (ghsLAgreeFinset q)ᶜ =
      Fintype.card T * ∑ su : U, fU su := by
    unfold ghsiUZ ZJ
    have hs := ghsL_split_sum_product (V := V) q
      (fun _ : T => (1 : Real)) fU
    rw [show (∑ a : ConfigSpace V,
        wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q)ᶜ)
          (fun e => 2 * K e) (fun _ => 0) a) =
        ∑ a : ConfigSpace V,
          (1 : Real) * fU (ghsLSplitEquiv q a).2 by
      apply Finset.sum_congr rfl
      intro a _
      rw [← ghsiUWeight_eq_wJ, ghsiUWeight_split]
      simp [fU]]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hs
  have hcard : Fintype.card (ConfigSpace V) =
      Fintype.card T * Fintype.card U := by
    rw [Fintype.card_congr (ghsLSplitEquiv q), Fintype.card_prod]
  rw [ghsiSubsetMass_eq_four_mul_tZ_uZ, ht, hu, hmass, hcard]
  norm_num [Nat.cast_mul]
  ring



theorem ghsiTZ_mul_ghsiUZ_le_of_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {A B : Finset V} (hAB : A ⊆ B) :
    ghsiTZ G K hf A * ghsiUZ G K B <=
      ghsiTZ G K hf B * ghsiUZ G K A := by
  classical
  let J2 : Sym2 (Option V) -> Real := ghsiGhostCoupling K hf
  have hJ2 : forall e, 0 <= J2 e := by
    intro e
    induction e with
    | h a b =>
        rcases a with _ | a <;> rcases b with _ | b <;>
          simp [J2, ghsiGhostCoupling, hK, hhf]
  have hnd : ∀ e ∈ (withGhost G).edgeFinset, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeFinset he
  have hlog := ghsvp_vertexZ_logSupermodular
    (withGhost G).edgeFinset J2 hJ2 hnd
    (ghsvp_fieldSet A) (ghsvp_someSet B)
  have hunion : ghsvp_fieldSet A ∪ ghsvp_someSet B =
      ghsvp_fieldSet B := by
    ext z
    rcases z with _ | z
    · simp [ghsvp_fieldSet, ghsvp_someSet]
    · simp [ghsvp_fieldSet, ghsvp_someSet]
      exact fun hz => hAB hz
  have hinter : ghsvp_fieldSet A ∩ ghsvp_someSet B =
      ghsvp_someSet A := by
    ext z
    rcases z with _ | z
    · simp [ghsvp_fieldSet, ghsvp_someSet]
    · simp [ghsvp_fieldSet, ghsvp_someSet]
      exact fun hz => hAB hz
  rw [hunion, hinter,
    ghsi_vertexZ_fieldSet_eq_two_mul_tZ,
    ghsi_vertexZ_someSet_eq_two_mul_uZ,
    ghsi_vertexZ_fieldSet_eq_two_mul_tZ,
    ghsi_vertexZ_someSet_eq_two_mul_uZ] at hlog
  nlinarith



theorem ghsiSubsetMass_compl_ratio_mono
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {A B : Finset V} (hAB : A ⊆ B) :
    ghsiSubsetMass G K hf A * ghsiSubsetMass G K hf Bᶜ <=
      ghsiSubsetMass G K hf B * ghsiSubsetMass G K hf Aᶜ := by
  classical
  have hcomp : Bᶜ ⊆ Aᶜ := by
    intro x hx
    simp only [mem_compl] at hx ⊢
    exact fun hA => hx (hAB hA)
  have h1 := ghsiTZ_mul_ghsiUZ_le_of_subset G K hf hK hhf hAB
  have h2 := ghsiTZ_mul_ghsiUZ_le_of_subset G K hf hK hhf hcomp
  have hnon : forall S : Finset V,
      0 <= ghsiTZ G K hf S ∧ 0 <= ghsiUZ G K S := by
    intro S
    exact ⟨(ZJ_pos _ _ _).le, (ZJ_pos _ _ _).le⟩
  have hprod := mul_le_mul h1 h2
    (mul_nonneg (hnon Bᶜ).1 (hnon Aᶜ).2)
    (mul_nonneg (hnon B).1 (hnon A).2)
  simp_rw [ghsiSubsetMass_eq_four_mul_tZ_uZ]
  simp only [compl_compl]
  nlinarith [hprod]



theorem ghsiFibreMass_compl_ratio_mono
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    {q r : ConfigSpace V} (hqr : q <= r) :
    ghsiFibreMass G K hf q *
        ghsiFibreMass G K hf (fun x => !(r x)) <=
      ghsiFibreMass G K hf r *
        ghsiFibreMass G K hf (fun x => !(q x)) := by
  classical
  have hsub : ghsLAgreeFinset q ⊆ ghsLAgreeFinset r :=
    ghsLAgreeFinset_monotone hqr
  have hratio := ghsiSubsetMass_compl_ratio_mono
    G K hf hK hhf hsub
  have hnot (s : ConfigSpace V) :
      ghsLAgreeFinset (fun x => !(s x)) = (ghsLAgreeFinset s)ᶜ := by
    ext x
    simp [ghsLAgreeFinset]
  rw [← hnot r, ← hnot q,
    ghsiSubsetMass_agreeFinset_eq_mul_fibreMass,
    ghsiSubsetMass_agreeFinset_eq_mul_fibreMass,
    ghsiSubsetMass_agreeFinset_eq_mul_fibreMass,
    ghsiSubsetMass_agreeFinset_eq_mul_fibreMass] at hratio
  have hc : 0 < (4 * Fintype.card (ConfigSpace V) : Real) := by
    have : 0 < Fintype.card (ConfigSpace V) := Fintype.card_pos
    positivity
  nlinarith [sq_pos_of_pos hc]

end

end StatMech.Ising
