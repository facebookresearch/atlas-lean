/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.TwoReplica
import Code.Sharpness.CurrentRep
import Code.Ising.AizenmanInclusionExclusion
import Code.Ising.AizenmanTrueBackbone
import Code.Ising.AizenmanHdom

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace StatMech

namespace Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]







noncomputable def acwRestrict (p : Sym2 V → Prop) [DecidablePred p] (n : Current V) : Current V :=
  fun e => if p e then n e else 0



def acwInternal (S : Finset V) (e : Sym2 V) : Prop := ∀ z ∈ e, z ∈ S

instance (S : Finset V) : DecidablePred (acwInternal S) := fun e => by
  unfold acwInternal; infer_instance






def acwClosedCut (S : Finset V) : Prop :=
  ∀ e ∈ G.edgeFinset, acwInternal S e ∨ acwInternal Sᶜ e






theorem acw_weight_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (n : Current V) : 0 ≤ weight G β J n := by
  unfold weight
  refine Finset.prod_nonneg (fun e _ => ?_)
  exact div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e)) _) (Nat.cast_nonneg _)







theorem acw_weight_restrict (β : ℝ) (J : Sym2 V → ℝ) (p : Sym2 V → Prop) [DecidablePred p]
    (n : Current V) :
    weight G β J (acwRestrict p n)
      = ∏ e ∈ G.edgeFinset.filter p, (β * J e) ^ (n e) / (Nat.factorial (n e)) := by
  unfold weight acwRestrict
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset p]
  rw [show (∏ e ∈ G.edgeFinset.filter (fun e => ¬ p e),
        (β * J e) ^ (if p e then n e else 0) / (Nat.factorial (if p e then n e else 0))) = 1 from
      Finset.prod_eq_one (fun e he => by rw [Finset.mem_filter] at he; simp [he.2])]
  rw [mul_one]
  refine Finset.prod_congr rfl (fun e he => by rw [Finset.mem_filter] at he; simp [he.2])














theorem acw_weight_factor (β : ℝ) (J : Sym2 V → ℝ) (p : Sym2 V → Prop) [DecidablePred p]
    (n : Current V) :
    weight G β J n = weight G β J (acwRestrict p n) * weight G β J (acwRestrict (fun e => ¬ p e) n) := by
  rw [acw_weight_restrict, acw_weight_restrict]
  rw [show weight G β J n = ∏ e ∈ G.edgeFinset, (β * J e) ^ (n e) / (Nat.factorial (n e)) from rfl]
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset p
        (fun e => (β * J e) ^ (n e) / (Nat.factorial (n e)))]










theorem acw_weight_factor_cut (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (n : Current V) :
    weight G β J n
      = weight G β J (acwRestrict (acwInternal S) n)
        * weight G β J (acwRestrict (fun e => ¬ acwInternal S e) n) :=
  acw_weight_factor G β J (acwInternal S) n









theorem acw_incidentFlux_internal_mem (S : Finset V) (hcut : acwClosedCut G S) (n : Current V)
    {x : V} (hx : x ∈ S) :
    Sharpness.incidentFlux G (acwRestrict (acwInternal S) n) x = Sharpness.incidentFlux G n x := by
  unfold Sharpness.incidentFlux acwRestrict
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Finset.mem_filter] at he
  obtain ⟨heG, hxe⟩ := he
  by_cases hint : acwInternal S e
  · simp [hint]
  · exfalso
    rcases hcut e heG with h | h
    · exact hint h
    · exact (Finset.mem_compl.1 (h x hxe)) hx






theorem acw_incidentFlux_internal_not_mem (S : Finset V) (n : Current V)
    {x : V} (hx : x ∉ S) :
    Sharpness.incidentFlux G (acwRestrict (acwInternal S) n) x = 0 := by
  unfold Sharpness.incidentFlux acwRestrict
  refine Finset.sum_eq_zero (fun e he => ?_)
  rw [Finset.mem_filter] at he
  obtain ⟨heG, hxe⟩ := he
  by_cases hint : acwInternal S e
  · exact absurd (hint x hxe) hx
  · simp [hint]







theorem acw_sources_internal_eq (S : Finset V) (hcut : acwClosedCut G S) (n : Current V) :
    Sharpness.sources G (acwRestrict (acwInternal S) n) = (Sharpness.sources G n) ∩ S := by
  ext x
  rw [Sharpness.mem_sources, Finset.mem_inter, Sharpness.mem_sources]
  by_cases hx : x ∈ S
  · rw [acw_incidentFlux_internal_mem G S hcut n hx]; simp [hx]
  · rw [acw_incidentFlux_internal_not_mem G S n hx]; simp [hx]





theorem acw_sources_external_eq (S : Finset V) (hcut : acwClosedCut G S) (n : Current V) :
    Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = (Sharpness.sources G n) ∩ Sᶜ := by
  have hcut' : acwClosedCut G Sᶜ := by
    intro e he
    rcases hcut e he with h | h
    · right; rwa [compl_compl]
    · left; exact h
  exact acw_sources_internal_eq G Sᶜ hcut' n








theorem acw_sources_partition (S : Finset V) (hcut : acwClosedCut G S) (n : Current V) :
    Sharpness.sources G n
      = Sharpness.sources G (acwRestrict (acwInternal S) n) ∪ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)
    ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n))
        (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)) := by
  rw [acw_sources_internal_eq G S hcut n, acw_sources_external_eq G S hcut n]
  refine ⟨?_, ?_⟩
  · rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
  · exact Finset.disjoint_left.2 (fun a ha hb =>
      (Finset.mem_compl.1 (Finset.mem_inter.1 hb).2) (Finset.mem_inter.1 ha).2)


























theorem acw_currentSum_eq_expectation (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) :
    Sharpness.currentSum G β J A = Sharpness.expectationJ G β J A * Sharpness.currentSum G β J ∅ := by
  rw [Sharpness.current_representation, div_mul_cancel₀ _ h0]














theorem acw_currentSum_ratio (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (h0 : Sharpness.currentSum G β J ∅ ≠ 0) (hA : Sharpness.expectationJ G β J A ≠ 0) :
    Sharpness.currentSum G β J B
      = (Sharpness.expectationJ G β J B / Sharpness.expectationJ G β J A)
        * Sharpness.currentSum G β J A := by
  rw [acw_currentSum_eq_expectation G β J B h0, acw_currentSum_eq_expectation G β J A h0]
  field_simp










open StatMech.Sharpness.RandomCurrent











theorem acw_crossClass_closure {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hratio : 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) :
    0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y :=
  aie_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hratio




















def acw_ratioFreeDom {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (o x y : V) (Φ : Finset ι → Finset ι → ℝ) : Prop :=
  2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
    ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A





theorem acw_ratioFreeDom_holds_of_no_allConn {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V) {o x y : V}
    (Φ : Finset ι → Finset ι → ℝ) (hΦnn : ∀ m K, 0 ≤ (Φ m) K)
    (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
    acw_ratioFreeDom ends M A o x y Φ := by
  unfold acw_ratioFreeDom
  rw [hno, Finset.sum_empty, mul_zero]
  exact Finset.sum_nonneg (fun m _ => aie_mass_nonneg ends m (Φ m) (hΦnn m) A)




















theorem acw_ratioFreeDom_refutable :
    ¬ acw_ratioFreeDom (V := Fin 3) ahd_triEnds
        ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
        (Sharpness.RandomCurrent.sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3)))
        0 1 2 (fun _ _ => 1) := by
  unfold acw_ratioFreeDom
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := Sharpness.RandomCurrent.sources ahd_triEnds m₀ with hA₀
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 := ahd_tri_allConn
  have hnotnone : ¬ aie_noneConn ahd_triEnds m₀ 0 1 2 := by
    rintro ⟨h1, _, _⟩; exact h1 hall.1
  rw [Finset.filter_singleton, if_pos hall, Finset.sum_singleton,
      Finset.filter_singleton, if_neg hnotnone, Finset.sum_empty] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith

end Ising

end StatMech
