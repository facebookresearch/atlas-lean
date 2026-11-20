/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Ising.TwoReplica
import Code.Ising.TwoReplicaWeighted
import Code.Ising.AizenmanSignDominance
import Code.Ising.HdomNativeWeight

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]













noncomputable def restrictCut (n : Current V) (p : Sym2 V → Prop) [DecidablePred p] : Current V :=
  fun e => if p e then n e else 0



theorem bbr_restrict_le (n : Current V) (p : Sym2 V → Prop) [DecidablePred p] (e : Sym2 V) :
    restrictCut n p e ≤ n e := by
  unfold restrictCut; by_cases h : p e <;> simp [h]







theorem bbr_cut_split (n : Current V) (p : Sym2 V → Prop) [DecidablePred p] :
    (fun e => restrictCut n p e + restrictCut n (fun e => ¬ p e) e) = n := by
  funext e; unfold restrictCut; by_cases h : p e <;> simp [h]














theorem bbr_weight_cut_factor (β : ℝ) (J : Sym2 V → ℝ) (n : Current V)
    (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.weight G β J n
      = Sharpness.weight G β J (restrictCut n p)
        * Sharpness.weight G β J (restrictCut n (fun e => ¬ p e)) := by
  unfold Sharpness.weight restrictCut
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  by_cases h : p e
  · rw [if_pos h, if_neg (not_not_intro h)]; simp
  · rw [if_neg h, if_pos h]; simp









theorem bbr_sources_cut_split (n : Current V) (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.sources G n
      = Sharpness.sources G (restrictCut n p)
        ∆ Sharpness.sources G (restrictCut n (fun e => ¬ p e)) := by
  conv_lhs => rw [← bbr_cut_split n p]
  exact sources_add G.edgeFinset (restrictCut n p) (restrictCut n (fun e => ¬ p e))


















theorem bbr_mass_eq_weight_mul_count (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V) :
    hnw_mass G β J m A
      = Sharpness.weight G β J m
        * ∑ K : {K : Current V // ∀ e, K e ≤ m e},
            (if Sharpness.sources G K.1 = A
              then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) :=
  hnw_mass_eq_weight_mul_count G β J m A



theorem bbr_mass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (S : Finset V) : 0 ≤ hnw_mass G β J m S :=
  hnw_mass_nonneg G β J hβ hJ m S





















theorem bbr_inj_domination {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → ℝ) (g : β → ℝ) (Ψ : α → β)
    (hΨmem : ∀ a ∈ S, Ψ a ∈ T)
    (hΨinj : ∀ a ∈ S, ∀ a' ∈ S, Ψ a = Ψ a' → a = a')
    (hgnn : ∀ b ∈ T, 0 ≤ g b)
    (hbound : ∀ a ∈ S, 2 * f a ≤ g (Ψ a)) :
    2 * (∑ a ∈ S, f a) ≤ ∑ b ∈ T, g b := by
  have h1 : 2 * (∑ a ∈ S, f a) ≤ ∑ a ∈ S, g (Ψ a) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun a ha => hbound a ha)
  have h2 : ∑ a ∈ S, g (Ψ a) = ∑ b ∈ S.image Ψ, g b := by
    rw [Finset.sum_image]; intro a ha a' ha' h; exact hΨinj a ha a' ha' h
  have h3 : ∑ b ∈ S.image Ψ, g b ≤ ∑ b ∈ T, g b := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb; rw [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb; exact hΨmem a ha
    · intro b hb _; exact hgnn b hb
  rw [h2] at h1; linarith










noncomputable def bbr_allFilter (M : Finset (Current V)) (o x y : V) : Finset (Current V) :=
  M.filter (fun m => hnw_allConn G m o x y)



noncomputable def bbr_noneFilter (M : Finset (Current V)) (o x y : V) : Finset (Current V) :=
  M.filter (fun m => hnw_noneConn G m o x y)













def bbr_BackboneSurgery (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (A : Finset V)
    (o x y : V) : Prop :=
  ∃ Ψ : Current V → Current V,
    (∀ m ∈ bbr_allFilter G M o x y, Ψ m ∈ bbr_noneFilter G M o x y)
    ∧ (∀ m ∈ bbr_allFilter G M o x y, ∀ m' ∈ bbr_allFilter G M o x y, Ψ m = Ψ m' → m = m')
    ∧ (∀ m ∈ bbr_allFilter G M o x y, 2 * hnw_mass G β J m A ≤ hnw_mass G β J (Ψ m) A)











theorem bbr_surgery_satisfiable (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (A : Finset V)
    (o x y : V) (hno : bbr_allFilter G M o x y = ∅) :
    bbr_BackboneSurgery G β J M A o x y := by
  refine ⟨id, ?_, ?_, ?_⟩ <;> rw [hno] <;> intro m hm <;> simp at hm











theorem bbr_hdom_of_surgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (A : Finset V) (o x y : V)
    (hsurg : bbr_BackboneSurgery G β J M A o x y) :
    2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A := by
  obtain ⟨Ψ, hΨmem, hΨinj, hbound⟩ := hsurg
  have hgnn : ∀ b ∈ bbr_noneFilter G M o x y, 0 ≤ hnw_mass G β J b A := by
    intro b _; exact bbr_mass_nonneg G β J hβ hJ b A
  have := bbr_inj_domination (bbr_allFilter G M o x y) (bbr_noneFilter G M o x y)
    (fun m => hnw_mass G β J m A) (fun m => hnw_mass G β J m A) Ψ hΨmem hΨinj hgnn hbound
  simpa only [bbr_allFilter, bbr_noneFilter] using this














theorem bbr_closure_of_surgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hsurg : bbr_BackboneSurgery G β J M A o x y) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y :=
  hnw_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh
    (bbr_hdom_of_surgery G β J hβ hJ M A o x y hsurg)










theorem bbr_ghs_of_surgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hsurg : bbr_BackboneSurgery G β J M A o x y) :
    (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}))
      ≤ ∑ m ∈ M, hnw_mass G β J m A :=
  hnw_ghs_distinct_site_of_hdom G β J M hnd A hm hox hoy hxy hcoh
    (bbr_hdom_of_surgery G β J hβ hJ M A o x y hsurg)

end Ising

end StatMech
