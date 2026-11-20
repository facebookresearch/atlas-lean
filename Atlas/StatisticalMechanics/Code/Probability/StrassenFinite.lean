/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Code.Foundations.StrassenFull

open Finset
open scoped NNReal

namespace StatMech
namespace Probability

variable {P : Type*}








section Defs

variable [Fintype P]



structure IsCoupling [PartialOrder P] (μ ν : P → ℝ≥0) (π : P × P → ℝ≥0) : Prop where
  
  fst_marginal : ∀ x, ∑ y, π (x, y) = μ x
  
  snd_marginal : ∀ y, ∑ x, π (x, y) = ν y



structure IsMonotoneCoupling [PartialOrder P] (μ ν : P → ℝ≥0) (π : P × P → ℝ≥0) : Prop
    extends IsCoupling μ ν π where
  
  supported : ∀ x y, ¬ x ≤ y → π (x, y) = 0




def StochasticDom [Preorder P] (μ ν : P → ℝ≥0) : Prop :=
  ∀ U : Finset P, (∀ ⦃a b⦄, a ≤ b → a ∈ U → b ∈ U) → ∑ x ∈ U, μ x ≤ ∑ x ∈ U, ν x

end Defs



section Easy

variable [Fintype P] [PartialOrder P] [DecidableEq P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]

omit [DecidableEq P] in








theorem StochasticDom.of_isMonotoneCoupling {μ ν : P → ℝ≥0} {π : P × P → ℝ≥0}
    (h : IsMonotoneCoupling μ ν π) : StochasticDom μ ν := by
  intro U hU
  have hμU : ∑ x ∈ U, μ x = ∑ p ∈ U ×ˢ (univ : Finset P), π p := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun x _ => (h.fst_marginal x).symm)
  have hνU : ∑ y ∈ U, ν y = ∑ p ∈ (univ : Finset P) ×ˢ U, π p := by
    rw [Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => (h.snd_marginal y).symm)
  rw [hμU, hνU]
  
  have hLHS : ∑ p ∈ U ×ˢ (univ : Finset P), π p
      = ∑ p ∈ (U ×ˢ (univ : Finset P)).filter (fun p => p.1 ≤ p.2), π p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p.1 ≤ p.2
    · rw [if_pos hp]
    · rw [if_neg hp]; exact h.supported p.1 p.2 hp
  rw [hLHS]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hU hp.2 hp.1
  · intro p _ _; exact zero_le'

end Easy








section Hard

open Transport

variable [Fintype P] [DecidableEq P] [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]



private noncomputable def piOfVec (c : OrderPairs P → ℝ) : P × P → ℝ≥0 :=
  fun p => if h : p.1 ≤ p.2 then (c ⟨p, h⟩).toNNReal else 0

omit [Fintype P] [DecidableEq P] in
private theorem piOfVec_coe (c : OrderPairs P → ℝ) (hc : ∀ q, 0 ≤ c q) (p : P × P) :
    ((piOfVec c p : ℝ≥0) : ℝ) = if h : p.1 ≤ p.2 then c ⟨p, h⟩ else 0 := by
  unfold piOfVec
  by_cases h : p.1 ≤ p.2
  · rw [dif_pos h, dif_pos h, Real.coe_toNNReal _ (hc _)]
  · rw [dif_neg h, dif_neg h]; rfl

omit [Fintype P] [DecidableEq P] in
private theorem piOfVec_supp (c : OrderPairs P → ℝ) (x y : P) (h : ¬ x ≤ y) :
    piOfVec c (x, y) = 0 := by
  unfold piOfVec; rw [dif_neg h]



private theorem row_reindex (c : OrderPairs P → ℝ) (x : P) :
    (∑ y, if h : x ≤ y then c ⟨(x, y), h⟩ else 0)
      = ∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0 := by
  have hLHS : (∑ y, if h : x ≤ y then c ⟨(x, y), h⟩ else 0)
      = ∑ y ∈ univ.filter (fun y => x ≤ y), if h : x ≤ y then c ⟨(x, y), h⟩ else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : x ≤ y
    · rw [if_pos h]
    · rw [if_neg h, dif_neg h]
  rw [hLHS, ← Finset.sum_filter]
  refine Finset.sum_bij'
    (i := fun (y : P) (hy : y ∈ univ.filter (fun y => x ≤ y)) =>
      (⟨(x, y), (Finset.mem_filter.mp hy).2⟩ : OrderPairs P))
    (j := fun (q : OrderPairs P) (_ : q ∈ univ.filter (fun q : OrderPairs P => (q : P × P).1 = x)) =>
      (q : P × P).2)
    ?_ ?_ ?_ ?_ ?_
  · intro y _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hx := (Finset.mem_filter.mp hq).2
    rw [← hx]; exact q.2
  · intro _ _; rfl
  · intro q hq
    have hx := (Finset.mem_filter.mp hq).2
    apply Subtype.ext
    show ((x, (q : P × P).2) : P × P) = (q : P × P)
    rw [← hx]
  · intro y hy
    have hy2 := (Finset.mem_filter.mp hy).2
    rw [dif_pos hy2]



private theorem col_reindex (c : OrderPairs P → ℝ) (y : P) :
    (∑ x, if h : x ≤ y then c ⟨(x, y), h⟩ else 0)
      = ∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0 := by
  have hLHS : (∑ x, if h : x ≤ y then c ⟨(x, y), h⟩ else 0)
      = ∑ x ∈ univ.filter (fun x => x ≤ y), if h : x ≤ y then c ⟨(x, y), h⟩ else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : x ≤ y
    · rw [if_pos h]
    · rw [if_neg h, dif_neg h]
  rw [hLHS, ← Finset.sum_filter]
  refine Finset.sum_bij'
    (i := fun (x : P) (hx : x ∈ univ.filter (fun x => x ≤ y)) =>
      (⟨(x, y), (Finset.mem_filter.mp hx).2⟩ : OrderPairs P))
    (j := fun (q : OrderPairs P) (_ : q ∈ univ.filter (fun q : OrderPairs P => (q : P × P).2 = y)) =>
      (q : P × P).1)
    ?_ ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hy := (Finset.mem_filter.mp hq).2
    rw [← hy]; exact q.2
  · intro _ _; rfl
  · intro q hq
    have hy := (Finset.mem_filter.mp hq).2
    apply Subtype.ext
    show (((q : P × P).1, y) : P × P) = (q : P × P)
    rw [← hy]
  · intro x hx
    have hx2 := (Finset.mem_filter.mp hx).2
    rw [dif_pos hx2]

omit [DecidableRel ((· ≤ ·) : P → P → Prop)] in


private theorem down_dom_of_stochasticDom {μ ν : P → ℝ≥0}
    (hTOT : ∑ x, μ x = ∑ x, ν x) (hSD : StochasticDom μ ν)
    (D : Finset P) (hD : Transport.IsDown D) :
    ∑ x ∈ D, (ν x : ℝ) ≤ ∑ x ∈ D, (μ x : ℝ) := by
  
  have hUup : ∀ ⦃a b⦄, a ≤ b → a ∈ Dᶜ → b ∈ Dᶜ := by
    intro a b hab haU
    rw [Finset.mem_compl] at haU ⊢
    exact fun hbD => haU (hD a b hab hbD)
  have hkey := hSD Dᶜ hUup
  have splitμ : ∑ x, μ x = ∑ x ∈ D, μ x + ∑ x ∈ Dᶜ, μ x := (Finset.sum_add_sum_compl D μ).symm
  have splitν : ∑ x, ν x = ∑ x ∈ D, ν x + ∑ x ∈ Dᶜ, ν x := (Finset.sum_add_sum_compl D ν).symm
  
  have hkeyR : (∑ x ∈ Dᶜ, μ x : ℝ) ≤ (∑ x ∈ Dᶜ, ν x : ℝ) := by exact_mod_cast hkey
  have splitμR : (∑ x, μ x : ℝ) = (∑ x ∈ D, μ x : ℝ) + (∑ x ∈ Dᶜ, μ x : ℝ) := by
    exact_mod_cast splitμ
  have splitνR : (∑ x, ν x : ℝ) = (∑ x ∈ D, ν x : ℝ) + (∑ x ∈ Dᶜ, ν x : ℝ) := by
    exact_mod_cast splitν
  have hTOTR : (∑ x, μ x : ℝ) = (∑ x, ν x : ℝ) := by exact_mod_cast hTOT
  push_cast at *
  linarith




theorem exists_isMonotoneCoupling_of_stochasticDom {μ ν : P → ℝ≥0}
    (hTOT : ∑ x, μ x = ∑ x, ν x) (hSD : StochasticDom μ ν) :
    ∃ π : P × P → ℝ≥0, IsMonotoneCoupling μ ν π := by
  rcases isEmpty_or_nonempty P with hP | hP
  · 
    refine ⟨fun _ => 0, ⟨⟨fun x => (IsEmpty.false x).elim, fun y => (IsEmpty.false y).elim⟩,
      fun x => (IsEmpty.false x).elim⟩⟩
  · 
    have hTOTR : ∑ x, ((μ x : ℝ)) = ∑ x, ((ν x : ℝ)) := by exact_mod_cast hTOT
    obtain ⟨c, hcpos, hrow, hcol⟩ :=
      Transport.exists_coupling_vec (P := P) (fun x => (μ x : ℝ)) (fun y => (ν y : ℝ))
        (fun x => (μ x).coe_nonneg) (fun y => (ν y).coe_nonneg) hTOTR
        (fun D hD => down_dom_of_stochasticDom hTOT hSD D hD)
    refine ⟨piOfVec c, ⟨⟨fun x => ?_, fun y => ?_⟩, fun x y h => piOfVec_supp c x y h⟩⟩
    · 
      have hcoe : ((∑ y, piOfVec c (x, y) : ℝ≥0) : ℝ) = (μ x : ℝ) := by
        push_cast
        rw [Finset.sum_congr rfl (fun y _ => piOfVec_coe c hcpos (x, y)),
          row_reindex c x, hrow x]
      exact_mod_cast hcoe
    · 
      have hcoe : ((∑ x, piOfVec c (x, y) : ℝ≥0) : ℝ) = (ν y : ℝ) := by
        push_cast
        rw [Finset.sum_congr rfl (fun x _ => piOfVec_coe c hcpos (x, y)),
          col_reindex c y, hcol y]
      exact_mod_cast hcoe

end Hard



section Iff

variable [Fintype P] [DecidableEq P] [PartialOrder P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]











theorem strassen_finite {μ ν : P → ℝ≥0} (hTOT : ∑ x, μ x = ∑ x, ν x) :
    StochasticDom μ ν ↔ ∃ π : P × P → ℝ≥0, IsMonotoneCoupling μ ν π := by
  constructor
  · intro hSD; exact exists_isMonotoneCoupling_of_stochasticDom hTOT hSD
  · rintro ⟨π, hπ⟩; exact StochasticDom.of_isMonotoneCoupling hπ

end Iff

end Probability
end StatMech
