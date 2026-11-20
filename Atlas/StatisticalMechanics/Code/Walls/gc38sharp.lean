/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Walls.gc37hdom

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict











section Abstract

variable {ι W : Type*} [DecidableEq ι] [DecidableEq W] [Fintype W] [Fintype ι]




theorem gc38_comp_sources_even (ends : ι → Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (u : W) :
    Even (#((RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K))) := by
  have h1 : Even (#((RandomCurrent.compOf ends K u).filter (fun z => Odd (RandomCurrent.degK ends K z)))) :=
    (RandomCurrent.even_sum_iff_even_count _ _).1 (RandomCurrent.sum_deg_comp_even ends K hnd u)
  have hset : (RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K)
      = (RandomCurrent.compOf ends K u).filter (fun z => Odd (RandomCurrent.degK ends K z)) := by
    apply Finset.filter_congr; intro z _; simp [RandomCurrent.mem_sources]
  rw [hset]; exact h1




theorem gc38_comp_source_count (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
    (hsrc : RandomCurrent.sources ends K = {o, x, y, g}) (u : W) :
    #((RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K))
      = (if RandomCurrent.connK ends K u o then 1 else 0) + (if RandomCurrent.connK ends K u x then 1 else 0)
        + (if RandomCurrent.connK ends K u y then 1 else 0) + (if RandomCurrent.connK ends K u g then 1 else 0) := by
  obtain ⟨hox, hoy, hog, hxy, hxg, hyg⟩ := hdist
  rw [show (RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K)
        = (({o, x, y, g} : Finset W)).filter (fun z => RandomCurrent.connK ends K u z) from ?_]
  · rw [Finset.card_filter, Finset.sum_insert (by simp [hox, hoy, hog]),
      Finset.sum_insert (by simp [hxy, hxg]), Finset.sum_insert (by simp [hyg]),
      Finset.sum_singleton]
    ring
  · ext z; simp only [Finset.mem_filter, RandomCurrent.mem_compOf, hsrc]; tauto












theorem gc38_disconn_triple_identity (ends : ι → Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) {o x y g : W}
    (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
    (hsrc : RandomCurrent.sources ends K = {o, x, y, g}) :
    (if ¬ RandomCurrent.connK ends K x y then (1 : ℝ) else 0)
      + (if ¬ RandomCurrent.connK ends K y g then 1 else 0)
      + (if ¬ RandomCurrent.connK ends K x g then 1 else 0)
      = 2 * (if ¬ (RandomCurrent.connK ends K o x ∧ RandomCurrent.connK ends K o y ∧ RandomCurrent.connK ends K o g) then 1 else 0) := by
  obtain ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ := hdist
  have po := gc38_comp_sources_even ends K hnd o
  have px := gc38_comp_sources_even ends K hnd x
  have py := gc38_comp_sources_even ends K hnd y
  rw [gc38_comp_source_count ends K ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ hsrc o] at po
  rw [gc38_comp_source_count ends K ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ hsrc x] at px
  rw [gc38_comp_source_count ends K ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ hsrc y] at py
  have coo : RandomCurrent.connK ends K o o := Relation.ReflTransGen.refl
  have cxx : RandomCurrent.connK ends K x x := Relation.ReflTransGen.refl
  have cyy : RandomCurrent.connK ends K y y := Relation.ReflTransGen.refl
  have link : ∀ a b, RandomCurrent.connK ends K o a → RandomCurrent.connK ends K o b → RandomCurrent.connK ends K a b :=
    fun a b h1 h2 => Relation.ReflTransGen.trans (RandomCurrent.connK_symm ends K h1) h2
  have nolink : ∀ a b, RandomCurrent.connK ends K o a → ¬ RandomCurrent.connK ends K o b → ¬ RandomCurrent.connK ends K a b :=
    fun a b h1 hnb hab => hnb (Relation.ReflTransGen.trans h1 hab)
  have csym : ∀ a b : W, RandomCurrent.connK ends K a b ↔ RandomCurrent.connK ends K b a :=
    fun a b => ⟨RandomCurrent.connK_symm ends K, RandomCurrent.connK_symm ends K⟩
  by_cases hoxc : RandomCurrent.connK ends K o x <;> by_cases hoyc : RandomCurrent.connK ends K o y <;>
    by_cases hogc : RandomCurrent.connK ends K o g <;>
    simp only [hoxc, hoyc, hogc, coo, cxx, cyy, if_true, if_false, and_true,
      not_false_iff, mul_one, csym x o, csym y o, csym y x] at po px py ⊢
  all_goals try (exfalso; revert po; decide)
  · 
    rw [if_neg (not_not.mpr (link x y hoxc hoyc)), if_neg (not_not.mpr (link y g hoyc hogc)),
      if_neg (not_not.mpr (link x g hoxc hogc))]
    norm_num
  · 
    have hxy_dis : ¬ RandomCurrent.connK ends K x y := nolink x y hoxc hoyc
    have hxg_dis : ¬ RandomCurrent.connK ends K x g := nolink x g hoxc hogc
    simp only [hxy_dis, if_false] at py
    have hyg : RandomCurrent.connK ends K y g := by
      revert py; by_cases h : RandomCurrent.connK ends K y g <;> simp [h]
    rw [if_pos hxy_dis, if_neg (not_not.mpr hyg), if_pos hxg_dis]
    norm_num
  · 
    have hyx_dis : ¬ RandomCurrent.connK ends K y x := nolink y x hoyc hoxc
    have hxy_dis : ¬ RandomCurrent.connK ends K x y := fun h => hyx_dis (RandomCurrent.connK_symm ends K h)
    have hyg_dis : ¬ RandomCurrent.connK ends K y g := nolink y g hoyc hogc
    simp only [hxy_dis, if_false] at px
    have hxg : RandomCurrent.connK ends K x g := by
      revert px; by_cases h : RandomCurrent.connK ends K x g <;> simp [h]
    rw [if_pos hxy_dis, if_pos hyg_dis, if_neg (not_not.mpr hxg)]
    norm_num
  · 
    have hgx_dis : ¬ RandomCurrent.connK ends K g x := nolink g x hogc hoxc
    have hxg_dis : ¬ RandomCurrent.connK ends K x g := fun h => hgx_dis (RandomCurrent.connK_symm ends K h)
    have hgy_dis : ¬ RandomCurrent.connK ends K g y := nolink g y hogc hoyc
    have hyg_dis : ¬ RandomCurrent.connK ends K y g := fun h => hgy_dis (RandomCurrent.connK_symm ends K h)
    simp only [hxg_dis, if_false] at px
    have hxy : RandomCurrent.connK ends K x y := by
      revert px; by_cases h : RandomCurrent.connK ends K x y <;> simp [h]
    rw [if_neg (not_not.mpr hxy), if_pos hyg_dis, if_pos hxg_dis]
    norm_num

end Abstract








variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open StatMech.Sharpness (ofEdgeFun weight currentSum sourcePairSum)
open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_edgecopy sourcePairSum_eq_edgecopy)




noncomputable def gc38_sourcePairAllConnSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (o x y g : V) : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
        * (if sources G (ofEdgeFun G pq.2) = (∅ : Finset V) then weight G β J (ofEdgeFun G pq.2) else 0))
      * (if CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o g then 1 else 0)



theorem gc38_sourcePairAllConnSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) (o x y g : V) : 0 ≤ gc38_sourcePairAllConnSum G β J A o x y g := by
  unfold gc38_sourcePairAllConnSum
  refine tsum_nonneg (fun z => ?_)
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · by_cases h : sources G (ofEdgeFun G z.1) = A
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : sources G (ofEdgeFun G z.2) = (∅ : Finset V)
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) o x
        ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) o y
        ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) o g <;> simp [h]






theorem gc38_allConnSum_eq_edgecopy (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (o x y g : V) :
    gc38_sourcePairAllConnSum G β J A o x y g
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ S : Finset (Copy G m),
            (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
              * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                    ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
          * weight G β J (ofEdgeFun G m) := by
  classical
  unfold gc38_sourcePairAllConnSum
  rw [FluxEdgeCopy.sourcePairSum_conv_factor G β J A ∅
    (fun m => if CurrentConnected G (ofEdgeFun G m) o x ∧ CurrentConnected G (ofEdgeFun G m) o y
        ∧ CurrentConnected G (ofEdgeFun G m) o g then 1 else 0)
    (fun m => by
      by_cases h : CurrentConnected G (ofEdgeFun G m) o x ∧ CurrentConnected G (ofEdgeFun G m) o y
          ∧ CurrentConnected G (ofEdgeFun G m) o g <;> simp [h])]
  refine tsum_congr (fun m => ?_)
  rw [Finset.sum_mul]
  
  
  rw [show (if CurrentConnected G (ofEdgeFun G m) o x ∧ CurrentConnected G (ofEdgeFun G m) o y
        ∧ CurrentConnected G (ofEdgeFun G m) o g then (1 : ℝ) else 0)
      = (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
        ∧ RandomCurrent.connK (endsM G m) univ o g then (1 : ℝ) else 0) from by
    rw [FluxEdgeCopy.connK_univ_iff, FluxEdgeCopy.connK_univ_iff, FluxEdgeCopy.connK_univ_iff]]
  by_cases hC : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
      ∧ RandomCurrent.connK (endsM G m) univ o g
  · rw [if_pos hC]
    simp only [mul_one]
    exact FluxEdgeCopy.sourcePair_superposition_bridge G β J A ∅ m
  · rw [if_neg hC]
    simp only [mul_zero, Finset.sum_const_zero, zero_mul]









open StatMech.Sharpness.GhostCurrentRep (gcr_pairCount_empty gcr_pairCount_disconn
  gcr_summable_edgecopy gcr_summable_edgecopy_disconn)










theorem gc38_perSuperposition_assembly (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ)
    {o x y g : V} (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g) :
    ((∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if ¬ RandomCurrent.connK (endsM G m) univ x y then 1 else 0))
      + (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if ¬ RandomCurrent.connK (endsM G m) univ y g then 1 else 0))
      + (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if ¬ RandomCurrent.connK (endsM G m) univ x g then 1 else 0)))
      = 2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
        - 2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)) := by
  classical
  obtain ⟨hox, hoy, hog, hxy, hxg, hyg⟩ := hdist
  rw [gcr_pairCount_disconn G m ({o, x, y, g} : Finset V) x y,
    gcr_pairCount_disconn G m ({o, x, y, g} : Finset V) y g,
    gcr_pairCount_disconn G m ({o, x, y, g} : Finset V) x g,
    gcr_pairCount_empty G m ({o, x, y, g} : Finset V)]
  
  rw [show (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
        = (if RandomCurrent.sources (endsM G m) univ = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
          * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                ∧ RandomCurrent.connK (endsM G m) univ o g then (1 : ℝ) else 0)
          * (#((univ : Finset (Copy G m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM G m) K = ({o, x, y, g} : Finset V))) : ℝ)
      from by
        rw [show (∑ S : Finset (Copy G m),
              (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
                * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
                * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                      ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
            = (∑ S : Finset (Copy G m),
                (if RandomCurrent.sources (endsM G m) S = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
                  * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
              * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                    ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)
          from by rw [Finset.sum_mul]]
        rw [gcr_pairCount_empty G m ({o, x, y, g} : Finset V)]; ring]
  by_cases hAm : RandomCurrent.sources (endsM G m) univ = ({o, x, y, g} : Finset V)
  · rw [if_pos hAm]
    have hsrc : RandomCurrent.sources (endsM G m) univ = ({o, x, y, g} : Finset V) := hAm
    have hparity := gc38_disconn_triple_identity (endsM G m) (univ : Finset (Copy G m))
      (fun i _ => endsM_not_isDiag G m i) ⟨hox, hoy, hog, hxy, hxg, hyg⟩ hsrc
    
    set c : ℝ := (#((univ : Finset (Copy G m)).powerset.filter
        (fun K => RandomCurrent.sources (endsM G m) K = ({o, x, y, g} : Finset V))) : ℝ) with hc
    
    have hneg : (if ¬ (RandomCurrent.connK (endsM G m) univ o x
          ∧ RandomCurrent.connK (endsM G m) univ o y ∧ RandomCurrent.connK (endsM G m) univ o g)
          then (1 : ℝ) else 0)
        = 1 - (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
              ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0) := by
      by_cases h : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
          ∧ RandomCurrent.connK (endsM G m) univ o g <;> simp [h]
    rw [hneg] at hparity
    
    have key := congrArg (fun t => t * c) hparity
    simp only at key
    linarith [key]
  · rw [if_neg hAm]
    simp only [zero_mul, mul_zero, add_zero, sub_zero]



theorem gc38_summable_edgecopy_allConn (β : ℝ) (J : Sym2 V → ℝ) (hJnn : ∀ e, 0 ≤ J e) (hβ : 0 ≤ β)
    (A : Finset V) (o x y g : V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      (∑ S : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
          * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
          * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
      * weight G β J (ofEdgeFun G m)) := by
  classical
  have hw : ∀ m : ↥G.edgeFinset → ℕ, 0 ≤ weight G β J (ofEdgeFun G m) := by
    intro m; unfold weight
    refine Finset.prod_nonneg (fun e _ => ?_)
    have hbJ : 0 ≤ β * J e := mul_nonneg hβ (hJnn e); positivity
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (gcr_summable_edgecopy G β J A ∅)
  · 
    apply mul_nonneg _ (hw m)
    refine Finset.sum_nonneg (fun S _ => ?_)
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · by_cases h : RandomCurrent.sources (endsM G m) S = A <;> simp [h]
    · by_cases h : RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) <;> simp [h]
    · by_cases h : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
          ∧ RandomCurrent.connK (endsM G m) univ o g <;> simp [h]
  · 
    apply mul_le_mul_of_nonneg_right _ (hw m)
    refine Finset.sum_le_sum (fun S _ => ?_)
    have hbase : (0 : ℝ) ≤ (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
        * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0) := by
      refine mul_nonneg ?_ ?_
      · by_cases h : RandomCurrent.sources (endsM G m) S = A <;> simp [h]
      · by_cases h : RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) <;> simp [h]
    by_cases h : RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
        ∧ RandomCurrent.connK (endsM G m) univ o g
    · rw [if_pos h, mul_one]
    · rw [if_neg h, mul_zero]; exact hbase








theorem gc38_disconnSum_triple_eq (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    {o x y g : V} (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g) :
    sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ x y
      + sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ y g
      + sourcePairDisconnSum G β J ({o, x, y, g} : Finset V) ∅ x g
      = 2 * sourcePairSum G β J ({o, x, y, g} : Finset V) ∅
        - 2 * gc38_sourcePairAllConnSum G β J ({o, x, y, g} : Finset V) o x y g := by
  classical
  set A : Finset V := {o, x, y, g} with hA
  
  rw [sourcePairDisconnSum_eq_edgecopy G β J A ∅ x y,
    sourcePairDisconnSum_eq_edgecopy G β J A ∅ y g,
    sourcePairDisconnSum_eq_edgecopy G β J A ∅ x g,
    sourcePairSum_eq_edgecopy G β J A ∅,
    gc38_allConnSum_eq_edgecopy G β J A o x y g]
  
  rw [← Summable.tsum_add (gcr_summable_edgecopy_disconn G β J hJ hβ A x y)
        (gcr_summable_edgecopy_disconn G β J hJ hβ A y g),
    ← Summable.tsum_add
        (Summable.add (gcr_summable_edgecopy_disconn G β J hJ hβ A x y)
          (gcr_summable_edgecopy_disconn G β J hJ hβ A y g))
        (gcr_summable_edgecopy_disconn G β J hJ hβ A x g)]
  
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_sub
      ((gcr_summable_edgecopy G β J A ∅).mul_left 2)
      ((gc38_summable_edgecopy_allConn G β J hJ hβ A o x y g).mul_left 2)]
  refine tsum_congr (fun m => ?_)
  
  have hassembly := gc38_perSuperposition_assembly G β J m hdist
  
  rw [show (2 : ℝ) * ((∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
        * weight G β J (ofEdgeFun G m))
      - 2 * ((∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0))
        * weight G β J (ofEdgeFun G m))
      = (2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0))
        - 2 * (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = (∅ : Finset V) then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ o x ∧ RandomCurrent.connK (endsM G m) univ o y
                  ∧ RandomCurrent.connK (endsM G m) univ o g then 1 else 0)))
        * weight G β J (ofEdgeFun G m) from by ring]
  rw [← hassembly, add_mul, add_mul]











private theorem gc38_sd_xy {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) :
    ({some o, some x, some y, none} : Finset (Option V)) ∆ ({some x, some y} : Finset (Option V))
      = ({some o, none} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl) <;> simp_all


private theorem gc38_sd_yg {o x y : V} (hoy : o ≠ y) (hxy : x ≠ y) :
    ({some o, some x, some y, none} : Finset (Option V)) ∆ ({some y, none} : Finset (Option V))
      = ({some o, some x} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl) <;> simp_all


private theorem gc38_sd_xg {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) :
    ({some o, some x, some y, none} : Finset (Option V)) ∆ ({some x, none} : Finset (Option V))
      = ({some o, some y} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl) <;> simp_all [hxy.symm]







theorem gc38_Z0sq_U4_eq_neg_two_allConn (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y
      = -2 * gc38_sourcePairAllConnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none := by
  classical
  set J : Sym2 (Option V) → ℝ := ghostCoupling h β (fun _ => 1) with hJ
  set A : Finset (Option V) := {some o, some x, some y, none} with hA
  have hJnn : ∀ e, (0 : ℝ) ≤ J e := gc6_ghostCoupling_nonneg (V := V) β h hh
  
  have hdist : (some o : Option V) ≠ some x ∧ (some o : Option V) ≠ some y ∧ (some o : Option V) ≠ none
      ∧ (some x : Option V) ≠ some y ∧ (some x : Option V) ≠ none ∧ (some y : Option V) ≠ none := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hox, hoy, hxy]
  
  have hU4 : (gc15_Z0 G β h) ^ 2 * gc37_U4 G β h o x y
      = (gc15_Z0 G β h) * currentSum (withGhost G) β J
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - currentSum (withGhost G) β J (insert (none : Option V) (({o} : Finset V).map someEmb))
            * currentSum (withGhost G) β J (({x, y} : Finset V).map someEmb)
        - currentSum (withGhost G) β J (({o, x} : Finset V).map someEmb)
            * currentSum (withGhost G) β J (insert (none : Option V) (({y} : Finset V).map someEmb))
        - currentSum (withGhost G) β J (({o, y} : Finset V).map someEmb)
            * currentSum (withGhost G) β J (insert (none : Option V) (({x} : Finset V).map someEmb)) :=
    gc37_Z0sq_U4 G β h o x y hox hoy hxy
  simp only [gc15_gsingle, gc15_gpair, gc15_gquad] at hU4
  
  have hZ0 : gc15_Z0 G β h = currentSum (withGhost G) β J ∅ := by rw [gc15_Z0, hJ]
  have g1 := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J A
      (u := some x) (v := some y) (by simp [hxy])
  have g2 := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J A
      (u := some y) (v := none) (by simp)
  have g3 := GhostCurrentRep.gcr_currentSum_ghostRep (withGhost G) β J A
      (u := some x) (v := none) (by simp)
  rw [gc38_sd_xy hox hoy] at g1
  rw [gc38_sd_yg hoy hxy] at g2
  rw [gc38_sd_xg hox hxy] at g3
  
  have hparity := gc38_disconnSum_triple_eq (withGhost G) β J hβ hJnn hdist
  
  rw [hU4, hZ0]
  
  have hsps := StatMech.Sharpness.sourcePairSum_eq_mul (withGhost G) β J A ∅
  linarith [g1, g2, g3, hparity, hsps]







theorem gc38_U4_nonpos_unconditional (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc37_U4 G β h o x y ≤ 0 := by
  have hid := gc38_Z0sq_U4_eq_neg_two_allConn G β h hβ hh o x y hox hoy hxy
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ2 : 0 < (gc15_Z0 G β h) ^ 2 := by positivity
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  have hconn := gc38_sourcePairAllConnSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1))
    hβ hJnn ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none
  nlinarith [hid, hconn, hZ2]







theorem gc38_U4_nonpos_replaces_connRep_hypothesis (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc37_U4 G β h o x y ≤ 0 :=
  gc38_U4_nonpos_unconditional G β h hβ hh o x y hox hoy hxy















def gc38_SharpGHSResidue (β h : ℝ) (o x y : V) : Prop :=
  gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y




theorem gc38_ursell3_nonpos_of_sharpResidue (β h : ℝ) (o x y : V)
    (hres : gc38_SharpGHSResidue G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  (gc37_ursell3_nonpos_iff_sharp G β h o x y).mpr hres






theorem gc38_sharp_gap_is_two_triple (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc37_U4 G β h o x y ≤ 0 ∧ 0 ≤ gc37_triple G β h o x y
      ∧ (gc38_SharpGHSResidue G β h o x y ↔ eg_ursell3 G β h o x y ≤ 0) := by
  refine ⟨gc38_U4_nonpos_unconditional G β h hβ hh o x y hox hoy hxy,
    gc37_triple_nonneg G β h hβ hh o x y, ?_⟩
  rw [gc38_SharpGHSResidue, ← gc37_ursell3_nonpos_iff_sharp]










theorem gc38_sharpResidue_at_zero (β : ℝ) (o x y : V) :
    gc38_SharpGHSResidue G β 0 o x y := by
  rw [gc38_SharpGHSResidue, gc37_U4_eq_neg_two_triple_at_zero]

end StatMech.Walls
