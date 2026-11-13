/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Ising.KWSelfDuality
import Code.Ising.KWDualBijection
import Code.Ising.KramersWannierClose

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising



section Spaces

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]



noncomputable def cutSpace : Finset (Finset (Sym2 V)) :=
  Finset.univ.image (fun s : ConfigSpace V => cutEdges Gp s)



noncomputable def evenSubgraphs : Finset (Finset (Sym2 V)) :=
  Gd.edgeFinset.powerset.filter IsEvenSubgraph

end Spaces







section Fiber

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj]





theorem cut_gen_eq_fiber_sum (t : ℝ) :
    (∑ s : ConfigSpace V, t ^ (cutEdges Gp s).card)
      = ∑ δ ∈ cutSpace Gp,
          ((Finset.univ.filter (fun s : ConfigSpace V => cutEdges Gp s = δ)).card : ℝ)
            * t ^ δ.card := by
  have hmaps : ∀ s ∈ (Finset.univ : Finset (ConfigSpace V)), cutEdges Gp s ∈ cutSpace Gp := by
    intro s _
    rw [cutSpace, Finset.mem_image]
    exact ⟨s, Finset.mem_univ s, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun δ => t ^ δ.card)]
  apply Finset.sum_congr rfl
  intro δ _
  rw [Finset.sum_const, nsmul_eq_mul]





theorem cut_gen_eq_mult (t mult : ℝ)
    (hfib : ∀ δ ∈ cutSpace Gp,
      ((Finset.univ.filter (fun s : ConfigSpace V => cutEdges Gp s = δ)).card : ℝ) = mult) :
    (∑ s : ConfigSpace V, t ^ (cutEdges Gp s).card)
      = mult * ∑ δ ∈ cutSpace Gp, t ^ δ.card := by
  rw [cut_gen_eq_fiber_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [hfib δ hδ]



omit [DecidableEq V] in


theorem mem_cutEdges_iff (s : ConfigSpace V) {x y : V} (hadj : Gp.Adj x y) :
    s(x, y) ∈ cutEdges Gp s ↔ s x ≠ s y := by
  unfold cutEdges
  rw [Finset.mem_filter, bond_mk]
  have hin : s(x, y) ∈ Gp.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj
  unfold spin
  by_cases hx : s x <;> by_cases hy : s y <;>
    simp only [hx, hy, hin, true_and, if_true, ne_eq] <;> norm_num

omit [DecidableEq V] in



theorem agree_adj {s₁ s₂ : ConfigSpace V} (hcut : cutEdges Gp s₁ = cutEdges Gp s₂)
    {x y : V} (hadj : Gp.Adj x y) :
    (s₁ x = s₂ x) ↔ (s₁ y = s₂ y) := by
  have h1 := mem_cutEdges_iff Gp s₁ hadj
  have h2 := mem_cutEdges_iff Gp s₂ hadj
  rw [hcut] at h1
  have hxor : (s₁ x ≠ s₁ y) ↔ (s₂ x ≠ s₂ y) := h1.symm.trans h2
  revert hxor
  cases s₁ x <;> cases s₁ y <;> cases s₂ x <;> cases s₂ y <;> simp

omit [DecidableEq V] in


theorem agree_walk {s₁ s₂ : ConfigSpace V} (hcut : cutEdges Gp s₁ = cutEdges Gp s₂)
    {x y : V} (w : Gp.Walk x y) :
    (s₁ x = s₂ x) ↔ (s₁ y = s₂ y) := by
  induction w with
  | nil => rfl
  | cons hadj p ih => exact (agree_adj Gp hcut hadj).trans ih

omit [DecidableEq V] in



theorem eq_or_flip_of_cutEdges_eq (hG : Gp.Preconnected) {s₁ s₂ : ConfigSpace V}
    (hcut : cutEdges Gp s₁ = cutEdges Gp s₂) :
    s₂ = s₁ ∨ s₂ = (fun v => ! s₁ v) := by
  classical
  by_cases hempty : IsEmpty V
  · left; funext v; exact (hempty.elim v)
  rw [not_isEmpty_iff] at hempty
  obtain ⟨v₀⟩ := hempty
  by_cases h0 : s₁ v₀ = s₂ v₀
  · left; funext v
    exact ((agree_walk Gp hcut (hG v₀ v).some).mp h0).symm
  · right; funext v
    have hagree := agree_walk Gp hcut (hG v₀ v).some
    have hne : ¬ (s₁ v = s₂ v) := fun h => h0 (hagree.mpr h)
    cases hb1 : s₁ v <;> cases hb2 : s₂ v <;> simp_all




theorem fiber_card_eq_two [Nonempty V] (hG : Gp.Preconnected)
    {δ : Finset (Sym2 V)} {s : ConfigSpace V} (hs : cutEdges Gp s = δ) :
    (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = δ)).card = 2 := by
  classical
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  have hfilter : (Finset.univ.filter (fun s' : ConfigSpace V => cutEdges Gp s' = δ))
      = {s, fun v => ! s v} := by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hs'
      have hcut : cutEdges Gp s = cutEdges Gp s' := by rw [hs, hs']
      exact eq_or_flip_of_cutEdges_eq Gp hG hcut
    · rintro (rfl | rfl)
      · exact hs
      · rw [cutEdges_flip]; exact hs
  rw [hfilter, Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  intro hcontra
  have hv := congrFun hcontra v₀
  cases h : s v₀ <;> rw [h] at hv <;> simp at hv

end Fiber










section Histogram

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]






theorem cutSpace_gen_eq_evenSubgraph_gen (t : ℝ)
    (hhist : Multiset.map (fun S => S.card) (cutSpace Gp).val
        = Multiset.map (fun S => S.card) (evenSubgraphs Gd).val) :
    (∑ δ ∈ cutSpace Gp, t ^ δ.card)
      = ∑ F ∈ evenSubgraphs Gd, t ^ F.card := by
  rw [Finset.sum, Finset.sum]
  have h2 : Multiset.map (fun S : Finset (Sym2 V) => t ^ S.card) (cutSpace Gp).val
      = Multiset.map (fun S : Finset (Sym2 V) => t ^ S.card) (evenSubgraphs Gd).val := by
    have hcomp : (fun S : Finset (Sym2 V) => t ^ S.card)
        = (fun n : ℕ => t ^ n) ∘ (fun S => S.card) := rfl
    rw [hcomp, ← Multiset.map_map, ← Multiset.map_map, hhist]
  rw [h2]






theorem cutEvenSubgraphMatching_of_hist [Nonempty V] (hG : Gp.Preconnected) (t : ℝ)
    (hhist : Multiset.map (fun S => S.card) (cutSpace Gp).val
        = Multiset.map (fun S => S.card) (evenSubgraphs Gd).val) :
    CutEvenSubgraphMatching Gp Gd t 2 := by
  unfold CutEvenSubgraphMatching
  rw [cut_gen_eq_mult Gp t 2 (fun δ hδ => by
    rw [cutSpace, Finset.mem_image] at hδ
    obtain ⟨s, _, hs⟩ := hδ
    exact_mod_cast fiber_card_eq_two Gp hG hs)]
  rw [cutSpace_gen_eq_evenSubgraph_gen Gp Gd t hhist]
  rfl

end Histogram








section Computable

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



def edgeDiff (s : ConfigSpace V) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun x y => s x != s y, fun _ _ => by simp [bne_comm]⟩ e



def cutEdgesB (s : ConfigSpace V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => edgeDiff s e)

omit [DecidableEq V] in

theorem cutEdges_eq_cutEdgesB (s : ConfigSpace V) :
    cutEdges G s = cutEdgesB G s := by
  unfold cutEdges cutEdgesB
  apply Finset.filter_congr
  intro e _
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk]; unfold spin edgeDiff
    simp only [Sym2.lift_mk]
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy] <;> norm_num


def cutSpaceB : Finset (Finset (Sym2 V)) :=
  Finset.univ.image (fun s : ConfigSpace V => cutEdgesB G s)



def evenSubgraphsB : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter IsEvenSubgraph


theorem cutSpace_eq_cutSpaceB : cutSpace G = cutSpaceB G := by
  unfold cutSpace cutSpaceB
  apply Finset.image_congr
  intro s _
  simp only []
  rw [cutEdges_eq_cutEdgesB]

end Computable









section K4



abbrev K4 : SimpleGraph (Fin 4) := ⊤

instance : DecidableRel (K4).Adj := by unfold K4; infer_instance


theorem K4_preconnected : (K4).Preconnected := by
  intro x y
  by_cases h : x = y
  · subst h; exact SimpleGraph.Reachable.refl x
  · exact SimpleGraph.Adj.reachable (by simp [K4, h])

set_option maxHeartbeats 2000000 in







theorem k4_cutSpace_evenSubgraph_hist :
    Multiset.map (fun S => S.card) (cutSpaceB (K4)).val
      = Multiset.map (fun S => S.card) (evenSubgraphsB (K4)).val := by
  decide










theorem k4_cutEvenSubgraphMatching (t : ℝ) :
    CutEvenSubgraphMatching (K4) (K4) t 2 := by
  apply cutEvenSubgraphMatching_of_hist (K4) (K4) K4_preconnected t
  rw [cutSpace_eq_cutSpaceB]
  have heq : evenSubgraphs (K4) = evenSubgraphsB (K4) := rfl
  rw [heq]
  exact k4_cutSpace_evenSubgraph_hist











theorem isingZ_self_dual_K4 (β βstar : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    isingZ (K4) βstar 0
      = ((2 : ℝ) ^ Fintype.card (Fin 4) * (Real.cosh βstar) ^ (K4).edgeFinset.card
        / (Real.exp (β * (K4).edgeFinset.card) * 2)) * isingZ (K4) β 0 :=
  isingZ_self_dual_of_cutMatching (K4) (K4) β βstar 2 (by norm_num) htemp
    (k4_cutEvenSubgraphMatching (Real.exp (-2 * β)))

end K4

end Ising

end StatMech
