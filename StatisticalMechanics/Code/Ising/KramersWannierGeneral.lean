/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Ising.KramersWannierDuality

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech

namespace Ising









section Handshake

variable {V : Type*} (Gp : SimpleGraph V) (s : ConfigSpace V)




def walkDis : {x y : V} → Gp.Walk x y → ℕ
  | _, _, .nil => 0
  | _, _, .cons (u := u) (v := v) _ p => (if s u ≠ s v then 1 else 0) + walkDis p




theorem walkDis_parity {x y : V} (p : Gp.Walk x y) :
    walkDis Gp s p % 2 = (if s x ≠ s y then 1 else 0) := by
  induction p with
  | nil => simp [walkDis]
  | @cons u v w h q ih =>
    simp only [walkDis]
    rw [Nat.add_mod, ih]
    cases hu : s u <;> cases hv : s v <;> cases hw : s w <;> simp_all






theorem walkDis_closed_even {x : V} (p : Gp.Walk x x) :
    walkDis Gp s p % 2 = 0 := by
  rw [walkDis_parity]; simp




theorem walkDis_eq_darts_sum {x y : V} (p : Gp.Walk x y) :
    walkDis Gp s p
      = (p.darts.map (fun d => if s d.fst ≠ s d.snd then 1 else 0)).sum := by
  induction p with
  | nil => simp [walkDis]
  | @cons u v w h q ih =>
    simp only [walkDis, SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons, ih]

end Handshake










section EdgeCrossing

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]
















structure EdgeCrossing where
  
  ψ : Sym2 V ≃ Sym2 V
  
  edge_mem : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset
  
  cut_to_even : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ)
  

  even_to_cut : ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp

variable {Gp Gd}


theorem cutSpace_subset_edgeFinset {δ : Finset (Sym2 V)} (hδ : δ ∈ cutSpace Gp) :
    δ ⊆ Gp.edgeFinset := by
  rw [cutSpace, Finset.mem_image] at hδ
  obtain ⟨s, _, rfl⟩ := hδ
  unfold cutEdges
  exact Finset.filter_subset _ _




theorem EdgeCrossing.image_mem_even (Φ : EdgeCrossing Gp Gd)
    {δ : Finset (Sym2 V)} (hδ : δ ∈ cutSpace Gp) :
    δ.image Φ.ψ ∈ evenSubgraphs Gd := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, Φ.cut_to_even δ hδ⟩
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact Φ.edge_mem a (cutSpace_subset_edgeFinset hδ ha)



theorem EdgeCrossing.invImage_image (Φ : EdgeCrossing Gp Gd)
    (δ : Finset (Sym2 V)) :
    (δ.image Φ.ψ).image Φ.ψ.symm = δ := by
  rw [Finset.image_image]
  have : (Φ.ψ.symm ∘ Φ.ψ) = id := by funext e; simp
  rw [this, Finset.image_id]



theorem EdgeCrossing.image_invImage (Φ : EdgeCrossing Gp Gd)
    (F : Finset (Sym2 V)) :
    (F.image Φ.ψ.symm).image Φ.ψ = F := by
  rw [Finset.image_image]
  have : (Φ.ψ ∘ Φ.ψ.symm) = id := by funext e; simp
  rw [this, Finset.image_id]


theorem EdgeCrossing.card_image (Φ : EdgeCrossing Gp Gd) (δ : Finset (Sym2 V)) :
    (δ.image Φ.ψ).card = δ.card :=
  Finset.card_image_of_injective δ Φ.ψ.injective












theorem EdgeCrossing.hist_eq (Φ : EdgeCrossing Gp Gd) :
    Multiset.map (fun S => S.card) (cutSpace Gp).val
      = Multiset.map (fun S => S.card) (evenSubgraphs Gd).val := by
  
  have himg : evenSubgraphs Gd = (cutSpace Gp).image (fun δ => δ.image Φ.ψ) := by
    ext F
    simp only [Finset.mem_image]
    constructor
    · intro hF
      exact ⟨F.image Φ.ψ.symm, Φ.even_to_cut F hF, Φ.image_invImage F⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact Φ.image_mem_even hδ
  rw [himg]
  
  have hinj : Set.InjOn (fun δ : Finset (Sym2 V) => δ.image Φ.ψ)
      (cutSpace Gp : Set (Finset (Sym2 V))) := by
    intro a _ b _ h
    have := congrArg (fun F => F.image Φ.ψ.symm) h
    simpa only [Φ.invImage_image] using this
  rw [Finset.image_val_of_injOn hinj, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  simp only [Function.comp_apply]
  exact (Φ.card_image a).symm











theorem cutMatching_of_edgeCrossing [Nonempty V] (hG : Gp.Preconnected)
    (Φ : EdgeCrossing Gp Gd) (t : ℝ) :
    CutEvenSubgraphMatching Gp Gd t 2 :=
  cutEvenSubgraphMatching_of_hist Gp Gd hG t Φ.hist_eq












theorem isingZ_self_dual_of_edgeCrossing [Nonempty V] (hG : Gp.Preconnected)
    (Φ : EdgeCrossing Gp Gd) (β βstar : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    isingZ Gd βstar 0
      = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        / (Real.exp (β * Gp.edgeFinset.card) * 2)) * isingZ Gp β 0 :=
  isingZ_self_dual_of_cutMatching Gp Gd β βstar 2 (by norm_num) htemp
    (cutMatching_of_edgeCrossing hG Φ (Real.exp (-2 * β)))











omit [Fintype V] in




theorem incCount_image_eq_filter (ψ : Sym2 V ≃ Sym2 V) (δ : Finset (Sym2 V)) (w : V) :
    incCount (δ.image ψ) w = (δ.filter (fun e => w ∈ ψ e)).card := by
  unfold incCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ ψ.injective]













theorem cut_to_even_of_faceWalk (ψ : Sym2 V ≃ Sym2 V)
    {basePt : V → V} (faceWalk : (w : V) → Gp.Walk (basePt w) (basePt w))
    (hbridge : ∀ (s : ConfigSpace V) (w : V),
      incCount ((cutEdges Gp s).image ψ) w = walkDis Gp s (faceWalk w)) :
    ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ) := by
  intro δ hδ
  rw [cutSpace, Finset.mem_image] at hδ
  obtain ⟨s, _, rfl⟩ := hδ
  intro w
  rw [Nat.even_iff, hbridge s w]
  exact walkDis_closed_even Gp s (faceWalk w)

end EdgeCrossing












section K4Recovery



def k4Missing (a b : Fin 4) : List (Fin 4) :=
  ([0, 1, 2, 3] : List (Fin 4)).filter (fun k => k ≠ a ∧ k ≠ b)



def k4CompPair (a b : Fin 4) : Sym2 (Fin 4) :=
  match k4Missing a b with
  | [c, d] => s(c, d)
  | _ => s(a, b)



def k4Comp (e : Sym2 (Fin 4)) : Sym2 (Fin 4) :=
  Sym2.lift ⟨k4CompPair, by decide⟩ e



theorem k4Comp_involutive (e : Sym2 (Fin 4)) : k4Comp (k4Comp e) = e := by
  revert e; decide


def k4CompEquiv : Sym2 (Fin 4) ≃ Sym2 (Fin 4) :=
  Function.Involutive.toPerm k4Comp k4Comp_involutive

@[simp] theorem k4CompEquiv_apply (e : Sym2 (Fin 4)) : k4CompEquiv e = k4Comp e := rfl
@[simp] theorem k4CompEquiv_symm_apply (e : Sym2 (Fin 4)) : k4CompEquiv.symm e = k4Comp e := rfl


theorem mem_K4_edgeFinset_iff (e : Sym2 (Fin 4)) :
    e ∈ (K4).edgeFinset ↔ ¬ e.IsDiag := by
  rw [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.ind with
  | _ x y => rw [SimpleGraph.mem_edgeSet]; simp [K4, SimpleGraph.top_adj, Sym2.mk_isDiag_iff]



theorem k4Comp_not_diag (e : Sym2 (Fin 4)) (he : ¬ e.IsDiag) : ¬ (k4Comp e).IsDiag := by
  revert e; decide

set_option maxRecDepth 10000 in



theorem k4Comp_cut_to_even :
    ∀ δ ∈ cutSpaceB (K4), IsEvenSubgraph (δ.image k4Comp) := by decide

set_option maxRecDepth 10000 in



theorem k4Comp_even_to_cut :
    ∀ F ∈ evenSubgraphsB (K4), (F.image k4Comp) ∈ cutSpaceB (K4) := by decide





noncomputable def k4EdgeCrossing : EdgeCrossing (K4) (K4) where
  ψ := k4CompEquiv
  edge_mem := by
    intro e he
    rw [mem_K4_edgeFinset_iff] at he ⊢
    rw [k4CompEquiv_apply]
    exact k4Comp_not_diag e he
  cut_to_even := by
    intro δ hδ
    rw [cutSpace_eq_cutSpaceB] at hδ
    have := k4Comp_cut_to_even δ hδ
    simpa only [k4CompEquiv_apply] using this
  even_to_cut := by
    intro F hF
    rw [show evenSubgraphs (K4) = evenSubgraphsB (K4) from rfl] at hF
    rw [cutSpace_eq_cutSpaceB]
    have := k4Comp_even_to_cut F hF
    simpa only [k4CompEquiv_symm_apply] using this






theorem isingZ_self_dual_K4_via_framework (β βstar : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    isingZ (K4) βstar 0
      = ((2 : ℝ) ^ Fintype.card (Fin 4) * (Real.cosh βstar) ^ (K4).edgeFinset.card
        / (Real.exp (β * (K4).edgeFinset.card) * 2)) * isingZ (K4) β 0 :=
  isingZ_self_dual_of_edgeCrossing K4_preconnected k4EdgeCrossing β βstar htemp

end K4Recovery

end Ising

end StatMech
