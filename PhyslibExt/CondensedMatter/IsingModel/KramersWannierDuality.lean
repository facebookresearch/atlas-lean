/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.KramersWannierCutMatching

/-!
# Kramers–Wannier duality for the complete graph on four vertices

Cut spaces and even subgraphs, and the self-duality of the zero-field Ising partition function on
`K₄`.

## i. Overview

The cut space of a graph is the set of edge sets cut by configurations, and the even subgraphs form
the cycle space. For the complete graph `K₄` (the planar tetrahedron, which is self-dual)
complementing edges within the vertex set gives a bijection from cuts to even subgraphs, which
yields `Z_{K₄}(β*) = (2⁴ cosh^{6} β* / (2 e^{6β})) Z_{K₄}(β)` when `tanh β* = e^{-2β}`.

## ii. Key results

- `StatMech.Ising.cutSpace` : the cut space
- `StatMech.Ising.evenSubgraphs` : the even subgraphs
- `StatMech.Ising.K4` : the complete graph on four vertices
- `StatMech.Ising.isingZ_self_dual_K4` : Kramers–Wannier duality on `K₄`

## iii. Table of contents

- A. Cut space and cycle space
- B. Boolean descriptions
- C. The complete graph on four vertices

## iv. References

- H. A. Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys.
  Rev. 60 (1941) 252–262
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

section Spaces

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]

/-! ## A. Cut space and cycle space -/

/-- The cut space: the edge sets `∂s` cut by configurations `s`. -/
noncomputable def cutSpace : Finset (Finset (Sym2 V)) :=
  Finset.univ.image (fun s : ConfigSpace V => cutEdges Gp s)

/-- The even subgraphs of `G`. -/
noncomputable def evenSubgraphs : Finset (Finset (Sym2 V)) :=
  Gd.edgeFinset.powerset.filter IsEvenSubgraph

end Spaces

section Fiber

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp : SimpleGraph V) [DecidableRel Gp.Adj]

lemma cut_gen_eq_fiber_sum (t : ℝ) :
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

lemma cut_gen_eq_mult (t mult : ℝ)
    (hfib : ∀ δ ∈ cutSpace Gp,
      ((Finset.univ.filter (fun s : ConfigSpace V => cutEdges Gp s = δ)).card : ℝ) = mult) :
    (∑ s : ConfigSpace V, t ^ (cutEdges Gp s).card)
      = mult * ∑ δ ∈ cutSpace Gp, t ^ δ.card := by
  rw [cut_gen_eq_fiber_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [hfib δ hδ]

omit [DecidableEq V] in
lemma mem_cutEdges_iff (s : ConfigSpace V) {x y : V} (hadj : Gp.Adj x y) :
    s(x, y) ∈ cutEdges Gp s ↔ s x ≠ s y := by
  unfold cutEdges
  rw [Finset.mem_filter, bond_mk]
  have hin : s(x, y) ∈ Gp.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact hadj
  unfold spin
  by_cases hx : s x <;> by_cases hy : s y <;>
    simp only [hx, hy, hin, true_and, ite_true, ne_eq] <;> norm_num

omit [DecidableEq V] in
lemma agree_adj {s₁ s₂ : ConfigSpace V} (hcut : cutEdges Gp s₁ = cutEdges Gp s₂)
    {x y : V} (hadj : Gp.Adj x y) :
    (s₁ x = s₂ x) ↔ (s₁ y = s₂ y) := by
  have h1 := mem_cutEdges_iff Gp s₁ hadj
  have h2 := mem_cutEdges_iff Gp s₂ hadj
  rw [hcut] at h1
  have hxor : (s₁ x ≠ s₁ y) ↔ (s₂ x ≠ s₂ y) := h1.symm.trans h2
  revert hxor
  cases s₁ x <;> cases s₁ y <;> cases s₂ x <;> cases s₂ y <;> simp

omit [DecidableEq V] in
lemma agree_walk {s₁ s₂ : ConfigSpace V} (hcut : cutEdges Gp s₁ = cutEdges Gp s₂)
    {x y : V} (w : Gp.Walk x y) :
    (s₁ x = s₂ x) ↔ (s₁ y = s₂ y) := by
  induction w with
  | nil => rfl
  | cons hadj p ih => exact (agree_adj Gp hcut hadj).trans ih

omit [DecidableEq V] in
lemma eq_or_flip_of_cutEdges_eq (hG : Gp.Preconnected) {s₁ s₂ : ConfigSpace V}
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

lemma fiber_card_eq_two [Nonempty V] (hG : Gp.Preconnected)
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

lemma cutSpace_gen_eq_evenSubgraph_gen (t : ℝ)
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

lemma cutEvenSubgraphMatching_of_hist [Nonempty V] (hG : Gp.Preconnected) (t : ℝ)
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

/-! ## B. Boolean descriptions -/

/-- Whether the spins of `s` differ at the endpoints of `e`. -/
def edgeDiff (s : ConfigSpace V) (e : Sym2 V) : Bool :=
  Sym2.lift ⟨fun x y => s x != s y, fun _ _ => by simp [bne_comm]⟩ e

/-- The edges cut by `s`, defined through `edgeDiff`. -/
def cutEdgesB (s : ConfigSpace V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => edgeDiff s e)

omit [DecidableEq V] in
lemma cutEdges_eq_cutEdgesB (s : ConfigSpace V) :
    cutEdges G s = cutEdgesB G s := by
  unfold cutEdges cutEdgesB
  apply Finset.filter_congr
  intro e _
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk]; unfold spin edgeDiff
    simp only [Sym2.lift_mk]
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy] <;> norm_num

/-- The cut space, defined through `cutEdgesB`. -/
def cutSpaceB : Finset (Finset (Sym2 V)) :=
  Finset.univ.image (fun s : ConfigSpace V => cutEdgesB G s)

/-- The even subgraphs, defined with a Boolean test. -/
def evenSubgraphsB : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter IsEvenSubgraph

lemma cutSpace_eq_cutSpaceB : cutSpace G = cutSpaceB G := by
  unfold cutSpace cutSpaceB
  apply Finset.image_congr
  intro s _
  simp only []
  rw [cutEdges_eq_cutEdgesB]

end Computable

section K4

/-! ## C. The complete graph on four vertices -/

/-- The complete graph `K₄` on `Fin 4`. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

/-- Adjacency in `K₄` is decidable. -/
instance : DecidableRel (K4).Adj := by unfold K4; infer_instance

lemma K4_preconnected : (K4).Preconnected := by
  intro x y
  by_cases h : x = y
  · subst h; exact SimpleGraph.Reachable.refl x
  · exact SimpleGraph.Adj.reachable (by simp [K4, h])

set_option maxHeartbeats 2000000 in
-- The proof unfolds large finite sums over box configurations; the default budget is too small.
lemma k4_cutSpace_evenSubgraph_hist :
    Multiset.map (fun S => S.card) (cutSpaceB (K4)).val
      = Multiset.map (fun S => S.card) (evenSubgraphsB (K4)).val := by
  decide

lemma k4_cutEvenSubgraphMatching (t : ℝ) :
    CutEvenSubgraphMatching (K4) (K4) t 2 := by
  apply cutEvenSubgraphMatching_of_hist (K4) (K4) K4_preconnected t
  rw [cutSpace_eq_cutSpaceB]
  have heq : evenSubgraphs (K4) = evenSubgraphsB (K4) := rfl
  rw [heq]
  exact k4_cutSpace_evenSubgraph_hist

/-- **Kramers–Wannier duality** on the self-dual graph `K₄`: if `tanh β* = e^{-2β}` then `Z(β*) =
(2⁴ (cosh β*)^{|E|} / (e^{β|E|} · 2)) Z(β)` at zero field.

H. A. Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*,
Phys. Rev. 60 (1941). -/
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
