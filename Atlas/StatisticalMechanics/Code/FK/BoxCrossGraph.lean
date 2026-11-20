/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.FK.InfiniteVolume
import Code.FK.MonoBC
import Code.FK.DomainMarkov
import Code.FK.WiredDominationInner
import Code.Lattice.BoundaryConditions

open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false

namespace StatMech

namespace FK

open StatMech.Lattice


def boxVertIncl (d n : ℕ) (x : boxVerts d n) : boxVerts d (n + 1) :=
  ⟨(x : Site d), box_subset_succ d n x.2⟩

@[simp] theorem boxVertIncl_val (d n : ℕ) (x : boxVerts d n) :
    ((boxVertIncl d n x : boxVerts d (n+1)) : Site d) = (x : Site d) := rfl

theorem boxVertIncl_injective (d n : ℕ) : Function.Injective (boxVertIncl d n) := by
  intro x y h
  apply Subtype.ext
  have := congrArg (Subtype.val) h
  simpa [boxVertIncl] using this




theorem boxGraph_adj_boxVertIncl (d n : ℕ) (x y : boxVerts d n) :
    (boxGraph d (n+1)).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (boxGraph d n).Adj x y := by
  unfold boxGraph
  simp only [SimpleGraph.comap_adj, boxVertIncl_val]





theorem boxGraph_eq_comap (d n : ℕ) :
    boxGraph d n = (boxGraph d (n+1)).comap (boxVertIncl d n) := by
  ext x y
  rw [SimpleGraph.comap_adj, boxGraph_adj_boxVertIncl]



def boxGraphEmb (d n : ℕ) : boxGraph d n ↪g boxGraph d (n+1) :=
  (boxGraph_eq_comap d n) ▸
    SimpleGraph.Embedding.comap ⟨boxVertIncl d n, boxVertIncl_injective d n⟩ (boxGraph d (n+1))







def innerEdge (d n : ℕ) : Sym2 (boxVerts d n) → Sym2 (boxVerts d (n+1)) :=
  Sym2.map (boxVertIncl d n)



theorem innerEdge_injective (d n : ℕ) : Function.Injective (innerEdge d n) :=
  Sym2.map.injective (boxVertIncl_injective d n)





theorem edgeIncl_innerEdge (d n : ℕ) (e : Sym2 (boxVerts d n)) :
    edgeIncl d (n+1) (innerEdge d n e) = edgeIncl d n e := by
  unfold edgeIncl innerEdge
  rw [Sym2.map_map]
  rfl









def IsInnerVert (d n : ℕ) (v : boxVerts d (n+1)) : Prop := (v : Site d) ∈ box d n

noncomputable instance instDecidablePredIsInnerVert (d n : ℕ) :
    DecidablePred (IsInnerVert d n) :=
  fun _ => Classical.dec _


theorem isInnerVert_iff_range (d n : ℕ) (v : boxVerts d (n+1)) :
    IsInnerVert d n v ↔ ∃ x, boxVertIncl d n x = v := by
  constructor
  · intro h
    exact ⟨⟨(v : Site d), h⟩, by apply Subtype.ext; rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.2


theorem isInnerVert_boxVertIncl (d n : ℕ) (x : boxVerts d n) :
    IsInnerVert d n (boxVertIncl d n x) := x.2





noncomputable def crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    ConfigSpace (Sym2 (boxVerts d (n+1))) :=
  fun e => if h : e ∈ Set.range (innerEdge d n) then ω h.choose else false


theorem crossExt_innerEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (e : Sym2 (boxVerts d n)) : crossExt d n ω (innerEdge d n e) = ω e := by
  unfold crossExt
  have hmem : innerEdge d n e ∈ Set.range (innerEdge d n) := ⟨e, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact innerEdge_injective d n hmem.choose_spec







def innerBdry (d n : ℕ) (v : boxVerts d (n+1)) : Prop :=
  IsInnerVert d n v ∧ (v : Site d) ∈ vertexBoundary d n

noncomputable instance instDecidablePredInnerBdry (d n : ℕ) :
    DecidablePred (innerBdry d n) :=
  fun _ => Classical.dec _


theorem innerBdry_boxVertIncl (d n : ℕ) (x : boxVerts d n) :
    innerBdry d n (boxVertIncl d n x) ↔ boxBoundary d n x := by
  unfold innerBdry boxBoundary
  simp only [boxVertIncl_val, isInnerVert_boxVertIncl, true_and]


theorem innerBdry_isInnerVert (d n : ℕ) {v : boxVerts d (n+1)} (h : innerBdry d n v) :
    IsInnerVert d n v := h.1





noncomputable def crossWiredGraph (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    SimpleGraph (boxVerts d (n+1)) :=
  wiredGraph (boxGraph d (n+1)) (innerBdry d n) (crossExt d n ω)






theorem crossExt_open_inner (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {u v : boxVerts d (n+1)} (h : crossExt d n ω s(u, v) = true) :
    IsInnerVert d n u ∧ IsInnerVert d n v := by
  unfold crossExt at h
  split at h
  · rename_i hmem
    obtain ⟨e, he⟩ := hmem
    
    refine Sym2.inductionOn e (fun a b hab => ?_) he
    rw [innerEdge, Sym2.map_mk] at hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      exact ⟨isInnerVert_boxVertIncl d n a, isInnerVert_boxVertIncl d n b⟩
    · subst h1; subst h2
      exact ⟨isInnerVert_boxVertIncl d n b, isInnerVert_boxVertIncl d n a⟩
  · exact absurd h (by simp)





theorem crossWiredGraph_not_adj_of_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {v : boxVerts d (n+1)}
    (hv : ¬ IsInnerVert d n v) (w : boxVerts d (n+1)) :
    ¬ (crossWiredGraph d n ω).Adj v w := by
  intro h
  rw [crossWiredGraph, wiredGraph_adj] at h
  rcases h with ⟨_, hopen⟩ | ⟨_, hbdry, _⟩
  · exact hv (crossExt_open_inner d n ω hopen).1
  · exact hv hbdry.1




theorem crossExt_innerEdge_pair (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (x y : boxVerts d n) :
    crossExt d n ω s(boxVertIncl d n x, boxVertIncl d n y) = ω s(x, y) := by
  have h : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  rw [h, crossExt_innerEdge]






theorem crossWiredGraph_adj_boxVertIncl (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (x y : boxVerts d n) :
    (crossWiredGraph d n ω).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Adj x y := by
  rw [crossWiredGraph, wiredGraph_adj, wiredGraph_adj, boxGraph_adj_boxVertIncl,
    crossExt_innerEdge_pair]
  constructor
  · rintro (⟨hadj, hopen⟩ | ⟨hne, hbx, hby⟩)
    · exact Or.inl ⟨hadj, hopen⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · exact fun h => hne (by rw [h])
      · exact (innerBdry_boxVertIncl d n x).mp hbx
      · exact (innerBdry_boxVertIncl d n y).mp hby
  · rintro (⟨hadj, hopen⟩ | ⟨hne, hbx, hby⟩)
    · exact Or.inl ⟨hadj, hopen⟩
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · exact fun h => hne (boxVertIncl_injective d n h)
      · exact (innerBdry_boxVertIncl d n x).mpr hbx
      · exact (innerBdry_boxVertIncl d n y).mpr hby






theorem crossWiredGraph_adj_inner_right (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraph d n ω).Adj u w) :
    IsInnerVert d n w := by
  rw [crossWiredGraph, wiredGraph_adj] at h
  rcases h with ⟨_, hopen⟩ | ⟨_, _, hbw⟩
  · exact (crossExt_open_inner d n ω hopen).2
  · exact hbw.1


theorem crossWiredGraph_reachable_inner (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraph d n ω).Reachable u w) :
    IsInnerVert d n w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hadj ih => exact crossWiredGraph_adj_inner_right d n ω ih hadj





theorem crossWiredGraph_reachable_of_inner (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {x y : boxVerts d n}
    (h : (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x y) :
    (crossWiredGraph d n ω).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
  let f : (wiredGraph (boxGraph d n) (boxBoundary d n) ω) →g (crossWiredGraph d n ω) :=
    { toFun := boxVertIncl d n
      map_rel' := fun {a b} hab => (crossWiredGraph_adj_boxVertIncl d n ω a b).mpr hab }
  exact h.map f






theorem inner_reachable_of_crossWiredGraph (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {x y : boxVerts d n}
    (h : (crossWiredGraph d n ω).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  
  
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (crossWiredGraph d n ω).Adj (boxVertIncl d n x) w →
        ∀ (hw : IsInnerVert d n w),
          (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x ⟨(w : Site d), hw⟩ by
    have hyinner : IsInnerVert d n (boxVertIncl d n y) := isInnerVert_boxVertIncl d n y
    have := H (boxVertIncl d n y) h hyinner
    
    convert this using 2
  intro w hw hwinner
  induction hw with
  | refl =>
      have : (⟨(boxVertIncl d n x : Site d), hwinner⟩ : boxVerts d n) = x := by
        apply Subtype.ext; rfl
      rw [this]
  | @tail u w hux hadj ih =>
      have huinner : IsInnerVert d n u :=
        crossWiredGraph_reachable_inner d n ω (isInnerVert_boxVertIncl d n x)
          (SimpleGraph.reachable_iff_reflTransGen .. |>.mpr hux)
      have ihu := ih huinner
      
      have hue : u = boxVertIncl d n ⟨(u : Site d), huinner⟩ := by apply Subtype.ext; rfl
      have hwe : w = boxVertIncl d n ⟨(w : Site d), hwinner⟩ := by apply Subtype.ext; rfl
      have hadj' : (crossWiredGraph d n ω).Adj
          (boxVertIncl d n ⟨(u : Site d), huinner⟩)
          (boxVertIncl d n ⟨(w : Site d), hwinner⟩) := by rw [← hue, ← hwe]; exact hadj
      have hstep := (crossWiredGraph_adj_boxVertIncl d n ω
        ⟨(u : Site d), huinner⟩ ⟨(w : Site d), hwinner⟩).mp hadj'
      exact ihu.trans hstep.reachable










noncomputable abbrev innerWiredGraph (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    SimpleGraph (boxVerts d n) :=
  wiredGraph (boxGraph d n) (boxBoundary d n) ω


def innerWiredHom (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    (innerWiredGraph d n ω) →g (crossWiredGraph d n ω) where
  toFun := boxVertIncl d n
  map_rel' := fun {a b} hab => (crossWiredGraph_adj_boxVertIncl d n ω a b).mpr hab





noncomputable def crossComponentEquivFun (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    (innerWiredGraph d n ω).ConnectedComponent ⊕
      {v : boxVerts d (n+1) // ¬ IsInnerVert d n v} →
      (crossWiredGraph d n ω).ConnectedComponent
  | Sum.inl c => c.map (innerWiredHom d n ω)
  | Sum.inr v => (crossWiredGraph d n ω).connectedComponentMk v.1


theorem crossComponentEquivFun_inl_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (x : boxVerts d n) :
    crossComponentEquivFun d n ω (Sum.inl ((innerWiredGraph d n ω).connectedComponentMk x))
      = (crossWiredGraph d n ω).connectedComponentMk (boxVertIncl d n x) := rfl



theorem crossWiredGraph_reachable_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {v w : boxVerts d (n+1)}
    (hv : ¬ IsInnerVert d n v) (h : (crossWiredGraph d n ω).Reachable v w) : w = v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail u w hvu hadj ih =>
      exact absurd hadj (by rw [ih]; exact crossWiredGraph_not_adj_of_annulus d n ω hv w)


theorem crossComponentEquivFun_injective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    Function.Injective (crossComponentEquivFun d n ω) := by
  rintro (c₁ | v₁) (c₂ | v₂) h
  · 
    induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivFun_inl_mk, crossComponentEquivFun_inl_mk,
      ConnectedComponent.eq] at h
    have hreach := inner_reachable_of_crossWiredGraph d n ω h
    exact congrArg Sum.inl (ConnectedComponent.eq.mpr hreach)
  · 
    induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    rw [crossComponentEquivFun_inl_mk] at h
    have h' : (crossWiredGraph d n ω).Reachable (boxVertIncl d n x₁) v₂.1 :=
      ConnectedComponent.eq.mp h
    exact absurd
      (crossWiredGraph_reachable_inner d n ω (isInnerVert_boxVertIncl d n x₁) h') v₂.2
  · 
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivFun_inl_mk] at h
    have h' : (crossWiredGraph d n ω).Reachable (boxVertIncl d n x₂) v₁.1 :=
      ConnectedComponent.eq.mp h.symm
    exact absurd
      (crossWiredGraph_reachable_inner d n ω (isInnerVert_boxVertIncl d n x₂) h') v₁.2
  · 
    have h' : (crossWiredGraph d n ω).Reachable v₁.1 v₂.1 := ConnectedComponent.eq.mp h
    exact congrArg Sum.inr
      (Subtype.ext (crossWiredGraph_reachable_annulus d n ω v₁.2 h').symm)


theorem crossComponentEquivFun_surjective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    Function.Surjective (crossComponentEquivFun d n ω) := by
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : IsInnerVert d n u
  · 
    refine ⟨Sum.inl ((innerWiredGraph d n ω).connectedComponentMk ⟨(u : Site d), hu⟩), ?_⟩
    rw [crossComponentEquivFun_inl_mk]
    apply ConnectedComponent.sound
    have : boxVertIncl d n ⟨(u : Site d), hu⟩ = u := by apply Subtype.ext; rfl
    rw [this]
  · 
    exact ⟨Sum.inr ⟨u, hu⟩, rfl⟩




noncomputable def crossComponentEquiv (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    (innerWiredGraph d n ω).ConnectedComponent ⊕
      {v : boxVerts d (n+1) // ¬ IsInnerVert d n v} ≃
      (crossWiredGraph d n ω).ConnectedComponent :=
  Equiv.ofBijective (crossComponentEquivFun d n ω)
    ⟨crossComponentEquivFun_injective d n ω, crossComponentEquivFun_surjective d n ω⟩


noncomputable def annulusCard (d n : ℕ) : ℕ :=
  Nat.card {v : boxVerts d (n+1) // ¬ IsInnerVert d n v}













theorem numClustersWired_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    StatMech.Lattice.numClustersWired (boxGraph d (n+1)) (innerBdry d n) (crossExt d n ω)
      = StatMech.Lattice.numClustersWired (boxGraph d n) (boxBoundary d n) ω
        + annulusCard d n := by
  
  
  
  show Nat.card (crossWiredGraph d n ω).ConnectedComponent
      = Nat.card (innerWiredGraph d n ω).ConnectedComponent + annulusCard d n
  rw [annulusCard, ← Nat.card_sum, Nat.card_congr (crossComponentEquiv d n ω).symm]











theorem innerEdge_mem_edgeSet_iff (d n : ℕ) (e : Sym2 (boxVerts d n)) :
    innerEdge d n e ∈ (boxGraph d (n+1)).edgeSet ↔ e ∈ (boxGraph d n).edgeSet := by
  refine Sym2.inductionOn e (fun a b => ?_)
  rw [innerEdge, Sym2.map_mk, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet,
    boxGraph_adj_boxVertIncl]



theorem innerEdge_image_edgeFinset (d n : ℕ) :
    (boxGraph d n).edgeFinset.image (innerEdge d n)
      = (boxGraph d (n+1)).edgeFinset.filter (· ∈ Set.range (innerEdge d n)) := by
  ext e
  simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_edgeFinset, Set.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(innerEdge_mem_edgeSet_iff d n a).mpr ha, a, rfl⟩
  · rintro ⟨hmem, a, rfl⟩
    exact ⟨a, (innerEdge_mem_edgeSet_iff d n a).mp hmem, rfl⟩




noncomputable def nonInnerEdgeCard (d n : ℕ) : ℕ :=
  ((boxGraph d (n+1)).edgeFinset.filter (fun e => e ∉ Set.range (innerEdge d n))).card


theorem crossExt_eq_false_of_not_range (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {e : Sym2 (boxVerts d (n+1))} (he : e ∉ Set.range (innerEdge d n)) :
    crossExt d n ω e = false := by
  unfold crossExt; rw [dif_neg he]






theorem edgeProduct_crossExt (d n : ℕ) {p : ℝ} (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    edgeProduct (boxGraph d (n+1)) p (crossExt d n ω)
      = edgeProduct (boxGraph d n) p ω * (1 - p) ^ nonInnerEdgeCard d n := by
  classical
  unfold edgeProduct nonInnerEdgeCard
  rw [← Finset.prod_filter_mul_prod_filter_not (boxGraph d (n+1)).edgeFinset
    (fun e => e ∈ Set.range (innerEdge d n))]
  congr 1
  · 
    rw [← innerEdge_image_edgeFinset,
      Finset.prod_image (fun a _ b _ h => innerEdge_injective d n h)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [crossExt_innerEdge]
  · 
    rw [Finset.prod_congr rfl (fun e he => ?_), Finset.prod_const]
    rw [Finset.mem_filter] at he
    rw [crossExt_eq_false_of_not_range d n ω he.2]
    rfl







noncomputable def crossShift (d n : ℕ) (p q : ℝ) : ℝ :=
  (1 - p) ^ nonInnerEdgeCard d n * q ^ annulusCard d n

theorem crossShift_pos {d n : ℕ} {p q : ℝ} (hp1 : p < 1) (hq : 0 < q) :
    0 < crossShift d n p q :=
  mul_pos (pow_pos (by linarith) _) (pow_pos hq _)









theorem bcWeight_crossExt (d n : ℕ) {p q : ℝ} (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    bcWeight (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q
        (crossExt d n ω)
      = wiredFkWeight (boxGraph d n) (boxBoundary d n) p q ω * crossShift d n p q := by
  rw [bcWeight, numClustersBC_boundaryClique, numClustersWired_crossExt,
    edgeProduct_crossExt, wiredFkWeight, crossShift, pow_add]
  ring













noncomputable def innerEdgeFinset (d n : ℕ) : Finset (Sym2 (boxVerts d (n+1))) :=
  Finset.univ.image (innerEdge d n)

theorem mem_innerEdgeFinset (d n : ℕ) (e : Sym2 (boxVerts d (n+1))) :
    e ∈ innerEdgeFinset d n ↔ e ∈ Set.range (innerEdge d n) := by
  simp only [innerEdgeFinset, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]



noncomputable def innerRestrict (d n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    ConfigSpace (Sym2 (boxVerts d n)) :=
  fun e => ρ (innerEdge d n e)

@[simp] theorem innerRestrict_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    innerRestrict d n (crossExt d n ω) = ω := by
  funext e; rw [innerRestrict, crossExt_innerEdge]



theorem crossExt_innerRestrict_of_agreesOff (d n : ℕ)
    {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
    (hρ : AgreesOff (innerEdgeFinset d n) (fun _ => false) ρ) :
    crossExt d n (innerRestrict d n ρ) = ρ := by
  funext e
  unfold crossExt
  split
  · rename_i hmem
    show innerRestrict d n ρ hmem.choose = ρ e
    rw [innerRestrict, hmem.choose_spec]
  · rename_i hmem
    have : e ∉ innerEdgeFinset d n := by rw [mem_innerEdgeFinset]; exact hmem
    exact (hρ e this).symm


theorem agreesOff_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    AgreesOff (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω) := by
  intro e he
  rw [mem_innerEdgeFinset] at he
  exact crossExt_eq_false_of_not_range d n ω he




noncomputable def innerFibreEquiv (d n : ℕ) :
    {ρ : ConfigSpace (Sym2 (boxVerts d (n+1))) //
        AgreesOff (innerEdgeFinset d n) (fun _ => false) ρ} ≃
      ConfigSpace (Sym2 (boxVerts d n)) where
  toFun ρ := innerRestrict d n ρ.1
  invFun ω := ⟨crossExt d n ω, agreesOff_crossExt d n ω⟩
  left_inv ρ := by
    apply Subtype.ext
    exact crossExt_innerRestrict_of_agreesOff d n ρ.2
  right_inv ω := innerRestrict_crossExt d n ω




theorem condFibre_eq_image_crossExt (d n : ℕ) :
    condFibre (innerEdgeFinset d n) (fun _ => false)
      = Finset.univ.image (crossExt d n) := by
  ext ρ
  rw [mem_condFibre, Finset.mem_image]
  constructor
  · intro hρ
    exact ⟨innerRestrict d n ρ, Finset.mem_univ _, crossExt_innerRestrict_of_agreesOff d n hρ⟩
  · rintro ⟨ω, _, rfl⟩
    exact agreesOff_crossExt d n ω




theorem inducedBcZ_innerEdgeFinset (d n : ℕ) {p q : ℝ} :
    inducedBcZ (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q
        (innerEdgeFinset d n) (fun _ => false)
      = wiredFkZ (boxGraph d n) (boxBoundary d n) p q * crossShift d n p q := by
  rw [inducedBcZ, condFibre_eq_image_crossExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_crossExt, innerRestrict_crossExt] at this),
    wiredFkZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => bcWeight_crossExt d n ω)
















theorem condBcProb_crossExt_eq_wiredFkProb (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    condBcProb (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q
        (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω)
      = wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  rw [condBcProb, if_pos (agreesOff_crossExt d n ω), bcWeight_crossExt,
    inducedBcZ_innerEdgeFinset, wiredFkProb]
  rw [mul_div_mul_right _ _ (crossShift_pos hp1 hq).ne']










theorem boxBoundary_succ_iff_not_inner (d n : ℕ) (v : boxVerts d (n+1)) :
    boxBoundary d (n+1) v ↔ ¬ IsInnerVert d n v := by
  unfold boxBoundary IsInnerVert
  rw [StatMech.Lattice.mem_vertexBoundary, Nat.add_sub_cancel]
  constructor
  · rintro ⟨_, hnotin⟩; exact hnotin
  · intro hnotin; exact ⟨v.2, hnotin⟩











def IsAnnulusWiring (d n : ℕ) (D : SimpleGraph (boxVerts d (n+1))) : Prop :=
  ∀ ⦃u v⦄, D.Adj u v → ¬ IsInnerVert d n u



theorem isAnnulusWiring_boxBoundary_succ (d n : ℕ) :
    IsAnnulusWiring d n
      (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) := by
  intro u v hadj
  rw [StatMech.Lattice.boundaryCliqueGraph_adj] at hadj
  exact (boxBoundary_succ_iff_not_inner d n u).mp hadj.2.1


noncomputable def crossWiredGraphAdd (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (D : SimpleGraph (boxVerts d (n+1))) : SimpleGraph (boxVerts d (n+1)) :=
  crossWiredGraph d n ω ⊔ D



theorem openSub_sup_eq_crossWiredGraphAdd (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (D : SimpleGraph (boxVerts d (n+1))) :
    openSub (boxGraph d (n+1)) (crossExt d n ω)
        ⊔ (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D)
      = crossWiredGraphAdd d n ω D := by
  rw [crossWiredGraphAdd, crossWiredGraph, StatMech.Lattice.wiredGraph,
    StatMech.FK.openSub_eq_openGraph, ← sup_assoc]





theorem crossWiredGraphAdd_adj_inner_right (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraphAdd d n ω D).Adj u w) :
    IsInnerVert d n w := by
  rw [crossWiredGraphAdd, SimpleGraph.sup_adj] at h
  rcases h with hcross | hd
  · exact crossWiredGraph_adj_inner_right d n ω hu hcross
  · exact absurd hu (hD hd)



theorem crossWiredGraphAdd_not_adj_inner_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (hw : ¬ IsInnerVert d n w) :
    ¬ (crossWiredGraphAdd d n ω D).Adj u w :=
  fun h => hw (crossWiredGraphAdd_adj_inner_right d n ω hD hu h)


theorem crossWiredGraphAdd_reachable_inner (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraphAdd d n ω D).Reachable u w) :
    IsInnerVert d n w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hadj ih => exact crossWiredGraphAdd_adj_inner_right d n ω hD ih hadj


theorem crossWiredGraphAdd_reachable_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : ¬ IsInnerVert d n u) (h : (crossWiredGraphAdd d n ω D).Reachable u w) :
    ¬ IsInnerVert d n w := by
  intro hw
  exact hu (crossWiredGraphAdd_reachable_inner d n ω hD hw h.symm)


abbrev AnnulusVert (d n : ℕ) : Type := {v : boxVerts d (n+1) // ¬ IsInnerVert d n v}




noncomputable def annulusSubgraph (d n : ℕ) (D : SimpleGraph (boxVerts d (n+1))) :
    SimpleGraph (AnnulusVert d n) :=
  SimpleGraph.comap (Subtype.val) D

noncomputable instance instDecidableRelAnnulusSubgraph (d n : ℕ)
    (D : SimpleGraph (boxVerts d (n+1))) : DecidableRel (annulusSubgraph d n D).Adj :=
  Classical.decRel _




theorem crossWiredGraphAdd_adj_boxVertIncl (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) (x y : boxVerts d n) :
    (crossWiredGraphAdd d n ω D).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (innerWiredGraph d n ω).Adj x y := by
  rw [crossWiredGraphAdd, SimpleGraph.sup_adj]
  constructor
  · rintro (hcross | hd)
    · exact (crossWiredGraph_adj_boxVertIncl d n ω x y).mp hcross
    · exact absurd (isInnerVert_boxVertIncl d n x) (hD hd)
  · intro h
    exact Or.inl ((crossWiredGraph_adj_boxVertIncl d n ω x y).mpr h)




theorem crossWiredGraphAdd_adj_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (D : SimpleGraph (boxVerts d (n+1)))
    (a b : AnnulusVert d n) :
    (crossWiredGraphAdd d n ω D).Adj a.1 b.1 ↔ (annulusSubgraph d n D).Adj a b := by
  rw [crossWiredGraphAdd, SimpleGraph.sup_adj, annulusSubgraph, SimpleGraph.comap_adj]
  constructor
  · rintro (hcross | hd)
    · exact absurd hcross (crossWiredGraph_not_adj_of_annulus d n ω a.2 b.1)
    · exact hd
  · intro h; exact Or.inr h




theorem inner_reachable_of_crossWiredGraphAdd (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {x y : boxVerts d n}
    (h : (crossWiredGraphAdd d n ω D).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerWiredGraph d n ω).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (crossWiredGraphAdd d n ω D).Adj (boxVertIncl d n x) w →
        ∀ (hw : IsInnerVert d n w),
          (innerWiredGraph d n ω).Reachable x ⟨(w : Site d), hw⟩ by
    have := H (boxVertIncl d n y) h (isInnerVert_boxVertIncl d n y)
    convert this using 2
  intro w hw hwinner
  induction hw with
  | refl =>
      have : (⟨(boxVertIncl d n x : Site d), hwinner⟩ : boxVerts d n) = x := by
        apply Subtype.ext; rfl
      rw [this]
  | @tail u w hux hadj ih =>
      have huinner : IsInnerVert d n u :=
        crossWiredGraphAdd_reachable_inner d n ω hD (isInnerVert_boxVertIncl d n x)
          (SimpleGraph.reachable_iff_reflTransGen .. |>.mpr hux)
      have ihu := ih huinner
      have hue : u = boxVertIncl d n ⟨(u : Site d), huinner⟩ := by apply Subtype.ext; rfl
      have hwe : w = boxVertIncl d n ⟨(w : Site d), hwinner⟩ := by apply Subtype.ext; rfl
      have hadj' : (crossWiredGraphAdd d n ω D).Adj
          (boxVertIncl d n ⟨(u : Site d), huinner⟩)
          (boxVertIncl d n ⟨(w : Site d), hwinner⟩) := by rw [← hue, ← hwe]; exact hadj
      have hstep := (crossWiredGraphAdd_adj_boxVertIncl d n ω hD
        ⟨(u : Site d), huinner⟩ ⟨(w : Site d), hwinner⟩).mp hadj'
      exact ihu.trans hstep.reachable



theorem annulus_reachable_of_crossWiredGraphAdd (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {a b : AnnulusVert d n}
    (h : (crossWiredGraphAdd d n ω D).Reachable a.1 b.1) :
    (annulusSubgraph d n D).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (crossWiredGraphAdd d n ω D).Adj a.1 w →
        ∀ (hw : ¬ IsInnerVert d n w),
          (annulusSubgraph d n D).Reachable a ⟨w, hw⟩ by
    have hb := H b.1 h b.2
    have : (⟨b.1, b.2⟩ : AnnulusVert d n) = b := Subtype.ext rfl
    rwa [this] at hb
  intro w hw hwannulus
  induction hw with
  | refl =>
      have : (⟨a.1, hwannulus⟩ : AnnulusVert d n) = a := Subtype.ext rfl
      rw [this]
  | @tail u w hau hadj ih =>
      have huannulus : ¬ IsInnerVert d n u :=
        crossWiredGraphAdd_reachable_annulus d n ω hD a.2
          (SimpleGraph.reachable_iff_reflTransGen .. |>.mpr hau)
      have ihu := ih huannulus
      have hstep := (crossWiredGraphAdd_adj_annulus d n ω D
        ⟨u, huannulus⟩ ⟨w, hwannulus⟩).mp hadj
      exact ihu.trans hstep.reachable


def innerWiredHomAdd (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} (hD : IsAnnulusWiring d n D) :
    (innerWiredGraph d n ω) →g (crossWiredGraphAdd d n ω D) where
  toFun := boxVertIncl d n
  map_rel' := fun {a b} hab => (crossWiredGraphAdd_adj_boxVertIncl d n ω hD a b).mpr hab


def annulusHomAdd (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (D : SimpleGraph (boxVerts d (n+1))) :
    (annulusSubgraph d n D) →g (crossWiredGraphAdd d n ω D) where
  toFun := Subtype.val
  map_rel' := fun {a b} hab => (crossWiredGraphAdd_adj_annulus d n ω D a b).mpr hab


noncomputable def crossComponentEquivAddFun (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) :
    (innerWiredGraph d n ω).ConnectedComponent ⊕
      (annulusSubgraph d n D).ConnectedComponent →
      (crossWiredGraphAdd d n ω D).ConnectedComponent
  | Sum.inl c => c.map (innerWiredHomAdd d n ω hD)
  | Sum.inr a => a.map (annulusHomAdd d n ω D)

theorem crossComponentEquivAddFun_inl_mk (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) (x : boxVerts d n) :
    crossComponentEquivAddFun d n ω hD
        (Sum.inl ((innerWiredGraph d n ω).connectedComponentMk x))
      = (crossWiredGraphAdd d n ω D).connectedComponentMk (boxVertIncl d n x) := rfl

theorem crossComponentEquivAddFun_inr_mk (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) (a : AnnulusVert d n) :
    crossComponentEquivAddFun d n ω hD
        (Sum.inr ((annulusSubgraph d n D).connectedComponentMk a))
      = (crossWiredGraphAdd d n ω D).connectedComponentMk a.1 := rfl


theorem crossComponentEquivAddFun_injective (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) :
    Function.Injective (crossComponentEquivAddFun d n ω hD) := by
  rintro (c₁ | a₁) (c₂ | a₂) h
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivAddFun_inl_mk, crossComponentEquivAddFun_inl_mk,
      ConnectedComponent.eq] at h
    exact congrArg Sum.inl
      (ConnectedComponent.eq.mpr (inner_reachable_of_crossWiredGraphAdd d n ω hD h))
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction a₂ using ConnectedComponent.ind with | _ b₂ =>
    rw [crossComponentEquivAddFun_inl_mk, crossComponentEquivAddFun_inr_mk] at h
    have h' : (crossWiredGraphAdd d n ω D).Reachable (boxVertIncl d n x₁) b₂.1 :=
      ConnectedComponent.eq.mp h
    exact absurd
      (crossWiredGraphAdd_reachable_inner d n ω hD (isInnerVert_boxVertIncl d n x₁) h') b₂.2
  · induction a₁ using ConnectedComponent.ind with | _ b₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivAddFun_inl_mk, crossComponentEquivAddFun_inr_mk] at h
    have h' : (crossWiredGraphAdd d n ω D).Reachable (boxVertIncl d n x₂) b₁.1 :=
      ConnectedComponent.eq.mp h.symm
    exact absurd
      (crossWiredGraphAdd_reachable_inner d n ω hD (isInnerVert_boxVertIncl d n x₂) h') b₁.2
  · induction a₁ using ConnectedComponent.ind with | _ b₁ =>
    induction a₂ using ConnectedComponent.ind with | _ b₂ =>
    rw [crossComponentEquivAddFun_inr_mk, crossComponentEquivAddFun_inr_mk,
      ConnectedComponent.eq] at h
    exact congrArg Sum.inr
      (ConnectedComponent.eq.mpr (annulus_reachable_of_crossWiredGraphAdd d n ω hD h))


theorem crossComponentEquivAddFun_surjective (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) :
    Function.Surjective (crossComponentEquivAddFun d n ω hD) := by
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : IsInnerVert d n u
  · refine ⟨Sum.inl ((innerWiredGraph d n ω).connectedComponentMk ⟨(u : Site d), hu⟩), ?_⟩
    rw [crossComponentEquivAddFun_inl_mk]
    apply ConnectedComponent.sound
    have : boxVertIncl d n ⟨(u : Site d), hu⟩ = u := by apply Subtype.ext; rfl
    rw [this]
  · exact ⟨Sum.inr ((annulusSubgraph d n D).connectedComponentMk ⟨u, hu⟩), rfl⟩



noncomputable def crossComponentEquivAdd (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) :
    (innerWiredGraph d n ω).ConnectedComponent ⊕
      (annulusSubgraph d n D).ConnectedComponent ≃
      (crossWiredGraphAdd d n ω D).ConnectedComponent :=
  Equiv.ofBijective (crossComponentEquivAddFun d n ω hD)
    ⟨crossComponentEquivAddFun_injective d n ω hD,
     crossComponentEquivAddFun_surjective d n ω hD⟩









theorem numClustersBC_crossExt_add (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj]
    (hD : IsAnnulusWiring d n D) :
    numClustersBC (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) (crossExt d n ω)
      = StatMech.Lattice.numClustersWired (boxGraph d n) (boxBoundary d n) ω
        + Nat.card (annulusSubgraph d n D).ConnectedComponent := by
  rw [numClustersBC, openSub_sup_eq_crossWiredGraphAdd, numClustersWired_eq_card]
  show Nat.card (crossWiredGraphAdd d n ω D).ConnectedComponent
      = Fintype.card (innerWiredGraph d n ω).ConnectedComponent
        + Nat.card (annulusSubgraph d n D).ConnectedComponent
  rw [← Nat.card_eq_fintype_card, ← Nat.card_sum,
    Nat.card_congr (crossComponentEquivAdd d n ω hD).symm]



noncomputable def crossShiftAdd (d n : ℕ) (p q : ℝ)
    (D : SimpleGraph (boxVerts d (n+1))) : ℝ :=
  (1 - p) ^ nonInnerEdgeCard d n * q ^ Nat.card (annulusSubgraph d n D).ConnectedComponent

theorem crossShiftAdd_pos {d n : ℕ} {p q : ℝ} (hp1 : p < 1) (hq : 0 < q)
    (D : SimpleGraph (boxVerts d (n+1))) : 0 < crossShiftAdd d n p q D :=
  mul_pos (pow_pos (by linarith) _) (pow_pos hq _)





theorem bcWeight_crossExt_add (d n : ℕ) {p q : ℝ} (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj] (hD : IsAnnulusWiring d n D) :
    bcWeight (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q (crossExt d n ω)
      = wiredFkWeight (boxGraph d n) (boxBoundary d n) p q ω * crossShiftAdd d n p q D := by
  rw [bcWeight, numClustersBC_crossExt_add d n ω hD, edgeProduct_crossExt, wiredFkWeight,
    crossShiftAdd, pow_add]
  ring


theorem inducedBcZ_innerEdgeFinset_add (d n : ℕ) {p q : ℝ}
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj]
    (hD : IsAnnulusWiring d n D) :
    inducedBcZ (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q
        (innerEdgeFinset d n) (fun _ => false)
      = wiredFkZ (boxGraph d n) (boxBoundary d n) p q * crossShiftAdd d n p q D := by
  rw [inducedBcZ, condFibre_eq_image_crossExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_crossExt, innerRestrict_crossExt] at this),
    wiredFkZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => bcWeight_crossExt_add d n ω hD)














theorem condBcProb_crossExt_eq_wiredFkProb_add (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    {D : SimpleGraph (boxVerts d (n+1))} [DecidableRel D.Adj]
    (hD : IsAnnulusWiring d n D) :
    condBcProb (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q
        (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω)
      = wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  rw [condBcProb, if_pos (agreesOff_crossExt d n ω), bcWeight_crossExt_add d n ω hD,
    inducedBcZ_innerEdgeFinset_add d n hD, wiredFkProb,
    mul_div_mul_right _ _ (crossShiftAdd_pos hp1 hq D).ne']

end FK

end StatMech
