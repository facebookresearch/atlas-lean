/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.FK.TranslationInvariance

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace









variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]




noncomputable def reCfgIso (σ : V ≃ W) (ω : ConfigSpace (Sym2 W)) : ConfigSpace (Sym2 V) :=
  fun e => ω (Sym2.map σ e)

theorem fvs_reCfgIso_apply (σ : V ≃ W) (ω : ConfigSpace (Sym2 W)) (e : Sym2 V) :
    reCfgIso σ ω e = ω (Sym2.map σ e) := rfl

theorem fvs_reCfgIso_reCfgIso (σ : V ≃ W) (ω : ConfigSpace (Sym2 W)) :
    reCfgIso σ.symm (reCfgIso σ ω) = ω := by
  funext e; unfold reCfgIso; rw [Sym2.map_map]; simp

theorem fvs_reCfgIso_reCfgIso' (σ : V ≃ W) (ω : ConfigSpace (Sym2 V)) :
    reCfgIso σ (reCfgIso σ.symm ω) = ω := by
  funext e; unfold reCfgIso; rw [Sym2.map_map]; simp



noncomputable def reCfgIsoEquiv (σ : V ≃ W) :
    ConfigSpace (Sym2 W) ≃ ConfigSpace (Sym2 V) where
  toFun := reCfgIso σ
  invFun := reCfgIso σ.symm
  left_inv := fvs_reCfgIso_reCfgIso σ
  right_inv := fvs_reCfgIso_reCfgIso' σ








variable (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]



noncomputable def fvs_openSubIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (ω : ConfigSpace (Sym2 W)) :
    openSub G (reCfgIso σ ω) ≃g openSub H ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [openSub_adj, reCfgIso]
    rw [Sym2.map_mk, hσ x y]


theorem fvs_numClusters_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (ω : ConfigSpace (Sym2 W)) :
    numClusters G (reCfgIso σ ω) = numClusters H ω := by
  unfold numClusters
  exact Fintype.card_congr (fvs_openSubIso G H σ hσ ω).connectedComponentEquiv



omit [DecidableEq V] [DecidableEq W] in

theorem fvs_mem_edgeFinset_map (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    Sym2.map σ e ∈ H.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, ← hσ]
  exact he

omit [DecidableEq V] [DecidableEq W] in

theorem fvs_mem_edgeFinset_map_symm (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    Sym2.map σ.symm e ∈ G.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hσ]
  simpa using he




theorem fvs_edgeProduct_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p : ℝ) (ω : ConfigSpace (Sym2 W)) :
    edgeProduct G p (reCfgIso σ ω) = edgeProduct H p ω := by
  unfold edgeProduct reCfgIso
  symm
  apply Finset.prod_bij' (i := fun e _ => Sym2.map σ.symm e) (j := fun e _ => Sym2.map σ e)
  · intro a ha; exact fvs_mem_edgeFinset_map_symm G H σ hσ ha
  · intro a ha; exact fvs_mem_edgeFinset_map G H σ hσ ha
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rw [Sym2.map_map]; simp




theorem fvs_fkWeight_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    fkWeight G p q (reCfgIso σ ω) = fkWeight H p q ω := by
  unfold fkWeight
  rw [fvs_edgeProduct_reCfgIso G H σ hσ p ω, fvs_numClusters_reCfgIso G H σ hσ ω]



theorem fvs_fkZ_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) :
    fkZ G p q = fkZ H p q := by
  unfold fkZ
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ) (fun ω => fkWeight G p q ω)]
  exact Finset.sum_congr rfl fun ω _ => fvs_fkWeight_reCfgIso G H σ hσ p q ω



theorem fvs_fkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    fkProb G p q (reCfgIso σ ω) = fkProb H p q ω := by
  unfold fkProb
  rw [fvs_fkWeight_reCfgIso G H σ hσ p q ω, fvs_fkZ_reCfgIso G H σ hσ p q]







variable (bdryV : V → Prop) [DecidablePred bdryV] (bdryW : W → Prop) [DecidablePred bdryW]



noncomputable def fvs_wiredGraphIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (ω : ConfigSpace (Sym2 W)) :
    StatMech.Lattice.wiredGraph G bdryV (reCfgIso σ ω)
      ≃g StatMech.Lattice.wiredGraph H bdryW ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [StatMech.Lattice.wiredGraph_adj, reCfgIso]
    rw [Sym2.map_mk, hσ x y, hbdry x, hbdry y]
    constructor
    · rintro (h | ⟨hne, hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun h => hne (by rw [h]), hx, hy⟩
    · rintro (h | ⟨hne, hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun h => hne (σ.injective h), hx, hy⟩


theorem fvs_numClustersWired_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (ω : ConfigSpace (Sym2 W)) :
    StatMech.Lattice.numClustersWired G bdryV (reCfgIso σ ω)
      = StatMech.Lattice.numClustersWired H bdryW ω := by
  unfold StatMech.Lattice.numClustersWired
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (fvs_wiredGraphIso G H bdryV bdryW σ hσ hbdry ω).connectedComponentEquiv


theorem fvs_wiredFkWeight_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    wiredFkWeight G bdryV p q (reCfgIso σ ω) = wiredFkWeight H bdryW p q ω := by
  unfold wiredFkWeight
  rw [fvs_edgeProduct_reCfgIso G H σ hσ p ω,
    fvs_numClustersWired_reCfgIso G H bdryV bdryW σ hσ hbdry ω]


theorem fvs_wiredFkZ_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) :
    wiredFkZ G bdryV p q = wiredFkZ H bdryW p q := by
  unfold wiredFkZ
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ) (fun ω => wiredFkWeight G bdryV p q ω)]
  exact Finset.sum_congr rfl fun ω _ => fvs_wiredFkWeight_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω


theorem fvs_wiredFkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (ω : ConfigSpace (Sym2 W)) :
    wiredFkProb G bdryV p q (reCfgIso σ ω) = wiredFkProb H bdryW p q ω := by
  unfold wiredFkProb
  rw [fvs_wiredFkWeight_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω,
    fvs_wiredFkZ_reCfgIso G H bdryV bdryW σ hσ hbdry p q]











theorem fvs_edgeMargProb_reCfgIso_inv (σ : V ≃ W)
    (μV : ConfigSpace (Sym2 V) → ℝ) (μW : ConfigSpace (Sym2 W) → ℝ)
    (hμ : ∀ ω, μV (reCfgIso σ ω) = μW ω) (e : Sym2 V) :
    edgeMargProb μW (Sym2.map σ e) = edgeMargProb μV e := by
  unfold edgeMargProb
  rw [← Equiv.sum_comp (reCfgIsoEquiv σ).symm
    (fun ω => (if ω (Sym2.map σ e) then (1:ℝ) else 0) * μW ω)]
  apply Finset.sum_congr rfl
  intro ω _
  show (if ((reCfgIsoEquiv σ).symm ω) (Sym2.map σ e) then (1:ℝ) else 0)
      * μW ((reCfgIsoEquiv σ).symm ω) = _
  have hsymm : (reCfgIsoEquiv σ).symm ω = reCfgIso σ.symm ω := rfl
  rw [hsymm]
  have h1 : (reCfgIso σ.symm ω) (Sym2.map σ e) = ω e := by
    unfold reCfgIso; rw [Sym2.map_map]; simp
  rw [h1]
  have h2 : μW (reCfgIso σ.symm ω) = μV ω := by
    have := hμ (reCfgIso σ.symm ω)
    rw [fvs_reCfgIso_reCfgIso' σ ω] at this
    exact this.symm
  rw [h2]











theorem fvs_edgeMargProb_fkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (fkProb H p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e :=
  fvs_edgeMargProb_reCfgIso_inv σ (fkProb G p q) (fkProb H p q)
    (fun ω => fvs_fkProb_reCfgIso G H σ hσ p q ω) e





theorem fvs_edgeMargProb_wiredFkProb_reCfgIso (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (wiredFkProb H bdryW p q) (Sym2.map σ e)
      = edgeMargProb (wiredFkProb G bdryV p q) e :=
  fvs_edgeMargProb_reCfgIso_inv σ (wiredFkProb G bdryV p q) (wiredFkProb H bdryW p q)
    (fun ω => fvs_wiredFkProb_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω) e

















theorem fvs_finiteVolume_shift_invariant (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) (hbdry : ∀ x, bdryV x ↔ bdryW (σ x))
    (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (wiredFkProb H bdryW p q) (Sym2.map σ e)
        = edgeMargProb (wiredFkProb G bdryV p q) e
      ∧ edgeMargProb (fkProb H p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e :=
  ⟨fvs_edgeMargProb_wiredFkProb_reCfgIso G H bdryV bdryW σ hσ hbdry p q e,
    fvs_edgeMargProb_fkProb_reCfgIso G H σ hσ p q e⟩

end FK










namespace FK

open StatMech.Lattice

variable {d : ℕ}



def fvs_transBox (d m : ℕ) (v : Site d) : Set (Site d) := {y | (y - v) ∈ box d m}


abbrev fvs_transBoxVerts (d m : ℕ) (v : Site d) : Type :=
  {y : Site d // y ∈ fvs_transBox d m v}



noncomputable def fvs_transEquiv (d m : ℕ) (v : Site d) :
    boxVerts d m ≃ fvs_transBoxVerts d m v where
  toFun := fun x => ⟨(x : Site d) + v, by
    show ((x : Site d) + v - v) ∈ box d m
    rw [add_sub_cancel_right]; exact x.2⟩
  invFun := fun y => ⟨(y : Site d) - v, y.2⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro y; apply Subtype.ext; simp

@[simp] theorem fvs_transEquiv_val (d m : ℕ) (v : Site d) (x : boxVerts d m) :
    (fvs_transEquiv d m v x : Site d) = (x : Site d) + v := rfl



noncomputable instance fvs_instFintypeTransBoxVerts (d m : ℕ) (v : Site d) :
    Fintype (fvs_transBoxVerts d m v) :=
  Fintype.ofEquiv (boxVerts d m) (fvs_transEquiv d m v)

instance fvs_instDecidableEqTransBoxVerts (d m : ℕ) (v : Site d) :
    DecidableEq (fvs_transBoxVerts d m v) :=
  Subtype.instDecidableEq



def fvs_transBoxGraph (d m : ℕ) (v : Site d) : SimpleGraph (fvs_transBoxVerts d m v) :=
  SimpleGraph.comap Subtype.val (hypercubicLattice d)

noncomputable instance fvs_instDecidableRelTransBoxGraph (d m : ℕ) (v : Site d) :
    DecidableRel (fvs_transBoxGraph d m v).Adj :=
  Classical.decRel _




def fvs_transBoxBoundary (d m : ℕ) (v : Site d) (y : fvs_transBoxVerts d m v) : Prop :=
  ((y : Site d) - v) ∈ vertexBoundary d m

noncomputable instance fvs_instDecidablePredTransBoxBoundary (d m : ℕ) (v : Site d) :
    DecidablePred (fvs_transBoxBoundary d m v) :=
  fun _ => Classical.dec _



theorem fvs_transEquiv_adj (d m : ℕ) (v : Site d) (x y : boxVerts d m) :
    (boxGraph d m).Adj x y
      ↔ (fvs_transBoxGraph d m v).Adj (fvs_transEquiv d m v x) (fvs_transEquiv d m v y) := by
  rw [boxGraph, fvs_transBoxGraph, SimpleGraph.comap_adj, SimpleGraph.comap_adj]
  show (hypercubicLattice d).Adj x.val y.val
    ↔ (hypercubicLattice d).Adj ((x : Site d) + v) ((y : Site d) + v)
  simp only [hypercubicLattice_adj]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    rw [← h] <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> simp [Pi.add_apply]




theorem fvs_transEquiv_boundary (d m : ℕ) (v : Site d) (x : boxVerts d m) :
    boxBoundary d m x ↔ fvs_transBoxBoundary d m v (fvs_transEquiv d m v x) := by
  unfold boxBoundary fvs_transBoxBoundary
  show (x : Site d) ∈ vertexBoundary d m ↔ ((x : Site d) + v - v) ∈ vertexBoundary d m
  rw [add_sub_cancel_right]

















theorem fvs_box_translation_edgeMarg (d m : ℕ) (v : Site d) (eb : Sym2 (boxVerts d m))
    {p q : ℝ} :
    edgeMargProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q)
          (Sym2.map (fvs_transEquiv d m v) eb)
        = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) eb
      ∧ edgeMargProb (fkProb (fvs_transBoxGraph d m v) p q) (Sym2.map (fvs_transEquiv d m v) eb)
        = edgeMargProb (fkProb (boxGraph d m) p q) eb :=
  fvs_finiteVolume_shift_invariant (boxGraph d m) (fvs_transBoxGraph d m v)
    (boxBoundary d m) (fvs_transBoxBoundary d m v) (fvs_transEquiv d m v)
    (fvs_transEquiv_adj d m v) (fvs_transEquiv_boundary d m v) p q eb











theorem fvs_transBox_ne_box (d m : ℕ) (hd : 0 < d) :
    ∃ (v y : Site d), y ∈ fvs_transBox d m v ∧ y ∉ box d m := by
  refine ⟨fun i => if i = ⟨0, hd⟩ then 1 else 0,
          fun i => if i = ⟨0, hd⟩ then (m : ℤ) + 1 else 0, ?_, ?_⟩
  · show (fun i => (if i = ⟨0, hd⟩ then (m : ℤ) + 1 else 0)
        - (if i = ⟨0, hd⟩ then (1 : ℤ) else 0)) ∈ box d m
    intro i
    by_cases hi : i = ⟨0, hd⟩
    · simp only [hi, if_true]
      rw [show ((m : ℤ) + 1 - 1) = (m : ℤ) by ring, Int.natAbs_natCast]
    · simp [hi]
  · intro h
    have hi := h ⟨0, hd⟩
    simp only [if_true] at hi
    rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast] at hi
    omega

end FK

end StatMech
