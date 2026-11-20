/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.FK.DensityFiniteToInfinite

open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace







variable {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def reCfg (σ : V ≃ V) (ω : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  fun e => ω (Sym2.map σ e)

theorem fkTI_reCfg_apply (σ : V ≃ V) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    reCfg σ ω e = ω (Sym2.map σ e) := rfl

theorem fkTI_reCfg_reCfg (σ : V ≃ V) (ω : ConfigSpace (Sym2 V)) :
    reCfg σ.symm (reCfg σ ω) = ω := by
  funext e; unfold reCfg; rw [Sym2.map_map]; simp

theorem fkTI_reCfg_reCfg' (σ : V ≃ V) (ω : ConfigSpace (Sym2 V)) :
    reCfg σ (reCfg σ.symm ω) = ω := by
  funext e; unfold reCfg; rw [Sym2.map_map]; simp


noncomputable def reCfgEquiv (σ : V ≃ V) :
    ConfigSpace (Sym2 V) ≃ ConfigSpace (Sym2 V) where
  toFun := reCfg σ
  invFun := reCfg σ.symm
  left_inv := fkTI_reCfg_reCfg σ
  right_inv := fkTI_reCfg_reCfg' σ







variable (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def fkTI_openSubIso (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (ω : ConfigSpace (Sym2 V)) :
    openSub G (reCfg σ ω) ≃g openSub G ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [openSub_adj, reCfg]
    rw [Sym2.map_mk, hσ x y]


theorem fkTI_numClusters_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (ω : ConfigSpace (Sym2 V)) :
    numClusters G (reCfg σ ω) = numClusters G ω := by
  unfold numClusters
  exact Fintype.card_congr (fkTI_openSubIso G σ hσ ω).connectedComponentEquiv



omit [DecidableEq V] in

theorem fkTI_mem_edgeFinset_map (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    Sym2.map σ e ∈ G.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hσ]
  exact he

omit [DecidableEq V] in

theorem fkTI_mem_edgeFinset_map_symm (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    Sym2.map σ.symm e ∈ G.edgeFinset := by
  induction e using Sym2.ind with | _ a b =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  rw [← hσ]; simpa using he




theorem fkTI_edgeProduct_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (reCfg σ ω) = edgeProduct G p ω := by
  unfold edgeProduct reCfg
  apply Finset.prod_bij' (i := fun e _ => Sym2.map σ e) (j := fun e _ => Sym2.map σ.symm e)
  · intro a ha; exact fkTI_mem_edgeFinset_map G σ hσ ha
  · intro a ha; exact fkTI_mem_edgeFinset_map_symm G σ hσ ha
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rw [Sym2.map_map]; simp
  · intro a ha; rfl




theorem fkTI_fkWeight_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q (reCfg σ ω) = fkWeight G p q ω := by
  unfold fkWeight
  rw [fkTI_edgeProduct_reCfg G σ hσ p ω, fkTI_numClusters_reCfg G σ hσ ω]



theorem fkTI_fkZ_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) :
    fkZ G p q = ∑ ω : ConfigSpace (Sym2 V), fkWeight G p q (reCfg σ ω) := by
  unfold fkZ
  exact Finset.sum_congr rfl fun ω _ => (fkTI_fkWeight_reCfg G σ hσ p q ω).symm


theorem fkTI_fkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkProb G p q (reCfg σ ω) = fkProb G p q ω := by
  unfold fkProb
  rw [fkTI_fkWeight_reCfg G σ hσ p q ω]







variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def fkTI_wiredGraphIso (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (ω : ConfigSpace (Sym2 V)) :
    StatMech.Lattice.wiredGraph G bdry (reCfg σ ω) ≃g StatMech.Lattice.wiredGraph G bdry ω where
  toEquiv := σ
  map_rel_iff' := by
    intro x y
    simp only [StatMech.Lattice.wiredGraph_adj, reCfg]
    rw [Sym2.map_mk, hσ x y, hbdry x, hbdry y]
    constructor
    · rintro (h | ⟨hne, hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun h => hne (by rw [h]), hx, hy⟩
    · rintro (h | ⟨hne, hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨fun h => hne (σ.injective h), hx, hy⟩


theorem fkTI_numClustersWired_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (ω : ConfigSpace (Sym2 V)) :
    StatMech.Lattice.numClustersWired G bdry (reCfg σ ω)
      = StatMech.Lattice.numClustersWired G bdry ω := by
  unfold StatMech.Lattice.numClustersWired
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (fkTI_wiredGraphIso G bdry σ hσ hbdry ω).connectedComponentEquiv


theorem fkTI_wiredFkWeight_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q (reCfg σ ω) = wiredFkWeight G bdry p q ω := by
  unfold wiredFkWeight
  rw [fkTI_edgeProduct_reCfg G σ hσ p ω, fkTI_numClustersWired_reCfg G bdry σ hσ hbdry ω]


theorem fkTI_wiredFkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q (reCfg σ ω) = wiredFkProb G bdry p q ω := by
  unfold wiredFkProb
  rw [fkTI_wiredFkWeight_reCfg G bdry σ hσ hbdry p q ω]









theorem fkTI_edgeMargProb_reCfg_inv (σ : V ≃ V) (μ : ConfigSpace (Sym2 V) → ℝ)
    (hμ : ∀ ω, μ (reCfg σ.symm ω) = μ ω) (e : Sym2 V) :
    edgeMargProb μ (Sym2.map σ e) = edgeMargProb μ e := by
  unfold edgeMargProb
  rw [← Equiv.sum_comp (reCfgEquiv σ.symm)
    (fun ω => (if ω (Sym2.map σ e) then (1:ℝ) else 0) * μ ω)]
  apply Finset.sum_congr rfl
  intro ω _
  show (if (reCfg σ.symm ω) (Sym2.map σ e) then (1:ℝ) else 0) * μ (reCfg σ.symm ω) = _
  have h1 : (reCfg σ.symm ω) (Sym2.map σ e) = ω e := by
    unfold reCfg; rw [Sym2.map_map]; simp
  rw [h1, hμ ω]


theorem fkTI_edgeMargProb_fkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (fkProb G p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e := by
  refine fkTI_edgeMargProb_reCfg_inv σ (fkProb G p q) (fun ω => ?_) e
  exact fkTI_fkProb_reCfg G σ.symm (fun x y => by
    rw [← hσ (σ.symm x) (σ.symm y)]; simp) p q ω


theorem fkTI_edgeMargProb_wiredFkProb_reCfg (σ : V ≃ V)
    (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) (hbdry : ∀ x, bdry (σ x) ↔ bdry x)
    (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (wiredFkProb G bdry p q) (Sym2.map σ e)
      = edgeMargProb (wiredFkProb G bdry p q) e := by
  refine fkTI_edgeMargProb_reCfg_inv σ (wiredFkProb G bdry p q) (fun ω => ?_) e
  refine fkTI_wiredFkProb_reCfg G bdry σ.symm (fun x y => by
    rw [← hσ (σ.symm x) (σ.symm y)]; simp) (fun x => by rw [← hbdry (σ.symm x)]; simp) p q ω

end FK



namespace FK

open StatMech.Lattice

variable {d : ℕ}





structure BoxSym (d : ℕ) where
  
  τ : Site d ≃ Site d
  
  adj : ∀ x y, (hypercubicLattice d).Adj (τ x) (τ y) ↔ (hypercubicLattice d).Adj x y
  
  box_mem : ∀ n x, τ x ∈ box d n ↔ x ∈ box d n



def BoxSym.lift (S : BoxSym d) (n : ℕ) : boxVerts d n ≃ boxVerts d n where
  toFun := fun x => ⟨S.τ x.val, (S.box_mem n x.val).mpr x.property⟩
  invFun := fun x => ⟨S.τ.symm x.val, by
    rw [← S.box_mem n (S.τ.symm x.val), Equiv.apply_symm_apply]; exact x.property⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro x; apply Subtype.ext; simp

@[simp] theorem BoxSym.lift_val (S : BoxSym d) (n : ℕ) (x : boxVerts d n) :
    (S.lift n x : Site d) = S.τ x.val := rfl


theorem BoxSym.lift_adj (S : BoxSym d) (n : ℕ) (x y : boxVerts d n) :
    (boxGraph d n).Adj (S.lift n x) (S.lift n y) ↔ (boxGraph d n).Adj x y := by
  rw [boxGraph, SimpleGraph.comap_adj, SimpleGraph.comap_adj]
  show (hypercubicLattice d).Adj (S.τ x.val) (S.τ y.val) ↔ _
  rw [S.adj]


theorem BoxSym.lift_boundary (S : BoxSym d) (n : ℕ) (x : boxVerts d n) :
    boxBoundary d n (S.lift n x) ↔ boxBoundary d n x := by
  unfold boxBoundary
  show S.τ x.val ∈ vertexBoundary d n ↔ x.val ∈ vertexBoundary d n
  simp only [mem_vertexBoundary, S.box_mem]



theorem BoxSym.lift_boxVertInclLE (S : BoxSym d) {N m : ℕ} (h : N ≤ m) (x : boxVerts d N) :
    S.lift m (boxVertInclLE d h x) = boxVertInclLE d h (S.lift N x) := by
  apply Subtype.ext
  show S.τ x.val = S.τ x.val
  rfl


theorem BoxSym.lift_innerEdgeLE (S : BoxSym d) {N m : ℕ} (h : N ≤ m) (eb : Sym2 (boxVerts d N)) :
    Sym2.map (S.lift m) (innerEdgeLE d h eb) = innerEdgeLE d h (Sym2.map (S.lift N) eb) := by
  unfold innerEdgeLE
  rw [Sym2.map_map, Sym2.map_map]
  apply Sym2.map_congr
  intro z _
  exact S.lift_boxVertInclLE h z







theorem fkTI_box_wired_edgeMarg_inv (S : BoxSym d) (m : ℕ) {p : ℝ} (e : Sym2 (boxVerts d m)) :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (Sym2.map (S.lift m) e)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e :=
  fkTI_edgeMargProb_wiredFkProb_reCfg (boxGraph d m) (boxBoundary d m) (S.lift m)
    (S.lift_adj m) (S.lift_boundary m) p 2 e


theorem fkTI_box_free_edgeMarg_inv (S : BoxSym d) (m : ℕ) {p : ℝ} (e : Sym2 (boxVerts d m)) :
    edgeMargProb (fkProb (boxGraph d m) p 2) (Sym2.map (S.lift m) e)
      = edgeMargProb (fkProb (boxGraph d m) p 2) e :=
  fkTI_edgeMargProb_fkProb_reCfg (boxGraph d m) (S.lift m) (S.lift_adj m) p 2 e




















theorem fkTI_wired_density_shift_inv (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
  
  have hlim₁ := dfi_wired_density_eq_limit N eb hp hp1
  have hlim₂ := dfi_wired_density_eq_limit N (Sym2.map (S.lift N) eb) hp hp1
  refine tendsto_nhds_unique hlim₁ ?_
  refine hlim₂.congr (fun k => ?_)
  
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) eb,
    fkTI_box_wired_edgeMarg_inv S (N+k) (innerEdgeLE d (Nat.le_add_right N k) eb)]






theorem fkTI_free_density_shift_inv (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
  have hlim₁ := dfi_free_density_eq_limit N eb hp hp1
  have hlim₂ := dfi_free_density_eq_limit N (Sym2.map (S.lift N) eb) hp hp1
  refine tendsto_nhds_unique hlim₁ ?_
  refine hlim₂.congr (fun k => ?_)
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) eb,
    fkTI_box_free_edgeMarg_inv S (N+k) (innerEdgeLE d (Nat.le_add_right N k) eb)]








def fkTI_signFlipEquiv (d : ℕ) (j : Fin d) : Site d ≃ Site d where
  toFun := fun x i => if i = j then -(x i) else x i
  invFun := fun x i => if i = j then -(x i) else x i
  left_inv := by intro x; funext i; by_cases h : i = j <;> simp [h]
  right_inv := by intro x; funext i; by_cases h : i = j <;> simp [h]




def fkTI_signFlip (d : ℕ) (j : Fin d) : BoxSym d where
  τ := fkTI_signFlipEquiv d j
  adj := by
    intro x y
    simp only [hypercubicLattice_adj, fkTI_signFlipEquiv, Equiv.coe_fn_mk]
    have hcoord : ∀ i : Fin d,
        ((if i = j then -(x i) else x i) - (if i = j then -(y i) else y i)).natAbs
          = (x i - y i).natAbs := by
      intro i
      by_cases hh : i = j
      · rw [if_pos hh, if_pos hh, show -(x i) - -(y i) = -(x i - y i) by ring, Int.natAbs_neg]
      · rw [if_neg hh, if_neg hh]
    rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  box_mem := by
    intro n x
    simp only [mem_box, fkTI_signFlipEquiv, Equiv.coe_fn_mk]
    have hcoord : ∀ i : Fin d, (if i = j then -(x i) else x i).natAbs = (x i).natAbs := by
      intro i
      by_cases hh : i = j
      · rw [if_pos hh, Int.natAbs_neg]
      · rw [if_neg hh]
    constructor
    · intro h i; rw [← hcoord i]; exact h i
    · intro h i; rw [hcoord i]; exact h i




theorem fkTI_signFlip_moves (d : ℕ) (j : Fin d) (x : Site d) (hx : x j ≠ 0) :
    (fkTI_signFlip d j).τ x ≠ x := by
  intro h
  have hj : (fkTI_signFlip d j).τ x j = x j := by rw [h]
  have hflip : (fkTI_signFlip d j).τ x j = -(x j) := by
    show (if j = j then -(x j) else x j) = -(x j)
    rw [if_pos rfl]
  rw [hflip] at hj
  omega













theorem fkTI_box_density_bound_wired_const (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB₀ : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB₀, wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (EB₀.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB₀.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  have hsum : (∑ eb ∈ EB₀, wiredEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB₀.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_wired N n hNn EB₀ hp hp1



theorem fkTI_box_density_bound_free_const (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB₀ : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB₀, freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB₀.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ (EB₀.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  have hsum : (∑ eb ∈ EB₀, freeEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB₀.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_free N n hNn EB₀ hp hp1

end FK

end StatMech
