/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.FK.InfiniteVolume
import Code.Ising.InfiniteVolume
import Code.Lattice.ClusterContourBijection
import Code.IsingFK.IsingBoxEncoding
import Code.IsingFK.MagPercoIdBox
import Code.IsingFK.MagnetizationCorrespondence

open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d n : ℕ}








theorem hbx_mem_bondFinsetTouch_iff (d n : ℕ) (a b : Site d) :
    s(a, b) ∈ bondFinsetTouch d n ↔
      ((hypercubicLattice d).Adj a b ∧ (a ∈ box d n ∨ b ∈ box d n)) := by
  rw [bondFinsetTouch, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, heq⟩
    rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨_, _⟩, hadj, htouch⟩ := hp
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; exact ⟨hadj, htouch⟩
    · subst h1; subst h2; exact ⟨hadj.symm, htouch.symm⟩
  · rintro ⟨hadj, htouch⟩
    refine ⟨(a, b), ?_, rfl⟩
    rw [bondPairsTouch, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, hadj, htouch⟩
    · rw [mem_boxFinset]
      rcases htouch with h | h
      · exact box_subset_succ d n h
      · exact ccb_adj_mem_box_succ hadj.symm h
    · rw [mem_boxFinset]
      rcases htouch with h | h
      · exact ccb_adj_mem_box_succ hadj h
      · exact box_subset_succ d n h




theorem hbx_mem_image_edgeIncl_iff (d m : ℕ) (a b : Site d) :
    s(a, b) ∈ Finset.image (edgeIncl d m) (boxGraph d m).edgeFinset ↔
      (a ∈ box d m ∧ b ∈ box d m ∧ (hypercubicLattice d).Adj a b) := by
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨e, he, heq⟩ := h
    induction e with
    | _ u v =>
      rw [edgeIncl, Sym2.map_mk] at heq
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph] at he
      simp only [SimpleGraph.comap_adj] at he
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2; exact ⟨u.2, v.2, he⟩
      · subst h1; subst h2; exact ⟨v.2, u.2, he.symm⟩
  · rintro ⟨ha, hb, hadj⟩
    rw [Finset.mem_image]
    refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph]
      simp only [SimpleGraph.comap_adj]; exact hadj
    · rw [edgeIncl, Sym2.map_mk]





theorem hbx_touch_subset_image (d n : ℕ) :
    bondFinsetTouch d n ⊆ Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset := by
  intro e he
  induction e with
  | _ a b =>
    rw [hbx_mem_bondFinsetTouch_iff] at he
    obtain ⟨hadj, htouch⟩ := he
    rw [hbx_mem_image_edgeIncl_iff]
    refine ⟨?_, ?_, hadj⟩
    · rcases htouch with h | h
      · exact box_subset_succ d n h
      · exact ccb_adj_mem_box_succ hadj.symm h
    · rcases htouch with h | h
      · exact ccb_adj_mem_box_succ hadj h
      · exact box_subset_succ d n h








theorem hbx_isingBond_latToBox_eq (d n : ℕ) (τ : {x // x ∈ box d n} → Bool)
    (e : Sym2 (boxVerts d (n + 1))) :
    isingBond (latToBox d n τ) e = bond (glue (plusField d) τ) (edgeIncl d (n + 1) e) := by
  induction e with
  | _ u v =>
    rw [isingBond_mk, edgeIncl, Sym2.map_mk, bond_mk, isingSpin_latToBox, isingSpin_latToBox]









theorem hbx_edge_energy (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) :
    ∑ e ∈ (boxGraph d (n + 1)).edgeFinset, isingBond (latToBox d n τ) e
      = (∑ e ∈ bondFinsetTouch d n, bond (glue (plusField d) τ) e)
        + ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
            \ bondFinsetTouch d n).card := by
  have hinj : Set.InjOn (edgeIncl d (n + 1))
      ((boxGraph d (n + 1)).edgeFinset : Set (Sym2 (boxVerts d (n + 1)))) :=
    (edgeIncl_injective d (n + 1)).injOn
  rw [Finset.sum_congr rfl (fun e _ => hbx_isingBond_latToBox_eq d n τ e),
    ← Finset.sum_image hinj (g := edgeIncl d (n + 1)) (f := bond (glue (plusField d) τ)),
    ← Finset.sum_sdiff (hbx_touch_subset_image d n)]
  have hcompl : ∑ e ∈ ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
        \ bondFinsetTouch d n), bond (glue (plusField d) τ) e
      = ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
          \ bondFinsetTouch d n).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_sdiff] at he
    obtain ⟨hin, hnotin⟩ := he
    induction e with
    | _ a b =>
      rw [hbx_mem_image_edgeIncl_iff] at hin
      obtain ⟨_, _, hadj⟩ := hin
      rw [hbx_mem_bondFinsetTouch_iff, not_and_or, not_or] at hnotin
      have hna : a ∉ box d n := by
        rcases hnotin with h | h
        · exact absurd hadj h
        · exact h.1
      have hnb : b ∉ box d n := by
        rcases hnotin with h | h
        · exact absurd hadj h
        · exact h.2
      rw [bond_mk, spin_true _ (by rw [glue_not_mem _ _ hna]; rfl),
        spin_true _ (by rw [glue_not_mem _ _ hnb]; rfl), Nat.cast_one]; ring
  rw [hcompl]; ring





def fToB (a : Fin 2) : Bool := a = 0

@[simp] theorem hbx_fToB_bToF (b : Bool) : fToB (bToF b) = b := by
  unfold fToB bToF; cases b <;> decide

@[simp] theorem hbx_bToF_fToB (a : Fin 2) : bToF (fToB a) = a := by
  unfold fToB bToF; fin_cases a <;> decide




theorem hbx_boxBoundary_succ_iff (d n : ℕ) (v : boxVerts d (n + 1)) :
    boxBoundary d (n + 1) v ↔ (v : Site d) ∉ box d n := by
  rw [boxBoundary, mem_vertexBoundary]; simp only [Nat.add_sub_cancel]
  exact ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩



noncomputable def boxToLat (d n : ℕ) (σ : boxVerts d (n + 1) → Fin 2) :
    {x // x ∈ box d n} → Bool :=
  fun x => fToB (σ ⟨x.1, box_subset_succ d n x.2⟩)






noncomputable def hbx_latBoxEquiv (d n : ℕ) :
    ({x // x ∈ box d n} → Bool) ≃
      {σ : boxVerts d (n + 1) → Fin 2 // BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ} where
  toFun τ := ⟨latToBox d n τ, boundaryFixed_latToBox d n τ⟩
  invFun σ := boxToLat d n σ.1
  left_inv τ := by
    funext x
    show boxToLat d n (latToBox d n τ) x = τ x
    unfold boxToLat latToBox
    rw [dif_pos x.2, hbx_fToB_bToF]
  right_inv σ := by
    apply Subtype.ext
    funext v
    show latToBox d n (boxToLat d n σ.1) v = σ.1 v
    unfold latToBox boxToLat
    by_cases h : (v : Site d) ∈ box d n
    · rw [dif_pos h, hbx_bToF_fToB]
    · rw [dif_neg h]; exact (σ.2 v ((hbx_boxBoundary_succ_iff d n v).mpr h)).symm





theorem hbx_sum_reindex (d n : ℕ) (f : (boxVerts d (n + 1) → Fin 2) → ℝ)
    (hf : ∀ σ, ¬ BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ → f σ = 0) :
    ∑ σ : boxVerts d (n + 1) → Fin 2, f σ
      = ∑ τ : {x // x ∈ box d n} → Bool, f (latToBox d n τ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun σ => BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ)]
  have hz : ∑ σ ∈ Finset.univ.filter
        (fun σ => ¬ BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ), f σ = 0 := by
    apply Finset.sum_eq_zero; intro σ hσ; exact hf σ (Finset.mem_filter.1 hσ).2
  rw [hz, add_zero,
    Finset.sum_subtype (p := fun σ => BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ)
      (Finset.univ.filter (fun σ => BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ))
      (fun σ => by simp) f,
    ← (hbx_latBoxEquiv d n).sum_comp
      (fun σ : {σ // BoundaryFixed (boxBoundary d (n + 1)) (0 : Fin 2) σ} => f σ.1)]
  rfl






theorem hbx_fvWeight_eq (d n : ℕ) (β : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ
      = Real.exp (β * ∑ e ∈ bondFinsetTouch d n, bond (glue (plusField d) τ) e) := by
  unfold fvWeight fvEnergy
  congr 1; ring







theorem hbx_isingWiredWeight_latToBox (d n : ℕ) (β : ℝ) (τ : {x // x ∈ box d n} → Bool) :
    isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β (latToBox d n τ)
      = Real.exp (β * ((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
              \ bondFinsetTouch d n).card)
          * fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ := by
  unfold isingWiredWeight
  rw [if_pos (boundaryFixed_latToBox d n τ), hbx_edge_energy, hbx_fvWeight_eq,
    mul_add, Real.exp_add]
  ring


















theorem hbx_isingWiredOnePoint_eq_fvMagnetization (d n : ℕ) (β : ℝ) :
    isingWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β (boxOrigin d (n + 1))
      = fvMagnetization d β n := by
  classical
  set C : ℝ := (((Finset.image (edgeIncl d (n + 1)) (boxGraph d (n + 1)).edgeFinset)
      \ bondFinsetTouch d n).card : ℝ) with hCdef
  set E : ℝ := Real.exp (β * C) with hEdef
  have hE0 : E ≠ 0 := (Real.exp_pos _).ne'
  
  have hnum : (∑ σ : boxVerts d (n + 1) → Fin 2,
        isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β σ
          * isingSpin (σ (boxOrigin d (n + 1))))
      = E * ∑ τ : {x // x ∈ box d n} → Bool,
          fvWeight (plusField d) n (bondFinsetTouch d n) β 0 τ
            * spin (glue (plusField d) τ) (Ising.origin d) := by
    rw [hbx_sum_reindex d n
      (fun σ => isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β σ
        * isingSpin (σ (boxOrigin d (n + 1))))
      (fun σ hσ => by simp only [isingWiredWeight, if_neg hσ, zero_mul])]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hbx_isingWiredWeight_latToBox]
    have hspin : isingSpin (latToBox d n τ (boxOrigin d (n + 1)))
        = spin (glue (plusField d) τ) (Ising.origin d) := by
      rw [isingSpin_latToBox]; rfl
    rw [hspin, ← hEdef]; ring
  
  have hden : isingWiredZ (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β
      = E * fvZ (plusField d) n (bondFinsetTouch d n) β 0 := by
    unfold isingWiredZ fvZ
    rw [hbx_sum_reindex d n
      (fun σ => isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) β σ)
      (fun σ hσ => by simp only [isingWiredWeight, if_neg hσ]),
      Finset.mul_sum]
    exact Finset.sum_congr rfl (fun τ _ => hbx_isingWiredWeight_latToBox d n β τ)
  
  rw [isingWiredOnePoint, hnum, hden, mul_div_mul_left _ _ hE0,
    fvMagnetization_eq_fvProb_sum]
  unfold fvProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [show Ising.origin d = Percolation.origin d from rfl]
  ring



















theorem hbx_hisingBox (d : ℕ) :
    ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)) := by
  intro β _ n _
  rw [esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint,
    hbx_isingWiredOnePoint_eq_fvMagnetization]










theorem hbx_htransition (d : ℕ) (hd : 1 ≤ d)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) :=
  Ising.mfc_htransition d hd (hbx_hisingBox d) hFKsub hpc1







theorem hbx_ising_transition (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  Ising.mfc_ising_transition d hd hmag_nonneg (hbx_hisingBox d) hFKsub hpc0 hpc1





theorem hbx_isingBetaC_eq (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  Ising.mfc_isingBetaC_eq d hd hmag_nonneg (hbx_hisingBox d) hFKsub hpc0 hpc1




theorem hbx_isingBetaC_pos (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  Ising.mfc_isingBetaC_pos d hd hmag_nonneg (hbx_hisingBox d) hFKsub hpc0 hpc1

end IsingFK

end StatMech
