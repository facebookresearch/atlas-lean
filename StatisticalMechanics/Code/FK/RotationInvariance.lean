/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































import Code.FK.TranslationInvariance
import Code.FK.BulkDeviationProof
import Code.FK.OffCentreSandwichProof

open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.show false

namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}










def rot_permEquiv (d : ℕ) (π : Equiv.Perm (Fin d)) : Site d ≃ Site d where
  toFun := fun x i => x (π.symm i)
  invFun := fun x i => x (π i)
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp

@[simp] theorem rot_permEquiv_apply (d : ℕ) (π : Equiv.Perm (Fin d)) (x : Site d) (i : Fin d) :
    rot_permEquiv d π x i = x (π.symm i) := rfl




def rot_permBoxSym (d : ℕ) (π : Equiv.Perm (Fin d)) : BoxSym d where
  τ := rot_permEquiv d π
  adj := by
    intro x y
    simp only [hypercubicLattice_adj, rot_permEquiv_apply]
    rw [← Equiv.sum_comp π.symm (fun i => (x i - y i).natAbs)]
  box_mem := by
    intro n x
    simp only [mem_box, rot_permEquiv_apply]
    refine ⟨fun h i => ?_, fun h i => h (π.symm i)⟩
    have := h (π i); simpa using this











theorem rot_lift_edgeIncl (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N)) :
    edgeIncl d N (Sym2.map (S.lift N) eb) = Sym2.map S.τ (edgeIncl d N eb) := by
  unfold edgeIncl
  rw [Sym2.map_map, Sym2.map_map]
  apply Sym2.map_congr
  intro z _
  exact BoxSym.lift_val S N z


theorem rot_site_mem_box (x : Site d) :
    x ∈ box d (Finset.univ.sup (fun i => (x i).natAbs)) :=
  fun i => Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)




theorem rot_free_density_boxSym (S : BoxSym d) (e : Sym2 (Site d))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (Sym2.map S.τ e) p = freeEdgeDensity d 2 e p := by
  induction e with
  | h x y =>
    obtain ⟨N, hxN, hyN⟩ : ∃ N, x ∈ box d N ∧ y ∈ box d N :=
      ⟨max (Finset.univ.sup (fun i => (x i).natAbs))
            (Finset.univ.sup (fun i => (y i).natAbs)),
        fun i => le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _),
        fun i => le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)⟩
    set eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N)) with heb
    have hincl : edgeIncl d N eb = s(x, y) := by
      unfold edgeIncl; rw [heb, Sym2.map_mk]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkTI_free_density_shift_inv S N eb hp hp1).symm



theorem rot_wired_density_boxSym (S : BoxSym d) (e : Sym2 (Site d))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (Sym2.map S.τ e) p = wiredEdgeDensity d 2 e p := by
  induction e with
  | h x y =>
    obtain ⟨N, hxN, hyN⟩ : ∃ N, x ∈ box d N ∧ y ∈ box d N :=
      ⟨max (Finset.univ.sup (fun i => (x i).natAbs))
            (Finset.univ.sup (fun i => (y i).natAbs)),
        fun i => le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _),
        fun i => le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)⟩
    set eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N)) with heb
    have hincl : edgeIncl d N eb = s(x, y) := by
      unfold edgeIncl; rw [heb, Sym2.map_mk]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkTI_wired_density_shift_inv S N eb hp hp1).symm







theorem rot_free_density_recentre (x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  rw [bdp_freeEdgeDensity_translation_inv hp hp1 (Multiplicative.ofAdd x) (s(x, y))]
  congr 1
  show s((Multiplicative.ofAdd x)⁻¹ • x, (Multiplicative.ofAdd x)⁻¹ • y) = s((0 : Site d), y - x)
  have h1 : (Multiplicative.ofAdd x)⁻¹ • x = (0 : Site d) := by
    show -x + x = 0; rw [neg_add_cancel]
  have h2 : (Multiplicative.ofAdd x)⁻¹ • y = y - x := by
    show -x + y = y - x; abel
  rw [h1, h2]



theorem rot_wired_density_recentre (x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  rw [bdp_wiredEdgeDensity_translation_inv hp hp1 (Multiplicative.ofAdd x) (s(x, y))]
  congr 1
  show s((Multiplicative.ofAdd x)⁻¹ • x, (Multiplicative.ofAdd x)⁻¹ • y) = s((0 : Site d), y - x)
  have h1 : (Multiplicative.ofAdd x)⁻¹ • x = (0 : Site d) := by
    show -x + x = 0; rw [neg_add_cancel]
  have h2 : (Multiplicative.ofAdd x)⁻¹ • y = y - x := by
    show -x + y = y - x; abel
  rw [h1, h2]









theorem rot_candMap_apply (j : Fin d) (b : Bool) (i : Fin d) :
    candMap d (0 : Site d) (j, b) i = (if i = j then (if b then 1 else -1) else 0) := by
  show Function.update (0 : Site d) j ((0 : Site d) j + (if b then 1 else -1)) i = _
  by_cases h : i = j
  · subst h; rw [Function.update_self]; simp
  · rw [Function.update_of_ne h]; simp [h]


theorem rot_boxSym_fixes_zero (S : BoxSym d) : S.τ (0 : Site d) = 0 := by
  
  have h0 : S.τ (0 : Site d) ∈ box d 0 := (S.box_mem 0 0).mpr (fun i => by simp)
  funext i
  have hi : (S.τ (0 : Site d) i).natAbs ≤ 0 := h0 i
  have : (S.τ (0 : Site d) i).natAbs = 0 := Nat.le_zero.mp hi
  simpa using Int.natAbs_eq_zero.mp this



theorem rot_signFlip_neg_to_pos (j : Fin d) :
    (fkTI_signFlip d j).τ (candMap d (0 : Site d) (j, false)) = candMap d (0 : Site d) (j, true) := by
  funext i
  show (if i = j then -(candMap d (0 : Site d) (j, false) i) else candMap d (0 : Site d) (j, false) i)
      = candMap d (0 : Site d) (j, true) i
  rw [rot_candMap_apply, rot_candMap_apply]
  by_cases h : i = j <;> simp [h]



theorem rot_permEquiv_axis_to_zero (j : Fin d) (hd : 0 < d) :
    rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true))
      = candMap d (0 : Site d) (⟨0, hd⟩, true) := by
  funext i
  show (candMap d (0 : Site d) (j, true)) ((Equiv.swap (⟨0, hd⟩ : Fin d) j).symm i)
      = candMap d (0 : Site d) (⟨0, hd⟩, true) i
  rw [rot_candMap_apply, rot_candMap_apply, Equiv.symm_swap]
  have hiff : ((Equiv.swap (⟨0, hd⟩ : Fin d) j) i = j) ↔ (i = ⟨0, hd⟩) := by
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  by_cases h : (Equiv.swap (⟨0, hd⟩ : Fin d) j) i = j
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]








def rot_refUnitEdge (d : ℕ) (hd : 0 < d) : Sym2 (Site d) :=
  s((0 : Site d), candMap d (0 : Site d) (⟨0, hd⟩, true))



theorem rot_map_centred_edge (S : BoxSym d) (w : Site d) :
    Sym2.map S.τ (s((0 : Site d), w) : Sym2 (Site d)) = s((0 : Site d), S.τ w) := by
  rw [Sym2.map_mk, rot_boxSym_fixes_zero S]



theorem rot_free_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  
  have hpos : freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← rot_free_density_boxSym (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  
  rw [hpos, ← rot_free_density_boxSym (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1,
      rot_map_centred_edge]
  show freeEdgeDensity d 2 (s((0 : Site d),
        rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl


theorem rot_wired_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  have hpos : wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← rot_wired_density_boxSym (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← rot_wired_density_boxSym (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1,
      rot_map_centred_edge]
  show wiredEdgeDensity d 2 (s((0 : Site d),
        rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl









theorem rot_edge_dir (x y : Site d) (hadj : (hypercubicLattice d).Adj x y) :
    ∃ p : Fin d × Bool, y - x = candMap d (0 : Site d) p := by
  change NearestNeighbour d x y at hadj
  rw [nearestNeighbour_iff_shift] at hadj
  obtain ⟨j, s, hs, hys⟩ := hadj
  refine ⟨(j, decide (s = 1)), ?_⟩
  funext i
  show y i - x i = candMap d (0 : Site d) (j, decide (s = 1)) i
  rw [rot_candMap_apply, hys]
  show (Function.update x j (x j + s)) i - x i = _
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]
    rcases hs with rfl | rfl <;> simp
  · rw [Function.update_of_ne hi]; simp [hi]



theorem rot_free_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [rot_free_density_recentre x y hp hp1, hdir]
  exact rot_free_centred_unit_const hd j b hp hp1


theorem rot_wired_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [rot_wired_density_recentre x y hp hp1, hdir]
  exact rot_wired_centred_unit_const hd j b hp hp1








theorem rot_free_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d m eb) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    show freeEdgeDensity d 2 (s((u : Site d), (v : Site d)) : Sym2 (Site d)) p = _
    exact rot_free_edge_const hd (u : Site d) (v : Site d) heb hp hp1


theorem rot_wired_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d m eb) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    show wiredEdgeDensity d 2 (s((u : Site d), (v : Site d)) : Sym2 (Site d)) p = _
    exact rot_wired_edge_const hd (u : Site d) (v : Site d) heb hp hp1



theorem rot_freeRotationResidue (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_FreeRotationResidue (d := d) N e' t := by
  intro m eb heb
  rw [rot_free_box_edge_const hd m eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t),
      rot_free_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]


theorem rot_wiredRotationResidue (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_WiredRotationResidue (d := d) N e' t := by
  intro m eb heb
  rw [rot_wired_box_edge_const hd m eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t),
      rot_wired_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)]











theorem rot_freeRotationResidue_edges (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_FreeRotationResidue (d := d) N e' t :=
  rot_freeRotationResidue hd N e' he' t


theorem rot_wiredRotationResidue_edges (hd : 0 < d) (N : ℕ) (e' : Sym2 (boxVerts d N))
    (he' : e' ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    ocs_WiredRotationResidue (d := d) N e' t :=
  rot_wiredRotationResidue hd N e' he' t

























set_option maxHeartbeats 1000000 in







theorem rot_fk_uniqueness_of_diag (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hfreeDiag : ∀ (e' : Sym2 (boxVerts d N)), e' ∉ (boxGraph d N).edgeFinset →
      ∀ (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
    (hwiredDiag : ∀ (e' : Sym2 (boxVerts d N)), e' ∉ (boxGraph d N).edgeFinset →
      ∀ (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ocs_fk_uniqueness_of_rotation hd N eb hEbox hg hboxfree
    (fun e' t => by
      by_cases he' : e' ∈ (boxGraph d N).edgeFinset
      · exact rot_freeRotationResidue hd N e' he' t
      · exact hfreeDiag e' he' t)
    (fun e' t => by
      by_cases he' : e' ∈ (boxGraph d N).edgeFinset
      · exact rot_wiredRotationResidue hd N e' he' t
      · exact hwiredDiag e' he' t)

end FK

end StatMech
