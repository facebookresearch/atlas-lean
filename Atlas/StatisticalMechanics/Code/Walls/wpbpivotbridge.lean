/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.Walls.wcddefectbridge
import Code.Walls.jc5_singlecycle
import Code.Lattice.DartOrbit
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedProof

open scoped BigOperators
open Finset
open SimpleGraph Function

namespace StatMech

namespace Wpb

open StatMech.Lattice
open StatMech.Wad
open StatMech.Wcd
open StatMech.Walls
open StatMech.Euc










theorem wpb_pivot_inj_nonpinch (K : Set (Site 2)) {e e' : Dart}
    (he : IsBoundaryDart K e) (he' : IsBoundaryDart K e')
    (hnp : ¬(wcd_frontCell e ∈ K ∧ wcd_sideCell e ∉ K))
    (hpv : wcd_pivot e = wcd_pivot e') : e = e' := by
  obtain ⟨ht, hh⟩ := he
  obtain ⟨ht', hh'⟩ := he'
  have hhe : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  have hhe' : e'.head = e'.tail + e'.dir := by rw [Dart.dir_def]; abel
  have siteEq : ∀ p q : Site 2, p 0 = q 0 → p 1 = q 1 → p = q := by
    intro p q h0 h1; funext i; fin_cases i; exacts [h0, h1]
  
  have hp0 : (wcd_pivot e).1 = (wcd_pivot e').1 := congrArg Prod.fst hpv
  have hp1 : (wcd_pivot e).2 = (wcd_pivot e').2 := congrArg Prod.snd hpv
  rcases wcd_dir_cases e with hd | hd | hd | hd <;>
    rcases wcd_dir_cases e' with hd' | hd' | hd' | hd' <;>
    simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, hd, hd',
      Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_neg, neg_zero, max_self] at hp0 hp1 <;>
  first
    
    | (refine Dart.ext (siteEq _ _ ?_ ?_) (siteEq _ _ ?_ ?_) <;>
        (first
          | omega
          | (simp only [hhe, hhe', hd, hd', Pi.add_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)))
    
    | (exfalso; apply hh'
       have heq : e'.head = e.tail := by
         refine siteEq _ _ ?_ ?_ <;>
           (first
             | omega
             | (simp only [hhe, hhe', hd, hd', Pi.add_apply, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega))
       rw [heq]; exact ht)
    
    | (exfalso; apply hh
       have heq : e'.tail = e.head := by
         refine siteEq _ _ ?_ ?_ <;>
           (first
             | omega
             | (simp only [hhe, hhe', hd, hd', Pi.add_apply, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega))
       rw [← heq]; exact ht')
    
    | (exfalso; apply hnp; refine ⟨?_, ?_⟩
       · have heq : e'.tail = wcd_frontCell e := by
           refine siteEq _ _ ?_ ?_ <;>
             (first
               | omega
               | (simp only [wcd_frontCell, hhe, hhe', hd, hd', Pi.add_apply, Pi.neg_apply,
                   rot90Fun_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                   Matrix.cons_val_fin_one, neg_neg, neg_zero]; omega))
         rw [← heq]; exact ht'
       · have heq : e'.head = wcd_sideCell e := by
           refine siteEq _ _ ?_ ?_ <;>
             (first
               | omega
               | (simp only [wcd_sideCell, hhe, hhe', hd, hd', Pi.add_apply, Pi.neg_apply,
                   rot90Fun_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                   Matrix.cons_val_fin_one, neg_neg, neg_zero]; omega))
         rw [← heq]; exact hh')







def WpbPinchFree (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ i < dartOrbitPeriod K a,
    ¬(wcd_frontCell ((dartNext K)^[i] a.1) ∈ K ∧ wcd_sideCell ((dartNext K)^[i] a.1) ∉ K)





theorem wpb_pivotInjective (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) :
    Set.InjOn (fun i => wcd_pivot ((dartNext K)^[i] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
  intro i hi j hj hij
  have hii : i < dartOrbitPeriod K a := Set.mem_Iio.mp hi
  have hjj : j < dartOrbitPeriod K a := Set.mem_Iio.mp hj
  have hbi := iterate_isBoundaryDart K a.1 a.2 i
  have hbj := iterate_isBoundaryDart K a.1 a.2 j
  have hde : (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
    wpb_pivot_inj_nonpinch K hbi hbj (hpf i hii) hij
  have hsub : (dartNextSub K)^[i] a = (dartNextSub K)^[j] a := by
    apply Subtype.ext
    rw [dartNextSub_iterate_val, dartNextSub_iterate_val]; exact hde
  exact jc5_orbit_injOn_Iio K a hi hj hsub




theorem wpb_unitWt_e1 : unitWt (![1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]
theorem wpb_unitWt_me1 : unitWt (![-1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]
theorem wpb_unitWt_e2 : unitWt (![0, 1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]
theorem wpb_unitWt_me2 : unitWt (![0, -1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]









theorem wpb_defect_zero_of_no_boundary_pivot (K : Set (Site 2)) (hK : K.Finite)
    (x y : ℤ) (hv : ((x, y) : ℤ × ℤ) ∈ regVerts (wcd_toVtxFinset K hK))
    (hnp : ∀ e : Dart, IsBoundaryDart K e → wcd_pivot e ≠ (x, y)) :
    defect (wcd_toVtxFinset K hK) (x, y) = 0 := by
  classical
  set K' := wcd_toVtxFinset K hK with hK'
  have siteEq : ∀ p q : Site 2, p 0 = q 0 → p 1 = q 1 → p = q := by
    intro p q h0 h1; funext i; fin_cases i; exacts [h0, h1]
  
  have hmem : ∀ a b : ℤ, (![a, b] : Site 2) ∈ K ↔ ((a, b) : ℤ × ℤ) ∈ K' := by
    intro a b
    have h := (wcd_siteToVtx_mem_toVtxFinset K hK (![a, b] : Site 2)).symm
    rw [hK']
    simpa only [wcd_siteToVtx_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using h
  
  have notbd : ∀ (p g : Site 2) (h : unitWt g = 1),
      wcd_pivot (mkDart p g h) = (x, y) → ¬ ((p ∈ K) ∧ ((p + g) ∉ K)) := by
    intro p g h hpiv hbd
    exact hnp (mkDart p g h) hbd hpiv
  
  have impl : ∀ (ax ay bx byy : ℤ) (g : Site 2) (h : unitWt g = 1),
      ((![ax, ay] : Site 2) + g = ![bx, byy]) →
      wcd_pivot (mkDart ![ax, ay] g h) = (x, y) →
      ((ax, ay) ∈ K' → (bx, byy) ∈ K') := by
    intro ax ay bx byy g h hgadd hpiv hin
    by_contra hout
    exact notbd ![ax, ay] g h hpiv ⟨(hmem ax ay).mpr hin,
      by rw [hgadd]; exact fun hc => hout ((hmem bx byy).mp hc)⟩
  
  have hp1 : wcd_pivot (mkDart ![x-1, y] ![1, 0] wpb_unitWt_e1) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  have hp2 : wcd_pivot (mkDart ![x, y-1] ![-1, 0] wpb_unitWt_me1) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  have hp3 : wcd_pivot (mkDart ![x-1, y-1] ![0, 1] wpb_unitWt_e2) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  have hp4 : wcd_pivot (mkDart ![x, y] ![0, -1] wpb_unitWt_me2) = (x, y) := by
    refine Prod.ext ?_ ?_ <;>
      simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, mkDart_tail,
        mkDart_dir, Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_neg, neg_zero] <;> omega
  
  have ha1 : (![x-1, y] : Site 2) + ![1, 0] = ![x, y] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  have ha2 : (![x, y-1] : Site 2) + ![-1, 0] = ![x-1, y-1] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  have ha3 : (![x-1, y-1] : Site 2) + ![0, 1] = ![x-1, y] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  have ha4 : (![x, y] : Site 2) + ![0, -1] = ![x, y-1] := by
    refine siteEq _ _ ?_ ?_ <;>
      simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;> omega
  
  have i1 : ((x-1, y) ∈ K') → ((x, y) ∈ K') := impl (x-1) y x y ![1, 0] wpb_unitWt_e1 ha1 hp1
  have i2 : ((x, y-1) ∈ K') → ((x-1, y-1) ∈ K') :=
    impl x (y-1) (x-1) (y-1) ![-1, 0] wpb_unitWt_me1 ha2 hp2
  have i3 : ((x-1, y-1) ∈ K') → ((x-1, y) ∈ K') :=
    impl (x-1) (y-1) (x-1) y ![0, 1] wpb_unitWt_e2 ha3 hp3
  have i4 : ((x, y) ∈ K') → ((x, y-1) ∈ K') := impl x y x (y-1) ![0, -1] wpb_unitWt_me2 ha4 hp4
  
  have hdisj : (x-1, y-1) ∈ K' ∨ (x, y-1) ∈ K' ∨ (x-1, y) ∈ K' ∨ (x, y) ∈ K' := by
    rw [regVerts, Finset.mem_biUnion] at hv
    obtain ⟨c, hcK, hcv⟩ := hv
    rw [← wad_mem_surround_iff] at hcv
    unfold surroundCells at hcv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcv
    rcases hcv with rfl | rfl | rfl | rfl
    · exact Or.inl hcK
    · exact Or.inr (Or.inl hcK)
    · exact Or.inr (Or.inr (Or.inl hcK))
    · exact Or.inr (Or.inr (Or.inr hcK))
  
  have hall : (x-1, y-1) ∈ K' ∧ (x, y-1) ∈ K' ∧ (x-1, y) ∈ K' ∧ (x, y) ∈ K' := by
    tauto
  obtain ⟨hSW, hSE, hNW, hNE⟩ := hall
  
  have hcard4 : (surroundCells (x, y)).card = 4 := by
    simp only [surroundCells]
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton, Prod.mk.injEq]; omega),
        Finset.card_singleton]
  have hsub : surroundCells (x, y) ⊆ K' := by
    intro c hc
    unfold surroundCells at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> assumption
  have hcd : cellDeg K' (x, y) = 4 := by
    unfold cellDeg
    rw [Finset.inter_eq_left.mpr hsub, hcard4]
  
  have hed : (edgeDeg K' (x, y) : ℤ) = 4 := by
    rw [wcd_edgeDeg_formula K' x y]
    simp only [hSW, hSE, hNW, hNE, or_true, true_or, if_true]
    norm_num
  
  have hdef : (defect K' (x, y) : ℤ) = 4 - 2 * (edgeDeg K' (x, y) : ℤ) + (cellDeg K' (x, y) : ℤ) :=
    rfl
  rw [hdef, hed, hcd]; norm_num








def WpbOrbitCovers (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ d : Dart, IsBoundaryDart K d → SameOrbit K a.1 d





theorem wpb_covering_of_orbitCovers (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hcov : WpbOrbitCovers K a) :
    ∀ v ∈ regVerts (wcd_toVtxFinset K hK),
      v ∉ (Finset.range (dartOrbitPeriod K a)).image
        (fun i => wcd_pivot ((dartNext K)^[i] a.1)) →
      defect (wcd_toVtxFinset K hK) v = 0 := by
  classical
  intro v hv hvimg
  obtain ⟨x, y⟩ := v
  refine wpb_defect_zero_of_no_boundary_pivot K hK x y hv ?_
  intro e he hpe
  obtain ⟨n, hn⟩ := hcov e he
  have hpos := dartOrbitPeriod_pos K hK a
  have hmod : (dartNextSub K)^[n % dartOrbitPeriod K a] a = (dartNextSub K)^[n] a :=
    Function.iterate_mod_minimalPeriod_eq (f := dartNextSub K) (x := a) (n := n)
  have hval : (dartNext K)^[n % dartOrbitPeriod K a] a.1 = (dartNext K)^[n] a.1 := by
    have h := congrArg Subtype.val hmod
    rwa [dartNextSub_iterate_val, dartNextSub_iterate_val] at h
  apply hvimg
  rw [Finset.mem_image]
  refine ⟨n % dartOrbitPeriod K a, Finset.mem_range.mpr (Nat.mod_lt _ hpos), ?_⟩
  show wcd_pivot ((dartNext K)^[n % dartOrbitPeriod K a] a.1) = (x, y)
  rw [hval, hn, hpe]




theorem wpb_pivotBridge_of (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hcov : WpbOrbitCovers K a) :
    WcdPivotBridge K hK a :=
  ⟨hpf, wpb_pivotInjective K a hpf, wpb_covering_of_orbitCovers K hK a hcov⟩




theorem wpb_revCount_pm_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hcov : WpbOrbitCovers K a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wcd_revCount_pm_one K hK a (wpb_pivotBridge_of K hK a hpf hcov) hbuild



theorem wpb_balanceIsFour (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hcov : WpbOrbitCovers K a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    BalanceIsFour K a :=
  wcd_balanceIsFour K hK a (wpb_pivotBridge_of K hK a hpf hcov) hbuild











theorem wpb_frontCell_notMem_unitCell (e : Dart) (he : IsBoundaryDart unitCell e) :
    wcd_frontCell e ∉ unitCell := by
  intro hf
  have htail : e.tail = ![0, 0] := by
    have h := he.1; rwa [unitCell, Set.mem_singleton_iff] at h
  rw [unitCell, Set.mem_singleton_iff, wcd_frontCell] at hf
  have hhe : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  rw [hhe, htail] at hf
  apply dartDir_ne_zero e
  have h0 := congrFun hf 0
  have h1 := congrFun hf 1
  simp only [rot90Fun, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hz0 : e.dir 0 = 0 := by omega
  have hz1 : e.dir 1 = 0 := by omega
  funext i; fin_cases i
  · exact hz0
  · exact hz1


theorem wpb_witness_pinchFree_unitCell : WpbPinchFree unitCell ucBase := by
  intro i _ hconj
  exact wpb_frontCell_notMem_unitCell _
    (iterate_isBoundaryDart unitCell ucBase.1 ucBase.2 i) hconj.1




theorem wpb_witness_orbitCovers_unitCell : WpbOrbitCovers unitCell ucBase := by
  intro d hd
  exact ifc_singleton_sameOrbit (![0, 0] : Site 2) ucBase.1 d ucBase.2 hd



theorem wpb_witness_pivotBridge_unitCell :
    WcdPivotBridge unitCell wcd_unitCell_finite ucBase :=
  wpb_pivotBridge_of unitCell wcd_unitCell_finite ucBase
    wpb_witness_pinchFree_unitCell wpb_witness_orbitCovers_unitCell




theorem wpb_witness_revCount_unitCell : revCount unitCell ucBase = -1 := by
  have hbuild : EucBuildable (wcd_toVtxFinset unitCell wcd_unitCell_finite) := by
    rw [wcd_toVtxFinset_unitCell wcd_unitCell_finite]
    exact EucBuildable.singleton ((0 : ℤ), (0 : ℤ))
  exact wcd_revCount_eq_neg_one unitCell wcd_unitCell_finite ucBase
    wpb_witness_pivotBridge_unitCell hbuild

end Wpb

end StatMech

