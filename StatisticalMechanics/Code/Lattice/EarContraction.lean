/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval
import Code.Lattice.EarExistence

open SimpleGraph Function

namespace StatMech

namespace Lattice











noncomputable def cornerBalance (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : ℤ :=
  rightCornerCount K a.1 (dartOrbitPeriod K a) - leftCornerCount K a.1 (dartOrbitPeriod K a)



theorem cornerBalance_eq_totalTurnZ (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K a = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  unfold cornerBalance
  rw [totalTurnZ_eq_cornerBalance]



theorem simplePolygonCornerBalance_iff_cornerBalance (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    SimplePolygonCornerBalance K a ↔ (cornerBalance K a = 4 ∨ cornerBalance K a = -4) := by
  unfold SimplePolygonCornerBalance cornerBalance
  rfl









theorem extremeCell_up_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![0, 1] ∉ K := by
  apply extremeCell_not_mem_of_higher K c _ hc; simp [Pi.add_apply]


theorem extremeCell_left_nmem (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    c + ![-1, 0] ∉ K := by
  apply extremeCell_not_mem_of_left K c _ hc <;> simp [Pi.add_apply]




theorem adj_neighbor_cases (v c : Site 2) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![1, 0] ∨ v = c + ![-1, 0] ∨ v = c + ![0, 1] ∨ v = c + ![0, -1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have key : ((v 0 - c 0).natAbs = 1 ∧ (v 1 - c 1).natAbs = 0) ∨
             ((v 0 - c 0).natAbs = 0 ∧ (v 1 - c 1).natAbs = 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases Int.natAbs_eq_iff.mp h0 with h | h
    · left; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega
    · right; left; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega
  · rcases Int.natAbs_eq_iff.mp h1 with h | h
    · right; right; left; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega
    · right; right; right; funext i; fin_cases i <;> simp [Pi.add_apply] <;> omega





theorem extremeCell_neighbor_right_or_down (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![1, 0] ∨ v = c + ![0, -1] := by
  rcases adj_neighbor_cases v c hadj with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hv) (extremeCell_left_nmem K c hc)
  · exact absurd (h ▸ hv) (extremeCell_up_nmem K c hc)
  · exact Or.inr h











def CellConnected (K : Set (Site 2)) : Prop :=
  ((hypercubicLattice 2).induce K).Connected



noncomputable def diffEquiv (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K) :
    {x : K // x ≠ (⟨c, hc⟩ : K)} ≃ ↑(K \ {c}) where
  toFun := fun x => ⟨x.1.1, by
    refine ⟨x.1.2, ?_⟩
    simp only [Set.mem_singleton_iff]; intro h; exact x.2 (Subtype.ext h)⟩
  invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
    intro h; exact y.2.2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val h))⟩
  left_inv := fun _ => by rfl
  right_inv := fun _ => by rfl





noncomputable def diffIso (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K) :
    (((hypercubicLattice 2).induce K).induce {(⟨c, hc⟩ : K)}ᶜ) ≃g
      ((hypercubicLattice 2).induce (K \ {c})) where
  toEquiv := diffEquiv K c hc
  map_rel_iff' := by intro a b; rfl




theorem cellConnected_diff_of_iso (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (h : (((hypercubicLattice 2).induce K).induce {(⟨c, hc⟩ : K)}ᶜ).Connected) :
    CellConnected (K \ {c}) :=
  Connected.map (diffIso K c hc).toHom (diffIso K c hc).toEquiv.surjective h







theorem cellConnected_diff_of_degree_one (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (hconn : CellConnected K)
    [Fintype ↑(((hypercubicLattice 2).induce K).neighborSet (⟨c, hc⟩ : K))]
    (hdeg : ((hypercubicLattice 2).induce K).degree (⟨c, hc⟩ : K) = 1) :
    CellConnected (K \ {c}) := by
  apply cellConnected_diff_of_iso K c hc
  exact hconn.induce_compl_singleton_of_degree_eq_one hdeg












noncomputable def cutWitness : Set (Site 2) := {![0, 0], ![1, 0], ![1, 1], ![2, 1]}

theorem mem_cutWitness (v : Site 2) :
    v ∈ cutWitness ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![1, 1] ∨ v = ![2, 1] := by
  unfold cutWitness; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem cw_v00 : (![0, 0] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto
theorem cw_v10 : (![1, 0] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto
theorem cw_v11 : (![1, 1] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto
theorem cw_v21 : (![2, 1] : Site 2) ∈ cutWitness := by rw [mem_cutWitness]; tauto



theorem cutWitness_cellConnected : CellConnected cutWitness := by
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨![0, 0], cw_v00⟩⟩⟩
  have e1 : ((hypercubicLattice 2).induce cutWitness).Adj ⟨![0, 0], cw_v00⟩ ⟨![1, 0], cw_v10⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have e2 : ((hypercubicLattice 2).induce cutWitness).Adj ⟨![1, 0], cw_v10⟩ ⟨![1, 1], cw_v11⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have e3 : ((hypercubicLattice 2).induce cutWitness).Adj ⟨![1, 1], cw_v11⟩ ⟨![2, 1], cw_v21⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have r0 : ∀ x : ↑cutWitness,
      ((hypercubicLattice 2).induce cutWitness).Reachable ⟨![0, 0], cw_v00⟩ x := by
    rintro ⟨x, hx⟩
    rw [mem_cutWitness] at hx
    rcases hx with h | h | h | h <;> subst h
    · rfl
    · exact e1.reachable
    · exact e1.reachable.trans e2.reachable
    · exact (e1.reachable.trans e2.reachable).trans e3.reachable
  intro a b
  exact (r0 a).symm.trans (r0 b)



theorem cutWitness_extreme : IsExtremeCell cutWitness ![1, 1] := by
  refine ⟨cw_v11, ?_⟩
  intro v hv
  rw [mem_cutWitness] at hv
  unfold lexKey
  rcases hv with h | h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp

theorem mem_cutWitness_diff (v : Site 2) :
    v ∈ cutWitness \ {![1, 1]} ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![2, 1] := by
  rw [Set.mem_diff, mem_cutWitness, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hne⟩
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h hne
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h) <;> subst h <;>
      refine ⟨by tauto, fun hcon => ?_⟩ <;>
      · rw [funext_iff, Fin.forall_fin_two] at hcon; norm_num at hcon

theorem cwd_v21 : (![2, 1] : Site 2) ∈ cutWitness \ {![1, 1]} := by
  rw [mem_cutWitness_diff]; tauto
theorem cwd_v00 : (![0, 0] : Site 2) ∈ cutWitness \ {![1, 1]} := by
  rw [mem_cutWitness_diff]; tauto



theorem cwd_v21_isolated :
    ((hypercubicLattice 2).induce (cutWitness \ {![1, 1]})).neighborSet ⟨![2, 1], cwd_v21⟩ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨w, hw⟩ hadj
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj, hypercubicLattice_adj,
    Fin.sum_univ_two] at hadj
  rw [mem_cutWitness_diff] at hw
  rcases hw with h | h | h <;> subst h <;> simp at hadj

theorem cwd_v21_ne_v00 :
    (⟨![2, 1], cwd_v21⟩ : ↑(cutWitness \ {![1, 1]})) ≠ ⟨![0, 0], cwd_v00⟩ := by
  intro h
  have := congrFun (congrArg Subtype.val h) 0
  norm_num at this








theorem cutWitness_diff_not_cellConnected : ¬ CellConnected (cutWitness \ {![1, 1]}) := by
  intro h
  have hreach := h.preconnected ⟨![2, 1], cwd_v21⟩ ⟨![0, 0], cwd_v00⟩
  exact not_reachable_of_neighborSet_left_eq_empty cwd_v21_ne_v00 cwd_v21_isolated hreach










noncomputable def transSet (w : Site 2) (K : Set (Site 2)) : Set (Site 2) := (· + w) '' K


theorem mem_transSet (w : Site 2) (K : Set (Site 2)) (x : Site 2) :
    x ∈ transSet w K ↔ x - w ∈ K := by
  unfold transSet
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨x - w, h, sub_add_cancel x w⟩


noncomputable def transDart (w : Site 2) (e : Dart) : Dart := mkDart (e.tail + w) e.dir (unitWt_dir e)

@[simp] theorem transDart_tail (w : Site 2) (e : Dart) : (transDart w e).tail = e.tail + w := rfl
@[simp] theorem transDart_dir (w : Site 2) (e : Dart) : (transDart w e).dir = e.dir := by
  rw [transDart, mkDart_dir]
@[simp] theorem transDart_head (w : Site 2) (e : Dart) : (transDart w e).head = e.head + w := by
  rw [transDart, mkDart_head, Dart.dir_def]; abel


theorem transDart_injective (w : Site 2) : Function.Injective (transDart w) := by
  intro a b h
  apply dart_eq_of_tail_dir
  · have := congrArg Dart.tail h; simp only [transDart_tail] at this; exact add_right_cancel this
  · have := congrArg Dart.dir h; simpa only [transDart_dir] using this


theorem transDart_boundary (K : Set (Site 2)) (w : Site 2) (e : Dart)
    (he : IsBoundaryDart K e) : IsBoundaryDart (transSet w K) (transDart w e) := by
  refine ⟨?_, ?_⟩
  · rw [transDart_tail, mem_transSet]; simpa using he.1
  · rw [transDart_head, mem_transSet]; simpa using he.2



theorem turnZ_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) :
    turnZ (transSet w K) (transDart w e) = turnZ K e := by
  classical
  unfold turnZ
  rw [transDart_head, transDart_dir, transDart_tail]
  have m1 : (e.head + w + -rot90Fun e.dir ∈ transSet w K) ↔ (e.head + -rot90Fun e.dir ∈ K) := by
    rw [mem_transSet]; congr! 1; abel
  have m2 : (e.tail + w + -rot90Fun e.dir ∈ transSet w K) ↔ (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [mem_transSet]; congr! 1; abel
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [if_pos (m1.mpr h1), if_pos h1]
  · rw [if_neg (fun hh => h1 (m1.mp hh)), if_neg h1]
    by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [if_pos (m2.mpr h2), if_pos h2]
    · rw [if_neg (fun hh => h2 (m2.mp hh)), if_neg h2]




theorem dartNext_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) :
    dartNext (transSet w K) (transDart w e) = transDart w (dartNext K e) := by
  classical
  have m1 : ((transDart w e).head + -rot90Fun (transDart w e).dir ∈ transSet w K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [transDart_head, transDart_dir, mem_transSet]; congr! 1; abel
  have m2 : ((transDart w e).tail + -rot90Fun (transDart w e).dir ∈ transSet w K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [transDart_tail, transDart_dir, mem_transSet]; congr! 1; abel
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [dartNext_of_front_mem (transSet w K) (transDart w e) (m1.mpr h1),
        dartNext_of_front_mem K e h1]
    apply dart_eq_of_tail_dir
    · simp only [mkDart_tail, transDart_tail, transDart_head, transDart_dir]; abel
    · simp only [mkDart_dir, transDart_dir]
  · by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [dartNext_of_side_mem (transSet w K) (transDart w e) (fun hh => h1 (m1.mp hh)) (m2.mpr h2),
          dartNext_of_side_mem K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, transDart_tail, transDart_dir]; abel
      · simp only [mkDart_dir, transDart_dir]
    · rw [dartNext_of_corner (transSet w K) (transDart w e) (fun hh => h1 (m1.mp hh))
            (fun hh => h2 (m2.mp hh)),
          dartNext_of_corner K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, transDart_tail, transDart_dir]
      · simp only [mkDart_dir, transDart_dir]


theorem iterate_dartNext_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) (k : ℕ) :
    (dartNext (transSet w K))^[k] (transDart w e) = transDart w ((dartNext K)^[k] e) := by
  induction k generalizing e with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dartNext_trans, ih]


theorem rightCornerCount_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) (p : ℕ) :
    rightCornerCount (transSet w K) (transDart w e) p = rightCornerCount K e p := by
  classical
  unfold rightCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [iterate_dartNext_trans, turnZ_trans]


theorem leftCornerCount_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) (p : ℕ) :
    leftCornerCount (transSet w K) (transDart w e) p = leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [iterate_dartNext_trans, turnZ_trans]


noncomputable def transSub (K : Set (Site 2)) (w : Site 2) :
    {e : Dart // IsBoundaryDart K e} → {e : Dart // IsBoundaryDart (transSet w K) e} :=
  fun a => ⟨transDart w a.1, transDart_boundary K w a.1 a.2⟩

@[simp] theorem transSub_val (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) : (transSub K w a).1 = transDart w a.1 := rfl



theorem isPeriodicPt_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (transSet w K)) n (transSub K w a) ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    show ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]
    have hstep : (dartNext (transSet w K))^[n] (transSub K w a).1 =
        transDart w ((dartNext K)^[n] a.1) := by
      show (dartNext (transSet w K))^[n] (transDart w a.1) = _
      rw [iterate_dartNext_trans]
    rw [hstep] at hv
    exact transDart_injective w hv
  · intro h
    apply Subtype.ext
    rw [dartNextSub_iterate_val]
    show (dartNext (transSet w K))^[n] (transDart w a.1) = transDart w a.1
    rw [iterate_dartNext_trans]
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [hv]



theorem dartOrbitPeriod_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod (transSet w K) (transSub K w a) = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact isPeriodicPt_trans K w a n



theorem cornerBalance_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance (transSet w K) (transSub K w a) = cornerBalance K a := by
  unfold cornerBalance
  rw [transSub_val, dartOrbitPeriod_trans, rightCornerCount_trans, leftCornerCount_trans]









noncomputable def ucBase1 : {e : Dart // IsBoundaryDart unitCell e} := ⟨ucDart1, ucDart1_boundary⟩
noncomputable def ucBase2 : {e : Dart // IsBoundaryDart unitCell e} := ⟨ucDart2, ucDart2_boundary⟩
noncomputable def ucBase3 : {e : Dart // IsBoundaryDart unitCell e} := ⟨ucDart3, ucDart3_boundary⟩




theorem it1_1 : (dartNext unitCell)^[1] ucDart1 = ucDart2 := by
  rw [iterate_one]; exact dartNext_ucDart1
theorem it1_2 : (dartNext unitCell)^[2] ucDart1 = ucDart3 := by
  rw [iterate_succ_apply', it1_1, dartNext_ucDart2]
theorem it1_3 : (dartNext unitCell)^[3] ucDart1 = ucDart0 := by
  rw [iterate_succ_apply', it1_2, dartNext_ucDart3]
theorem it1_4 : (dartNext unitCell)^[4] ucDart1 = ucDart1 := by
  rw [iterate_succ_apply', it1_3, dartNext_ucDart0]

theorem it2_1 : (dartNext unitCell)^[1] ucDart2 = ucDart3 := by
  rw [iterate_one]; exact dartNext_ucDart2
theorem it2_2 : (dartNext unitCell)^[2] ucDart2 = ucDart0 := by
  rw [iterate_succ_apply', it2_1, dartNext_ucDart3]
theorem it2_3 : (dartNext unitCell)^[3] ucDart2 = ucDart1 := by
  rw [iterate_succ_apply', it2_2, dartNext_ucDart0]
theorem it2_4 : (dartNext unitCell)^[4] ucDart2 = ucDart2 := by
  rw [iterate_succ_apply', it2_3, dartNext_ucDart1]

theorem it3_1 : (dartNext unitCell)^[1] ucDart3 = ucDart0 := by
  rw [iterate_one]; exact dartNext_ucDart3
theorem it3_2 : (dartNext unitCell)^[2] ucDart3 = ucDart1 := by
  rw [iterate_succ_apply', it3_1, dartNext_ucDart0]
theorem it3_3 : (dartNext unitCell)^[3] ucDart3 = ucDart2 := by
  rw [iterate_succ_apply', it3_2, dartNext_ucDart1]
theorem it3_4 : (dartNext unitCell)^[4] ucDart3 = ucDart3 := by
  rw [iterate_succ_apply', it3_3, dartNext_ucDart2]



theorem ucBase1_period4 : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase1 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext; rw [dartNextSub_iterate_val]; exact it1_4
theorem ucBase1_notfix : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase1 := by
  intro h
  have h2 : dartNext unitCell ucDart1 = ucDart1 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_ucDart1] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart2_dir, ucDart1_dir] at hd
  have := congrFun hd 0; simp at this
theorem ucBase1_notper2 : ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase1 := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart1 = ucDart1 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [it1_2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart3_dir, ucDart1_dir] at hd
  have := congrFun hd 1; simp at this
theorem ucBase1_orbitPeriod : dartOrbitPeriod unitCell ucBase1 = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase1 ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase1_period4
  have hper := Function.isPeriodicPt_minimalPeriod (dartNextSub unitCell) ucBase1
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase1 with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd; interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper; rw [Function.IsPeriodicPt, iterate_one] at hper; exact absurd hper ucBase1_notfix
  · rw [h] at hper; exact absurd hper ucBase1_notper2
  · exact h

theorem ucBase2_period4 : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase2 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext; rw [dartNextSub_iterate_val]; exact it2_4
theorem ucBase2_notfix : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase2 := by
  intro h
  have h2 : dartNext unitCell ucDart2 = ucDart2 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_ucDart2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart3_dir, ucDart2_dir] at hd
  have := congrFun hd 0; simp at this
theorem ucBase2_notper2 : ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase2 := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart2 = ucDart2 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [it2_2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart0_dir, ucDart2_dir] at hd
  have := congrFun hd 0; simp at this
theorem ucBase2_orbitPeriod : dartOrbitPeriod unitCell ucBase2 = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase2 ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase2_period4
  have hper := Function.isPeriodicPt_minimalPeriod (dartNextSub unitCell) ucBase2
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase2 with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd; interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper; rw [Function.IsPeriodicPt, iterate_one] at hper; exact absurd hper ucBase2_notfix
  · rw [h] at hper; exact absurd hper ucBase2_notper2
  · exact h

theorem ucBase3_period4 : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase3 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext; rw [dartNextSub_iterate_val]; exact it3_4
theorem ucBase3_notfix : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase3 := by
  intro h
  have h2 : dartNext unitCell ucDart3 = ucDart3 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_ucDart3] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart0_dir, ucDart3_dir] at hd
  have := congrFun hd 0; simp at this
theorem ucBase3_notper2 : ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase3 := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart3 = ucDart3 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [it3_2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart1_dir, ucDart3_dir] at hd
  have := congrFun hd 1; simp at this
theorem ucBase3_orbitPeriod : dartOrbitPeriod unitCell ucBase3 = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase3 ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase3_period4
  have hper := Function.isPeriodicPt_minimalPeriod (dartNextSub unitCell) ucBase3
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase3 with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd; interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper; rw [Function.IsPeriodicPt, iterate_one] at hper; exact absurd hper ucBase3_notfix
  · rw [h] at hper; exact absurd hper ucBase3_notper2
  · exact h



theorem ucBase1_totalTurnZ : totalTurnZ unitCell ucDart1 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart1_turnZ
  · rw [dartNext_ucDart1]; exact ucDart2_turnZ
  · rw [it1_2]; exact ucDart3_turnZ
  · rw [it1_3]; exact ucDart0_turnZ
theorem ucBase2_totalTurnZ : totalTurnZ unitCell ucDart2 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart2_turnZ
  · rw [dartNext_ucDart2]; exact ucDart3_turnZ
  · rw [it2_2]; exact ucDart0_turnZ
  · rw [it2_3]; exact ucDart1_turnZ
theorem ucBase3_totalTurnZ : totalTurnZ unitCell ucDart3 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart3_turnZ
  · rw [dartNext_ucDart3]; exact ucDart0_turnZ
  · rw [it3_2]; exact ucDart1_turnZ
  · rw [it3_3]; exact ucDart2_turnZ



theorem unitCell_cornerBalance (a : {e : Dart // IsBoundaryDart unitCell e})
    (ha : a.1 = ucDart0 ∨ a.1 = ucDart1 ∨ a.1 = ucDart2 ∨ a.1 = ucDart3) :
    cornerBalance unitCell a = -4 := by
  rw [cornerBalance_eq_totalTurnZ]
  rcases ha with h | h | h | h
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase := Subtype.ext h
      rw [hb]; exact unitCell_orbitPeriod_eq_four
    rw [this]; exact unitCell_totalTurnZ_four
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase1 := Subtype.ext h
      rw [hb]; exact ucBase1_orbitPeriod
    rw [this]; exact ucBase1_totalTurnZ
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase2 := Subtype.ext h
      rw [hb]; exact ucBase2_orbitPeriod
    rw [this]; exact ucBase2_totalTurnZ
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase3 := Subtype.ext h
      rw [hb]; exact ucBase3_orbitPeriod
    rw [this]; exact ucBase3_totalTurnZ


theorem transSet_unitCell (v : Site 2) : transSet v unitCell = {v} := by
  unfold transSet unitCell
  rw [Set.image_singleton]
  congr 1
  funext i; fin_cases i <;> simp


theorem singleton_boundaryDart_tail (v : Site 2) (e : Dart)
    (he : IsBoundaryDart ({v} : Set (Site 2)) e) : e.tail = v := he.1


theorem singleton_boundaryDart_dir (v : Site 2) (e : Dart)
    (_he : IsBoundaryDart ({v} : Set (Site 2)) e) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
  have hadj := e.adj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have key : ((e.dir 0).natAbs = 1 ∧ (e.dir 1).natAbs = 0) ∨
             ((e.dir 0).natAbs = 0 ∧ (e.dir 1).natAbs = 1) := by
    have hd : e.dir = e.head - e.tail := rfl
    rw [hd]; simp only [Pi.sub_apply]; omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases Int.natAbs_eq_iff.mp h0 with h | h
    · left; funext i; fin_cases i <;> simp_all [Dart.dir]
    · right; left; funext i; fin_cases i <;> simp_all [Dart.dir]
  · rcases Int.natAbs_eq_iff.mp h1 with h | h
    · right; right; left; funext i; fin_cases i <;> simp_all [Dart.dir]
    · right; right; right; funext i; fin_cases i <;> simp_all [Dart.dir]



theorem singleton_boundaryDart_eq_transDart (v : Site 2) (e : Dart)
    (he : IsBoundaryDart ({v} : Set (Site 2)) e) :
    (e = transDart v ucDart0 ∧ e.dir = ![1, 0]) ∨
    (e = transDart v ucDart2 ∧ e.dir = ![-1, 0]) ∨
    (e = transDart v ucDart3 ∧ e.dir = ![0, 1]) ∨
    (e = transDart v ucDart1 ∧ e.dir = ![0, -1]) := by
  have htail : e.tail = v := he.1
  rcases singleton_boundaryDart_dir v e he with h | h | h | h
  · left; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart0_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart0_dir]
  · right; left; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart2_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart2_dir]
  · right; right; left; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart3_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart3_dir]
  · right; right; right; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart1_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart1_dir]




theorem cornerBalance_congr (K K' : Set (Site 2)) (hKK : K = K')
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart K' e})
    (ha : a.1 = a'.1) : cornerBalance K a = cornerBalance K' a' := by
  subst hKK
  rw [Subtype.ext ha]




theorem singleton_cornerBalance_reduce (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e})
    (b : {e : Dart // IsBoundaryDart unitCell e}) (he : a.1 = transDart v b.1) :
    cornerBalance ({v} : Set (Site 2)) a = cornerBalance unitCell b := by
  have hset : ({v} : Set (Site 2)) = transSet v unitCell := (transSet_unitCell v).symm
  have hstep : cornerBalance ({v} : Set (Site 2)) a
      = cornerBalance (transSet v unitCell) (transSub unitCell v b) := by
    apply cornerBalance_congr ({v} : Set (Site 2)) (transSet v unitCell) hset
    rw [he, transSub_val]
  rw [hstep, cornerBalance_trans]





theorem singleton_cornerBalance (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    cornerBalance ({v} : Set (Site 2)) a = -4 := by
  rcases singleton_boundaryDart_eq_transDart v a.1 a.2 with
    ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · rw [singleton_cornerBalance_reduce v a ucBase he]
    exact unitCell_cornerBalance ucBase (Or.inl rfl)
  · rw [singleton_cornerBalance_reduce v a ucBase2 he]
    exact unitCell_cornerBalance ucBase2 (Or.inr (Or.inr (Or.inl rfl)))
  · rw [singleton_cornerBalance_reduce v a ucBase3 he]
    exact unitCell_cornerBalance ucBase3 (Or.inr (Or.inr (Or.inr rfl)))
  · rw [singleton_cornerBalance_reduce v a ucBase1 he]
    exact unitCell_cornerBalance ucBase1 (Or.inr (Or.inl rfl))











def BalanceIsFour (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  cornerBalance K a = 4 ∨ cornerBalance K a = -4


theorem balanceIsFour_iff_simplePolygon (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    BalanceIsFour K a ↔ SimplePolygonCornerBalance K a :=
  (simplePolygonCornerBalance_iff_cornerBalance K a).symm



theorem singleton_balanceIsFour (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    BalanceIsFour ({v} : Set (Site 2)) a :=
  Or.inr (singleton_cornerBalance v a)











def BalancePreservingContraction : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a






theorem balanceIsFour_of_contraction (hcontr : BalancePreservingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : BalanceIsFour K a := by
  generalize hn : K.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n IH =>
    subst hn
    rcases Nat.lt_or_ge K.ncard 2 with hlt | hge
    · 
      have h1 : K.ncard = 1 := by
        have hpos : 0 < K.ncard := (Set.ncard_pos hK).mpr hne
        omega
      obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp h1
      subst hv
      exact singleton_balanceIsFour v a
    · 
      obtain ⟨K', hK', hne', a', hlt, hbal⟩ := hcontr K hK hge a
      have hIH := IH K'.ncard hlt K' hK' hne' a' rfl
      unfold BalanceIsFour at hIH ⊢
      rw [← hbal]; exact hIH






theorem simplePolygonCornerBalance_of_contraction (hcontr : BalancePreservingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : SimplePolygonCornerBalance K a :=
  (balanceIsFour_iff_simplePolygon K a).mp (balanceIsFour_of_contraction hcontr K hK hne a)




theorem turningIsFullRevolution_of_contraction (hcontr : BalancePreservingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_simplePolygon K a
    (simplePolygonCornerBalance_of_contraction hcontr K hK hne a)





theorem unitCell_balanceIsFour : BalanceIsFour unitCell ucBase :=
  Or.inr (unitCell_cornerBalance ucBase (Or.inl rfl))




























end Lattice

end StatMech
