/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationWalkTransition
import Code.Onsager.TorusLoopHomology









namespace StatMech.Onsager

open BigOperators

def ons_decCycleDartList {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) : List (ons_Dart L) :=
  (ons_decCycleFirstReturn q).dropLast

def ons_decCycleDartLoop {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    Fin (ons_decCycleDartList q).length → ons_Dart L :=
  (ons_decCycleDartList q).get

instance ons_decCycleDartList_neZero {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    NeZero (ons_decCycleDartList q).length := by
  refine ⟨?_⟩
  simp [ons_decCycleDartList, ons_decCycleFirstReturn]

theorem ons_decCycleDartList_ofFn {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    List.ofFn (ons_decCycleDartLoop q) = ons_decCycleDartList q :=
  List.ofFn_get _

theorem ons_decCycleDartList_eq
    {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ons_decCycleDartList q =
      d :: (ons_decWalkExternalDarts q).tail.reverse := by
  unfold ons_decCycleDartList ons_decCycleFirstReturn
  exact List.dropLast_concat

theorem ons_decCycleDartLoop_zero
    {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ons_decCycleDartLoop q 0 = d := by
  simp [ons_decCycleDartLoop, ons_decCycleDartList_eq]



theorem ons_decCycleDartLoop_valid
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∀ k : Fin (ons_decCycleDartList q).length,
      (ons_decCycleDartLoop q k).1 =
        ons_dirStep L (ons_decCycleDartLoop q (k + 1)).2
          (ons_decCycleDartLoop q (k + 1)).1 := by
  apply ons_isChain_closed_ofFn
    (R := fun e f : ons_Dart L =>
      e.1 = ons_dirStep L f.2 f.1)
    (ons_decCycleDartLoop q)
  rw [ons_decCycleDartList_ofFn, ons_decCycleDartLoop_zero]
  rw [ons_decCycleDartList_eq]
  simpa only [List.cons_append] using
    ons_decCycleFirstReturn_isChain_KW q hq hsnd


theorem ons_decCycleDartLoop_portEdge_injective
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    Function.Injective
      (fun k : Fin (ons_decCycleDartList q).length =>
        ons_portEdge L (ons_decCycleDartLoop q k)) := by
  let ext := ons_decWalkExternalDarts q
  let base := ons_decCycleDartList q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hbase : base = d :: ext.tail.reverse := by
    exact ons_decCycleDartList_eq q
  have hextNodup := ons_decWalkExternalDarts_portEdge_nodup q hq
  change (ext.map (ons_portEdge L)).Nodup at hextNodup
  rw [hext, List.map_cons, List.nodup_cons] at hextNodup
  have hbaseNodup :
      (base.map (ons_portEdge L)).Nodup := by
    rw [hbase, List.map_cons, List.nodup_cons,
      List.map_reverse, List.mem_reverse]
    exact ⟨hextNodup.1, List.nodup_reverse.mpr hextNodup.2⟩
  intro i j hij
  change ons_portEdge L (base.get i) =
    ons_portEdge L (base.get j) at hij
  have hinjOn := List.inj_on_of_nodup_map hbaseNodup
  have hget : base.get i = base.get j :=
    hinjOn (List.get_mem base i) (List.get_mem base j) hij
  exact (List.nodup_iff_injective_get.mp
    (hbaseNodup.of_map (ons_portEdge L))) hget



theorem ons_decCycleDartLoop_edgeSet
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_dartEdgeSet (ons_decCycleDartLoop q) =
      ons_walkOriginalEdges q := by
  classical
  let ext := ons_decWalkExternalDarts q
  let base := ons_decCycleDartList q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hbase : base = d :: ext.tail.reverse :=
    ons_decCycleDartList_eq q
  have hbaseExt : ∀ e, e ∈ base ↔ e ∈ ext := by
    intro e
    rw [hbase, hext]
    simp
  rw [← ons_decWalkExternalDarts_image_portEdge q]
  ext edge
  simp only [ons_dartEdgeSet, Finset.mem_image, Finset.mem_univ,
    true_and, List.mem_toFinset]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨base.get k, ?_, rfl⟩
    exact (hbaseExt _).mp (List.get_mem base k)
  · rintro ⟨e, he, rfl⟩
    have heBase : e ∈ base := by
      change e ∈ ext at he
      exact (hbaseExt e).mpr he
    obtain ⟨k, hk⟩ := List.get_of_mem heBase
    refine ⟨k, ?_⟩
    simpa [ons_decCycleDartLoop, base] using congrArg (ons_portEdge L) hk




theorem ons_dartEdgeSet_xSeam_card_of_portEdge_injective
    {L n : ℕ} [Fact (2 < L)]
    (d : Fin n → ons_Dart L)
    (hinj : Function.Injective (fun k => ons_portEdge L (d k))) :
    ((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card =
      (Finset.univ.filter (fun k => ons_xWrap (d k))).card := by
  rw [ons_dartEdgeSet_filter_x]
  exact Finset.card_image_iff.mpr hinj.injOn

theorem ons_dartEdgeSet_ySeam_card_of_portEdge_injective
    {L n : ℕ} [Fact (2 < L)]
    (d : Fin n → ons_Dart L)
    (hinj : Function.Injective (fun k => ons_portEdge L (d k))) :
    ((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card =
      (Finset.univ.filter (fun k => ons_yWrap (d k))).card := by
  rw [ons_dartEdgeSet_filter_y]
  exact Finset.card_image_iff.mpr hinj.injOn



theorem ons_evenHomology_dartEdgeSet_eq_windingParity_of_portEdge_injective
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hinj : Function.Injective (fun k => ons_portEdge L (d k)))
    (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my) :
    ons_evenHomology L (ons_dartEdgeSet d) =
      ons_windingParity mx my := by
  have hL : (L : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
      (Fact.out : 2 < L)))
  have hxwrap := ons_sum_dirExponentX_eq_wrap d hvalid
  have hywrap := ons_sum_dirExponentY_eq_wrap d hvalid
  have hx : mx = ∑ k, ons_xWrapSign (d k) := by
    apply mul_left_cancel₀ hL
    exact hmx.symm.trans hxwrap
  have hy : my = ∑ k, ons_yWrapSign (d k) := by
    apply mul_left_cancel₀ hL
    exact hmy.symm.trans hywrap
  apply Prod.ext
  · change
      ⟨((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card % 2,
          Nat.mod_lt _ (by decide)⟩ = ons_intParity mx
    rw [ons_dartEdgeSet_xSeam_card_of_portEdge_injective d hinj, hx]
    exact (ons_intParity_sum_xWrapSign d).symm
  · change
      ⟨((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card % 2,
          Nat.mod_lt _ (by decide)⟩ = ons_intParity my
    rw [ons_dartEdgeSet_ySeam_card_of_portEdge_injective d hinj, hy]
    exact (ons_intParity_sum_yWrapSign d).symm



theorem ons_decCycle_spinPhase_product_eq_homology
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) (a b : Fin 2) :
    (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b)
      (ons_decCycleDartLoop q k).2) =
      ons_spinLinearCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges q)) := by
  let loop := ons_decCycleDartLoop q
  have hvalid := ons_decCycleDartLoop_valid q hq hsnd
  have hinj := ons_decCycleDartLoop_portEdge_injective q hq hsnd
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists loop hvalid
  rw [prod_ons_dirPhase _ _ (ons_spinPhase_ne_zero L a)
    (ons_spinPhase_ne_zero L b) (fun k => (loop k).2), hmx, hmy]
  have ha : ons_spinPhase L a ^ (L : ℤ) =
      (-1 : ℂ) ^ (a.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hb : ons_spinPhase L b ^ (L : ℤ) =
      (-1 : ℂ) ^ (b.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  rw [_root_.zpow_mul, _root_.zpow_mul, ha, hb,
    ← _root_.zpow_mul, ← _root_.zpow_mul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    ons_spinPhase_character]
  have hhom :=
    ons_evenHomology_dartEdgeSet_eq_windingParity_of_portEdge_injective
      loop hvalid hinj mx my hmx hmy
  rw [ons_decCycleDartLoop_edgeSet q hq hsnd] at hhom
  rw [hhom]

end StatMech.Onsager
