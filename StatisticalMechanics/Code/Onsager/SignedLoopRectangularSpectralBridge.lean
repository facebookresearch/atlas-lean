/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopRectangularEmbedding
import Code.Onsager.KWRectangleWeighted
import Code.FrontierA.KacWardRectilinearPolygonBridge
import Code.FrontierA.TriangularIsingTorusCycleTopology





open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section



def ons_rectDualDartDirection4 {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) : Fin 4 :=
  if dart.snd.1.val < dart.fst.1.val then 2
  else if dart.fst.1.val < dart.snd.1.val then 0
  else if dart.snd.2.val < dart.fst.2.val then 3 else 1



theorem ons_rectDual_dartVector_eq_kwRectilinearVector {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualComplexPoint dart.snd - ons_rectDualComplexPoint dart.fst =
      kwRectilinearVector (ons_rectDualDartDirection4 dart) := by
  unfold ons_rectDualComplexPoint
  rw [ons_rectDualIntPoint_snd_eq_add_step,
    triangularIntPoint_add_sub]
  by_cases hxneg : dart.snd.1.val < dart.fst.1.val
  · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
      triangularIntStep, triangularIntPoint]
  · by_cases hxpos : dart.fst.1.val < dart.snd.1.val
    · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
        hxpos, triangularIntStep, triangularIntPoint]
    · by_cases hyneg : dart.snd.2.val < dart.fst.2.val
      · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
          hxpos, hyneg, triangularIntStep, triangularIntPoint,
          kwRectilinearVector, StatMech.Onsager.BaseCase.stepOf]
      · simp [ons_rectDualDartDirection4, ons_rectDualDartDirection, hxneg,
          hxpos, hyneg, triangularIntStep, triangularIntPoint,
          kwRectilinearVector, StatMech.Onsager.BaseCase.stepOf]



theorem ons_rectDualDartDirection4_ne_opposite {M N : Nat}
    (dart next : (ons_rectDualGraph M N).Dart)
    (hadj : (ons_rectDualGraph M N).DartAdj dart next)
    (hedge : dart.edge ≠ next.edge) :
    ons_rectDualDartDirection4 next ≠ ons_rectDualDartDirection4 dart + 2 := by
  intro hdir
  have hvec := ons_rectDual_dartVector_eq_kwRectilinearVector dart
  have hvec' := ons_rectDual_dartVector_eq_kwRectilinearVector next
  rw [hdir] at hvec'
  have hopposite :
      kwRectilinearVector (ons_rectDualDartDirection4 dart + 2) =
        -kwRectilinearVector (ons_rectDualDartDirection4 dart) := by
    generalize ons_rectDualDartDirection4 dart = direction
    fin_cases direction <;> simp
  rw [hopposite] at hvec'
  have hsnd : dart.snd = next.fst := hadj
  have hend : next.snd = dart.fst := by
    apply ons_rectDualComplexPoint_injective
    rw [← sub_eq_zero]
    calc
      ons_rectDualComplexPoint next.snd - ons_rectDualComplexPoint dart.fst =
          (ons_rectDualComplexPoint next.snd -
              ons_rectDualComplexPoint next.fst) +
            (ons_rectDualComplexPoint dart.snd -
              ons_rectDualComplexPoint dart.fst) := by rw [← hsnd]; ring
      _ = 0 := by rw [hvec', hvec]; ring
  apply hedge
  change s(dart.fst, dart.snd) = s(next.fst, next.snd)
  rw [Sym2.eq_iff]
  exact Or.inr ⟨hend.symm, hsnd⟩

theorem ons_rectDualDartDirection4_symm {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualDartDirection4 dart.symm =
      ons_rectDualDartDirection4 dart + 2 := by
  by_cases hleft : dart.snd.1.val < dart.fst.1.val
  · have hnotright : ¬dart.fst.1.val < dart.snd.1.val :=
      not_lt_of_ge hleft.le
    simp [ons_rectDualDartDirection4, hleft, hnotright]
  · by_cases hright : dart.fst.1.val < dart.snd.1.val
    · have hnotleft : ¬dart.snd.1.val < dart.fst.1.val :=
        not_lt_of_ge hright.le
      simp [ons_rectDualDartDirection4, hright, hnotleft]
    · have hx : dart.fst.1.val = dart.snd.1.val :=
        Nat.le_antisymm (Nat.le_of_not_gt hleft) (Nat.le_of_not_gt hright)
      have hyne : dart.fst.2.val ≠ dart.snd.2.val := by
        intro hy
        apply dart.fst_ne_snd
        apply Prod.ext <;> apply Fin.ext
        · exact hx
        · exact hy
      by_cases hdown : dart.snd.2.val < dart.fst.2.val
      · have hnotup : ¬dart.fst.2.val < dart.snd.2.val :=
          not_lt_of_ge hdown.le
        simp [ons_rectDualDartDirection4, hleft, hright, hdown, hnotup]
      · have hup : dart.fst.2.val < dart.snd.2.val :=
          lt_of_le_of_ne (Nat.le_of_not_gt hdown) hyne
        simp [ons_rectDualDartDirection4, hleft, hright, hdown, hup]




theorem ons_rectDual_turnPhase_eq_turnW {M N : Nat}
    (dart next : (ons_rectDualGraph M N).Dart)
    (hadj : (ons_rectDualGraph M N).DartAdj dart next)
    (hedge : dart.edge ≠ next.edge) :
    (ons_rectDualStraightLineEmbedding M N).turnPhase dart next =
      ons_turnW ons_turnRoot (ons_rectDualDartDirection4 dart)
        (ons_rectDualDartDirection4 next) := by
  rw [← (ons_rectDualStraightLineEmbedding M N).vectorTurnPhase_eq_turnPhase]
  change kwVectorTurnPhase
      (ons_rectDualComplexPoint dart.snd - ons_rectDualComplexPoint dart.fst)
      (ons_rectDualComplexPoint next.snd - ons_rectDualComplexPoint next.fst) = _
  rw [ons_rectDual_dartVector_eq_kwRectilinearVector,
    ons_rectDual_dartVector_eq_kwRectilinearVector]
  exact kwVectorTurnPhase_rectilinear _ _
    (ons_rectDualDartDirection4_ne_opposite dart next hadj hedge)



def ons_rectDualVertexSlot {M N : Nat}
    (vertex : ons_RectDualVertex M N) : ons_RectVertex M N :=
  ((vertex.1.val : ZMod (M + 1)), (vertex.2.val : ZMod (N + 1)))

@[simp] theorem ons_rectDualVertexSlot_fst_val {M N : Nat}
    (vertex : ons_RectDualVertex M N) :
    (ons_rectDualVertexSlot vertex).1.val = vertex.1.val := by
  simp [ons_rectDualVertexSlot, ZMod.val_natCast,
    Nat.mod_eq_of_lt vertex.1.isLt]

@[simp] theorem ons_rectDualVertexSlot_snd_val {M N : Nat}
    (vertex : ons_RectDualVertex M N) :
    (ons_rectDualVertexSlot vertex).2.val = vertex.2.val := by
  simp [ons_rectDualVertexSlot, ZMod.val_natCast,
    Nat.mod_eq_of_lt vertex.2.isLt]

theorem ons_rectDualVertexSlot_injective {M N : Nat} :
    Function.Injective
      (ons_rectDualVertexSlot : ons_RectDualVertex M N → ons_RectVertex M N) := by
  intro u v h
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg (fun p : ons_RectVertex M N ↦ p.1.val) h
    simpa using hx
  · have hy := congrArg (fun p : ons_RectVertex M N ↦ p.2.val) h
    simpa using hy



def ons_rectDualDartSlot {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) : ons_RectDart M N :=
  (ons_rectDualVertexSlot dart.fst, ons_rectDualDartDirection4 dart)

theorem ons_rectDualDartSlot_valid {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDartValid M N (ons_rectDualDartSlot dart) := by
  have hadj : ons_rectDualAdj M N dart.fst dart.snd := dart.adj
  rcases hadj with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · have hne : dart.fst.1.val ≠ dart.snd.1.val := by
      intro h
      simp [h] at hx
    by_cases hleft : dart.snd.1.val < dart.fst.1.val
    · have hpos : 0 < dart.fst.1.val :=
        lt_of_le_of_lt (Nat.zero_le _) hleft
      simpa [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hleft] using hpos
    · have hright : dart.fst.1.val < dart.snd.1.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hleft) hne
      have hhead : dart.snd.1.val < M + 1 := dart.snd.1.isLt
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hleft, hright]
      rw [Nat.dist_eq_sub_of_le hright.le] at hx
      omega
  · have hxval : dart.fst.1.val = dart.snd.1.val :=
      congrArg Fin.val hx
    have hne : dart.fst.2.val ≠ dart.snd.2.val := by
      intro h
      simp [h] at hy
    have hnotleft : ¬dart.snd.1.val < dart.fst.1.val := by omega
    have hnotright : ¬dart.fst.1.val < dart.snd.1.val := by omega
    by_cases hdown : dart.snd.2.val < dart.fst.2.val
    · have hpos : 0 < dart.fst.2.val :=
        lt_of_le_of_lt (Nat.zero_le _) hdown
      simpa [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hnotleft, hnotright, hdown] using hpos
    · have hup : dart.fst.2.val < dart.snd.2.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hdown) hne
      have hhead : dart.snd.2.val < N + 1 := dart.snd.2.isLt
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hnotleft, hnotright,
        hdown]
      rw [Nat.dist_eq_sub_of_le hup.le] at hy
      omega

theorem ons_rectDualDartSlot_injective {M N : Nat} :
    Function.Injective
      (ons_rectDualDartSlot :
        (ons_rectDualGraph M N).Dart → ons_RectDart M N) := by
  intro dart next hslot
  have htailSlot := congrArg (fun slot : ons_RectDart M N ↦ slot.1) hslot
  have hdir := congrArg (fun slot : ons_RectDart M N ↦ slot.2) hslot
  have htail : dart.fst = next.fst :=
    ons_rectDualVertexSlot_injective (by
      simpa [ons_rectDualDartSlot] using htailSlot)
  have hdir' : ons_rectDualDartDirection4 dart =
      ons_rectDualDartDirection4 next := by
    simpa [ons_rectDualDartSlot] using hdir
  have hvec := ons_rectDual_dartVector_eq_kwRectilinearVector dart
  have hvec' := ons_rectDual_dartVector_eq_kwRectilinearVector next
  have hhead : dart.snd = next.snd := by
    apply ons_rectDualComplexPoint_injective
    rw [← sub_eq_zero]
    calc
      ons_rectDualComplexPoint dart.snd - ons_rectDualComplexPoint next.snd =
          (ons_rectDualComplexPoint dart.snd -
              ons_rectDualComplexPoint dart.fst) -
            (ons_rectDualComplexPoint next.snd -
              ons_rectDualComplexPoint next.fst) := by rw [htail]; ring
      _ = 0 := by rw [hvec, hvec', hdir']; ring
  apply SimpleGraph.Dart.ext
  exact Prod.ext htail hhead

theorem ons_rectDualDartSlot_surjective_valid {M N : Nat}
    (slot : ons_RectDart M N) (hslot : ons_rectDartValid M N slot) :
    ∃ dart : (ons_rectDualGraph M N).Dart,
      ons_rectDualDartSlot dart = slot := by
  rcases slot with ⟨⟨x, y⟩, direction⟩
  fin_cases direction
  · simp [ons_rectDartValid] at hslot
    have hxlt : x.val < M + 1 := ZMod.val_lt x
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val + 1, by omega⟩, ⟨y.val, ZMod.val_lt y⟩)
    have hadj : ons_rectDualAdj M N u v := by
      left
      refine ⟨rfl, ?_⟩
      simp [u, v, Nat.dist_eq_sub_of_le]
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v]
  · simp [ons_rectDartValid] at hslot
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val + 1, by omega⟩)
    have hadj : ons_rectDualAdj M N u v := by
      right
      refine ⟨rfl, ?_⟩
      simp [u, v, Nat.dist_eq_sub_of_le]
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v]
  · simp [ons_rectDartValid] at hslot
    have hxlt : x.val < M + 1 := ZMod.val_lt x
    have hxpos : 0 < x.val := by
      exact Nat.pos_of_ne_zero (fun h ↦ hslot ((ZMod.val_eq_zero x).mp h))
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val - 1, by omega⟩, ⟨y.val, ZMod.val_lt y⟩)
    have hadj : ons_rectDualAdj M N u v := by
      left
      refine ⟨rfl, ?_⟩
      change Nat.dist x.val (x.val - 1) = 1
      rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (Nat.sub_le _ _)]
      omega
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · have hlt : x.val - 1 < x.val := by omega
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v,
        hlt]
  · simp [ons_rectDartValid] at hslot
    have hylt : y.val < N + 1 := ZMod.val_lt y
    have hypos : 0 < y.val := by
      exact Nat.pos_of_ne_zero (fun h ↦ hslot ((ZMod.val_eq_zero y).mp h))
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val - 1, by omega⟩)
    have hadj : ons_rectDualAdj M N u v := by
      right
      refine ⟨rfl, ?_⟩
      change Nat.dist y.val (y.val - 1) = 1
      rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (Nat.sub_le _ _)]
      omega
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · have hlt : y.val - 1 < y.val := by omega
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v,
        hlt]


def ons_rectDualDartEquivValid (M N : Nat) :
    (ons_rectDualGraph M N).Dart ≃
      {slot : ons_RectDart M N // ons_rectDartValid M N slot} :=
  Equiv.ofBijective
    (fun dart ↦ ⟨ons_rectDualDartSlot dart,
      ons_rectDualDartSlot_valid dart⟩)
    ⟨fun _ _ h ↦ ons_rectDualDartSlot_injective (congrArg Subtype.val h),
      fun slot ↦ by
        obtain ⟨dart, hdart⟩ :=
          ons_rectDualDartSlot_surjective_valid slot.1 slot.2
        exact ⟨dart, Subtype.ext hdart⟩⟩



def ons_rectDualDartSumEquiv (M N : Nat) :
    (ons_rectDualGraph M N).Dart ⊕
        {slot : ons_RectDart M N // ¬ons_rectDartValid M N slot} ≃
      ons_RectDart M N :=
  (Equiv.sumCongr (ons_rectDualDartEquivValid M N) (Equiv.refl _)).trans
    (Equiv.sumCompl (ons_rectDartValid M N))



noncomputable def ons_rectDualSlotWeight (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (slot : ons_RectDart M N) : Complex :=
  if hslot : ons_rectDartValid M N slot then
    edgeWeight ((ons_rectDualDartEquivValid M N).symm ⟨slot, hslot⟩).edge
  else 0

@[simp] theorem ons_rectDualSlotWeight_dartSlot (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualSlotWeight M N edgeWeight (ons_rectDualDartSlot dart) =
      edgeWeight dart.edge := by
  rw [ons_rectDualSlotWeight, dif_pos (ons_rectDualDartSlot_valid dart)]
  congr 1
  exact congrArg SimpleGraph.Dart.edge
    ((ons_rectDualDartEquivValid M N).symm_apply_apply dart)

theorem norm_ons_rectDualSlotWeight_le (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (q : Real) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q)
    (slot : ons_RectDart M N) :
    ‖ons_rectDualSlotWeight M N edgeWeight slot‖ ≤ q := by
  unfold ons_rectDualSlotWeight
  split_ifs with hslot
  · exact hweight _
  · simpa using hq



theorem ons_rectDualVertexSlot_snd_eq_rectDirStep {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualVertexSlot dart.snd =
      ons_rectDirStep M N (ons_rectDualDartDirection4 dart)
        (ons_rectDualVertexSlot dart.fst) := by
  have hadj : ons_rectDualAdj M N dart.fst dart.snd := dart.adj
  rcases hadj with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · have hne : dart.fst.1.val ≠ dart.snd.1.val := by
      intro h
      simp [h] at hx
    by_cases hleft : dart.snd.1.val < dart.fst.1.val
    · have hval : dart.fst.1.val = dart.snd.1.val + 1 := by
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hleft)] at hx
        omega
      apply Prod.ext
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hleft]
        rw [hval]
        simp
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hleft, hy]
    · have hright : dart.fst.1.val < dart.snd.1.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hleft) hne
      have hval : dart.snd.1.val = dart.fst.1.val + 1 := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hright)] at hx
        omega
      apply Prod.ext
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hleft, hright]
        rw [hval]
        push_cast
        rfl
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hleft, hright, hy]
  · have hxval : dart.fst.1.val = dart.snd.1.val :=
      congrArg Fin.val hx
    have hne : dart.fst.2.val ≠ dart.snd.2.val := by
      intro h
      simp [h] at hy
    have hnotleft : ¬dart.snd.1.val < dart.fst.1.val := by omega
    have hnotright : ¬dart.fst.1.val < dart.snd.1.val := by omega
    by_cases hdown : dart.snd.2.val < dart.fst.2.val
    · have hval : dart.fst.2.val = dart.snd.2.val + 1 := by
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hdown)] at hy
        omega
      apply Prod.ext
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hdown, hxval]
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hnotleft, hnotright, hdown]
        rw [hval]
        push_cast
        ring
    · have hup : dart.fst.2.val < dart.snd.2.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hdown) hne
      have hval : dart.snd.2.val = dart.fst.2.val + 1 := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hup)] at hy
        omega
      apply Prod.ext
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hdown, hxval]
      · simp [ons_rectDualVertexSlot, ons_rectDualDartDirection4,
          ons_rectDirStep, hnotleft, hnotright, hdown]
        rw [hval]
        push_cast
        rfl



theorem ons_rectKWmatDartWeighted_apply_of_valid
    (M N : Nat) (weight : ons_RectDart M N → Complex)
    (next dart : ons_RectDart M N)
    (hnext : ons_rectDartValid M N next)
    (hdart : ons_rectDartValid M N dart) :
    ons_rectKWmatDartWeighted M N weight next dart =
      if next.1 = ons_rectDirStep M N dart.2 dart.1 then
        ons_turnW ons_turnRoot dart.2 next.2 * weight dart
      else 0 := by
  classical
  unfold ons_rectKWmatDartWeighted
  rw [Matrix.mul_diagonal]
  unfold ons_rectDartMask
  rw [Matrix.mul_diagonal]
  simp only [hdart, if_true, mul_one]
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (ons_rectHeadDartEquiv M N dart)]
  · have htailhead :
        ons_rectTailDartEquiv M N (ons_rectHeadDartEquiv M N dart) =
          dart := (ons_rectHeadDartEquiv M N).symm_apply_apply dart
    rw [show ((ons_rectTailDartEquiv M N).permMatrix Complex)
        (ons_rectHeadDartEquiv M N dart) dart = 1 by
      simp [Equiv.Perm.permMatrix, htailhead]]
    rw [mul_one, Matrix.diagonal_mul]
    simp [hnext, ons_arrivalTurnMatrixOf, ons_turnMatrix,
      ons_rectHeadDartEquiv]
  · intro slot _ hslot
    by_cases htail : ons_rectTailDartEquiv M N slot = dart
    · have : slot = ons_rectHeadDartEquiv M N dart := by
        simpa [ons_rectTailDartEquiv] using
          congrArg (ons_rectHeadDartEquiv M N) htail
      exact (hslot this).elim
    · have hconcrete :
          (ons_rectDirStep M N (slot.2 + 2) slot.1, slot.2) ≠ dart := by
        simpa [ons_rectTailDartEquiv_apply] using htail
      simp [Equiv.Perm.permMatrix, hconcrete]
  · simp

theorem ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_right
    (M N : Nat) (weight : ons_RectDart M N → Complex)
    (next dart : ons_RectDart M N)
    (hdart : ¬ons_rectDartValid M N dart) :
    ons_rectKWmatDartWeighted M N weight next dart = 0 := by
  unfold ons_rectKWmatDartWeighted
  rw [Matrix.mul_diagonal]
  unfold ons_rectDartMask
  rw [Matrix.mul_diagonal]
  simp [hdart]

theorem ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_left
    (M N : Nat) (weight : ons_RectDart M N → Complex)
    (next dart : ons_RectDart M N)
    (hnext : ¬ons_rectDartValid M N next) :
    ons_rectKWmatDartWeighted M N weight next dart = 0 := by
  classical
  unfold ons_rectKWmatDartWeighted
  rw [Matrix.mul_diagonal]
  unfold ons_rectDartMask
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp [Matrix.diagonal_mul, hnext]



theorem kwGraphTransition_canonical_eq_rectKWmatDartWeighted_apply
    {M N : Nat}
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (dartWeight : ons_RectDart M N → Complex)
    (hweight : ∀ dart : (ons_rectDualGraph M N).Dart,
      dartWeight (ons_rectDualDartSlot dart) = edgeWeight dart.edge)
    (dart next : (ons_rectDualGraph M N).Dart) :
    kwGraphTransition (ons_rectDualGraph M N) edgeWeight
        (ons_rectDualStraightLineEmbedding M N).turnPhase dart next =
      ons_rectKWmatDartWeighted M N dartWeight
        (ons_rectDualDartSlot next) (ons_rectDualDartSlot dart) := by
  rw [ons_rectKWmatDartWeighted_apply_of_valid M N dartWeight
    (ons_rectDualDartSlot next) (ons_rectDualDartSlot dart)
    (ons_rectDualDartSlot_valid next) (ons_rectDualDartSlot_valid dart)]
  by_cases hstep : dart.snd = next.fst
  · have hslotStep : (ons_rectDualDartSlot next).1 =
        ons_rectDirStep M N (ons_rectDualDartSlot dart).2
          (ons_rectDualDartSlot dart).1 := by
      simpa [ons_rectDualDartSlot, hstep] using
        ons_rectDualVertexSlot_snd_eq_rectDirStep dart
    rw [if_pos hslotStep]
    by_cases hedge : dart.edge = next.edge
    · rw [kwGraphTransition]
      simp only [hstep, true_and, hedge]
      have hreverse : next = dart.symm := by
        rcases (SimpleGraph.dart_edge_eq_iff dart next).mp hedge with heq | heq
        · exfalso
          exact dart.fst_ne_snd (by simpa [heq] using hstep.symm)
        · exact (congrArg SimpleGraph.Dart.symm heq).symm
      rw [hreverse]
      simp only [ons_rectDualDartSlot]
      rw [ons_rectDualDartDirection4_symm, ons_turnW_uturn]
      simp
    · rw [kwGraphTransition, if_pos ⟨hstep, hedge⟩,
        ons_rectDual_turnPhase_eq_turnW dart next hstep hedge,
        hweight dart]
      simp [ons_rectDualDartSlot]
      ring
  · have hslotStep : (ons_rectDualDartSlot next).1 ≠
        ons_rectDirStep M N (ons_rectDualDartSlot dart).2
          (ons_rectDualDartSlot dart).1 := by
      intro hslot
      apply hstep
      apply ons_rectDualVertexSlot_injective
      rw [ons_rectDualVertexSlot_snd_eq_rectDirStep dart]
      simpa [ons_rectDualDartSlot] using hslot.symm
    rw [kwGraphTransition, if_neg (fun h ↦ hstep h.1), if_neg hslotStep]




theorem reindex_rectKWmatDartWeighted_eq_native_fromBlocks
    (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex) :
    (Matrix.reindex (ons_rectDualDartSumEquiv M N).symm
      (ons_rectDualDartSumEquiv M N).symm)
        (ons_rectKWmatDartWeighted M N
          (ons_rectDualSlotWeight M N edgeWeight)) =
      Matrix.fromBlocks
        (kwGraphTransition (ons_rectDualGraph M N) edgeWeight
          (ons_rectDualStraightLineEmbedding M N).turnPhase).transpose
        0 0 0 := by
  ext i j
  rcases i with dart | padding <;> rcases j with next | padding'
  · simpa [Matrix.reindex_apply, Matrix.submatrix,
      ons_rectDualDartSumEquiv, ons_rectDualDartEquivValid] using
      (kwGraphTransition_canonical_eq_rectKWmatDartWeighted_apply
        edgeWeight (ons_rectDualSlotWeight M N edgeWeight)
        (ons_rectDualSlotWeight_dartSlot M N edgeWeight) next dart).symm
  · simpa [Matrix.reindex_apply, Matrix.submatrix,
      ons_rectDualDartSumEquiv, ons_rectDualDartEquivValid] using
      ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_right M N
        (ons_rectDualSlotWeight M N edgeWeight)
        (ons_rectDualDartSlot dart) padding'.1 padding'.2
  · simpa [Matrix.reindex_apply, Matrix.submatrix,
      ons_rectDualDartSumEquiv, ons_rectDualDartEquivValid] using
      ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_left M N
        (ons_rectDualSlotWeight M N edgeWeight)
        padding.1 (ons_rectDualDartSlot next) padding.2
  · simpa [Matrix.reindex_apply, Matrix.submatrix,
      ons_rectDualDartSumEquiv, ons_rectDualDartEquivValid] using
      ons_rectKWmatDartWeighted_apply_eq_zero_of_not_valid_left M N
        (ons_rectDualSlotWeight M N edgeWeight)
        padding.1 padding'.1 padding.2


theorem rectKWmatDartWeighted_charpoly_eq_native_mul_X
    (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex) :
    (ons_rectKWmatDartWeighted M N
        (ons_rectDualSlotWeight M N edgeWeight)).charpoly =
      (kwGraphTransition (ons_rectDualGraph M N) edgeWeight
          (ons_rectDualStraightLineEmbedding M N).turnPhase).charpoly *
        Polynomial.X ^ Fintype.card
          {slot : ons_RectDart M N // ¬ons_rectDartValid M N slot} := by
  have h := congrArg Matrix.charpoly
    (reindex_rectKWmatDartWeighted_eq_native_fromBlocks M N edgeWeight)
  rw [Matrix.charpoly_reindex,
    Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_transpose, Matrix.charpoly_zero] at h
  exact h


theorem rectKWmatDartWeighted_det_one_sub_eq_native
    (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex) :
    (1 - ons_rectKWmatDartWeighted M N
      (ons_rectDualSlotWeight M N edgeWeight)).det =
      (1 - kwGraphTransition (ons_rectDualGraph M N) edgeWeight
        (ons_rectDualStraightLineEmbedding M N).turnPhase).det := by
  have h := congrArg (Polynomial.eval (1 : Complex))
    (rectKWmatDartWeighted_charpoly_eq_native_mul_X M N edgeWeight)
  rw [Polynomial.eval_mul, Matrix.eval_charpoly, Matrix.eval_charpoly] at h
  simpa using h



theorem norm_root_kwGraphTransition_canonical_le
    (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (q : Real) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q)
    (alpha : Complex)
    (halpha : alpha ∈
      (kwGraphTransition (ons_rectDualGraph M N) edgeWeight
        (ons_rectDualStraightLineEmbedding M N).turnPhase).charpoly.roots) :
    ‖alpha‖ ≤ (Real.sqrt 2 + 1) * q := by
  let native := kwGraphTransition (ons_rectDualGraph M N) edgeWeight
    (ons_rectDualStraightLineEmbedding M N).turnPhase
  let padded := ons_rectKWmatDartWeighted M N
    (ons_rectDualSlotWeight M N edgeWeight)
  have hnative : native.charpoly.IsRoot alpha :=
    (Polynomial.mem_roots (Matrix.charpoly_monic native).ne_zero).mp halpha
  have hpadded : padded.charpoly.IsRoot alpha := by
    rw [show padded.charpoly = native.charpoly *
        Polynomial.X ^ Fintype.card
          {slot : ons_RectDart M N // ¬ons_rectDartValid M N slot} by
      simpa [native, padded] using
        rectKWmatDartWeighted_charpoly_eq_native_mul_X M N edgeWeight]
    rw [Polynomial.IsRoot, Polynomial.eval_mul, hnative]
    simp
  have hpaddedRoots : alpha ∈ padded.charpoly.roots :=
    (Polynomial.mem_roots (Matrix.charpoly_monic padded).ne_zero).mpr hpadded
  exact norm_root_ons_rectKWmatDartWeighted_le M N
    (ons_rectDualSlotWeight M N edgeWeight) q hq
    (norm_ons_rectDualSlotWeight_le M N edgeWeight q hq hweight)
    alpha hpaddedRoots



theorem kwGraphTransition_canonical_spectral
    (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (q : Real) (hq0 : 0 ≤ q) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q) :
    ∀ alpha ∈
      (kwGraphTransition (ons_rectDualGraph M N) edgeWeight
        (ons_rectDualStraightLineEmbedding M N).turnPhase).charpoly.roots,
      ‖alpha‖ < 1 := by
  intro alpha halpha
  refine (norm_root_kwGraphTransition_canonical_le
    M N edgeWeight q hq0 hweight alpha halpha).trans_lt ?_
  have hconstant : 0 < Real.sqrt 2 + 1 := by positivity
  have hmul := mul_lt_mul_of_pos_left hq hconstant
  simpa [sqrt_two_add_one_mul_signedLoopCriticalWeight] using hmul



theorem kwGraphTransition_canonical_det_eq_walk_exp
    (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex)
    (q : Real) (hq0 : 0 ≤ q) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : ∀ edge, ‖edgeWeight edge‖ ≤ q) :
    (1 - kwGraphTransition (ons_rectDualGraph M N) edgeWeight
        (ons_rectDualStraightLineEmbedding M N).turnPhase).det =
      Complex.exp (-∑' n : Nat,
        (∑ walk : Fin (n + 1) → (ons_rectDualGraph M N).Dart,
          ∏ k : Fin (n + 1),
            kwGraphTransition (ons_rectDualGraph M N) edgeWeight
              (ons_rectDualStraightLineEmbedding M N).turnPhase
              (walk k) (walk (k + 1))) / (n + 1)) := by
  exact ons_det_eq_walk_exp _
    (kwGraphTransition_canonical_spectral
      M N edgeWeight q hq0 hq hweight)



noncomputable def ons_rectDualWalkExponent (M N : Nat)
    (edgeWeight : Sym2 (ons_RectDualVertex M N) → Complex) : Complex :=
  ∑' n : Nat,
    (∑ walk : Fin (n + 1) → (ons_rectDualGraph M N).Dart,
      ∏ k : Fin (n + 1),
        kwGraphTransition (ons_rectDualGraph M N) edgeWeight
          (ons_rectDualStraightLineEmbedding M N).turnPhase
          (walk k) (walk (k + 1))) / (n + 1)


noncomputable def ons_rectDualEdgeSignDefect (M N : Nat)
    (defect : Sym2 (ons_RectDualVertex M N) → Prop)
    [DecidablePred defect] (q : Real)
    (edge : Sym2 (ons_RectDualVertex M N)) : Complex :=
  if defect edge then -(q : Complex) else (q : Complex)

theorem norm_ons_rectDualEdgeSignDefect
    (M N : Nat)
    (defect : Sym2 (ons_RectDualVertex M N) → Prop)
    [DecidablePred defect] {q : Real} (hq : 0 ≤ q)
    (edge : Sym2 (ons_RectDualVertex M N)) :
    ‖ons_rectDualEdgeSignDefect M N defect q edge‖ = q := by
  unfold ons_rectDualEdgeSignDefect
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hq]



theorem ons_rectDualSignDefect_det_ratio_eq_walk_exp
    (M N : Nat)
    (defect : Sym2 (ons_RectDualVertex M N) → Prop)
    [DecidablePred defect]
    (q : Real) (hq0 : 0 ≤ q) (hq : q < ons_signedLoopCriticalWeight) :
    (1 - kwGraphTransition (ons_rectDualGraph M N)
        (ons_rectDualEdgeSignDefect M N defect q)
        (ons_rectDualStraightLineEmbedding M N).turnPhase).det /
      (1 - kwGraphTransition (ons_rectDualGraph M N)
        (fun _ ↦ (q : Complex))
        (ons_rectDualStraightLineEmbedding M N).turnPhase).det =
      Complex.exp (-(ons_rectDualWalkExponent M N
          (ons_rectDualEdgeSignDefect M N defect q) -
        ons_rectDualWalkExponent M N (fun _ ↦ (q : Complex)))) := by
  have hdef := kwGraphTransition_canonical_det_eq_walk_exp M N
    (ons_rectDualEdgeSignDefect M N defect q) q hq0 hq
    (fun edge ↦ (norm_ons_rectDualEdgeSignDefect
      M N defect hq0 edge).le)
  have hplain := kwGraphTransition_canonical_det_eq_walk_exp M N
    (fun _ ↦ (q : Complex)) q hq0 hq (fun _ ↦ by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0])
  rw [hdef, hplain, ← Complex.exp_sub]
  congr 1
  unfold ons_rectDualWalkExponent
  ring

end

end StatMech.Onsager
