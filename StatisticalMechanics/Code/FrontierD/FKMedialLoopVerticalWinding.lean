/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierD.FKMedialBoundaryPermutation
import Code.FrontierD.FKMedialLoopTurningFiber

open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


def fkMedialVerticalSeamDart (T : EvenTorus) (i : Fin T.width) :
    FKMedialDart T :=
  ((i, svFinLast T.height_pos), .north)


def fkOrientedVerticalSeamSign (T : EvenTorus)
    (arrows : SixVertexArrows T) (i : Fin T.width) : Int :=
  if arrows.vertical (i, svFinLast T.height_pos) then 1 else -1




def fkMedialCanonicalVerticalSeamSign (T : EvenTorus)
    (i : Fin T.width) : Int :=
  if fkMedialCheckerColor (fkMedialVerticalSeamDart T i) then -1 else 1



def fkMedialLoopCanonicalVerticalFlux
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ i : Fin T.width,
    if (fkMedialLoopGraph T pairing).connectedComponentMk
          (fkMedialVerticalSeamDart T i) = C then
      fkMedialCanonicalVerticalSeamSign T i
    else 0



def fkMedialUnorientedVerticalWindingTotal
    (pairing : FKMedialLoopPairing T) : Nat :=
  ∑ C : FKMedialLoop T pairing,
    (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs


def fkMedialVerticallyWindingComponents
    (pairing : FKMedialLoopPairing T) : Finset (FKMedialLoop T pairing) := by
  classical
  exact Finset.univ.filter fun C =>
    fkMedialLoopCanonicalVerticalFlux pairing C ≠ 0



theorem card_fkMedialVerticallyWindingComponents_le_total
    (pairing : FKMedialLoopPairing T) :
    (fkMedialVerticallyWindingComponents pairing).card ≤
      fkMedialUnorientedVerticalWindingTotal pairing := by
  classical
  rw [Finset.card_eq_sum_ones]
  calc
    (∑ C ∈ fkMedialVerticallyWindingComponents pairing, 1) ≤
        ∑ C ∈ fkMedialVerticallyWindingComponents pairing,
          (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
      apply Finset.sum_le_sum
      intro C hC
      rw [Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero]
      exact (Finset.mem_filter.mp hC).2
    _ ≤ ∑ C : FKMedialLoop T pairing,
          (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.filter_subset _ _
    _ = fkMedialUnorientedVerticalWindingTotal pairing := rfl


def fkOrientedMedialLoopVerticalFlux
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (C : FKMedialLoop T pairing) : Int := by
  classical
  exact ∑ i : Fin T.width,
    if (fkMedialLoopGraph T pairing).connectedComponentMk
          (fkMedialVerticalSeamDart T i) = C then
      fkOrientedVerticalSeamSign T arrows i
    else 0




def fkMedialCheckerArrows (T : EvenTorus) : SixVertexArrows T where
  horizontal v := !fkMedialCheckerColor (v, .east)
  vertical v := !fkMedialCheckerColor (v, .north)

theorem fkMedialDartIncoming_checkerArrows
    (T : EvenTorus) (d : FKMedialDart T) :
    fkMedialDartIncoming (fkMedialCheckerArrows T) d =
      fkMedialCheckerColor d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side <;>
    simp [fkMedialDartIncoming, fkLoopWestIncoming,
      fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming,
      fkMedialCheckerArrows, fkMedialCheckerColor,
      fkMedialSideVertical]



theorem fkMedialCheckerArrows_compatible
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) :
    ∀ v, fkLoopPairingCompatible (pairing v)
      (fkMedialCheckerArrows T) v := by
  intro v
  cases hp : pairing v <;>
    simp only [fkLoopPairingCompatible, Bool.false_eq_true,
      ite_false, ite_true]
  · constructor
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .west) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .north)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .west)).symm
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .east) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .south)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .east)).symm
  · constructor
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .west) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .south)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .west)).symm
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .east) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .north)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .east)).symm

private theorem bool_eq_iff_eq_of_ne_ne
    {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    (a = c ↔ b = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all



theorem fkMedialDartIncoming_eq_checkerColor_iff_of_adj
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Adj d e) :
    (fkMedialDartIncoming arrows d = fkMedialCheckerColor d ↔
      fkMedialDartIncoming arrows e = fkMedialCheckerColor e) := by
  exact bool_eq_iff_eq_of_ne_ne
    (fkMedialLoopGraph_adj_incoming_ne pairing arrows hcompat hde)
    (fkMedialLoopGraph_adj_checkerColor_ne T pairing hde)



theorem fkMedialDartIncoming_eq_checkerColor_iff_of_reachable
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
    (fkMedialDartIncoming arrows d = fkMedialCheckerColor d ↔
      fkMedialDartIncoming arrows e = fkMedialCheckerColor e) := by
  obtain ⟨w⟩ := hde
  induction w with
  | nil => exact Iff.rfl
  | cons h w ih =>
      exact (fkMedialDartIncoming_eq_checkerColor_iff_of_adj
        pairing arrows hcompat h).trans ih

theorem fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq
    (T : EvenTorus) (arrows : SixVertexArrows T) (i : Fin T.width)
    (h : fkMedialDartIncoming arrows (fkMedialVerticalSeamDart T i) =
      fkMedialCheckerColor (fkMedialVerticalSeamDart T i)) :
    fkOrientedVerticalSeamSign T arrows i =
      fkMedialCanonicalVerticalSeamSign T i := by
  change (!arrows.vertical (i, svFinLast T.height_pos)) =
      fkMedialCheckerColor
        ((i, svFinLast T.height_pos), FKMedialSide.north) at h
  unfold fkOrientedVerticalSeamSign fkMedialCanonicalVerticalSeamSign
    fkMedialVerticalSeamDart
  cases ha : arrows.vertical (i, svFinLast T.height_pos) <;>
    cases hc : fkMedialCheckerColor
      ((i, svFinLast T.height_pos), FKMedialSide.north) <;>
    simp_all

theorem fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne
    (T : EvenTorus) (arrows : SixVertexArrows T) (i : Fin T.width)
    (h : fkMedialDartIncoming arrows (fkMedialVerticalSeamDart T i) ≠
      fkMedialCheckerColor (fkMedialVerticalSeamDart T i)) :
    fkOrientedVerticalSeamSign T arrows i =
      -fkMedialCanonicalVerticalSeamSign T i := by
  change (!arrows.vertical (i, svFinLast T.height_pos)) ≠
      fkMedialCheckerColor
        ((i, svFinLast T.height_pos), FKMedialSide.north) at h
  unfold fkOrientedVerticalSeamSign fkMedialCanonicalVerticalSeamSign
    fkMedialVerticalSeamDart
  cases ha : arrows.vertical (i, svFinLast T.height_pos) <;>
    cases hc : fkMedialCheckerColor
      ((i, svFinLast T.height_pos), FKMedialSide.north) <;>
    simp_all



theorem fkOrientedMedialLoopVerticalFlux_eq_or_eq_neg
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (C : FKMedialLoop T pairing) :
    fkOrientedMedialLoopVerticalFlux pairing arrows C =
        fkMedialLoopCanonicalVerticalFlux pairing C ∨
      fkOrientedMedialLoopVerticalFlux pairing arrows C =
        -fkMedialLoopCanonicalVerticalFlux pairing C := by
  classical
  by_cases hmode : fkMedialDartIncoming arrows C.out =
      fkMedialCheckerColor C.out
  · left
    unfold fkOrientedMedialLoopVerticalFlux
      fkMedialLoopCanonicalVerticalFlux
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq
      have hreach : (fkMedialLoopGraph T pairing).Reachable C.out
          (fkMedialVerticalSeamDart T i) :=
        ConnectedComponent.exact (C.out_eq.trans hC.symm)
      exact (fkMedialDartIncoming_eq_checkerColor_iff_of_reachable
        pairing arrows hcompat hreach).1 hmode
    · rw [if_neg hC, if_neg hC]
  · right
    unfold fkOrientedMedialLoopVerticalFlux
      fkMedialLoopCanonicalVerticalFlux
    rw [← sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne
      have hreach : (fkMedialLoopGraph T pairing).Reachable C.out
          (fkMedialVerticalSeamDart T i) :=
        ConnectedComponent.exact (C.out_eq.trans hC.symm)
      intro heq
      apply hmode
      exact (fkMedialDartIncoming_eq_checkerColor_iff_of_reachable
        pairing arrows hcompat hreach).2 heq
    · rw [if_neg hC, if_neg hC, neg_zero]


theorem fkOrientedMedialLoopVerticalFlux_natAbs
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (C : FKMedialLoop T pairing) :
    (fkOrientedMedialLoopVerticalFlux pairing arrows C).natAbs =
      (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
  rcases fkOrientedMedialLoopVerticalFlux_eq_or_eq_neg
      pairing arrows hcompat C with h | h
  · rw [h]
  · rw [h, Int.natAbs_neg]



theorem fkOrientedMedialLoopVerticalFlux_arrowsOfMode
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool)
    (C : FKMedialLoop T pairing) :
    fkOrientedMedialLoopVerticalFlux pairing
        (FKMedialTurningFiber.arrowsOfMode pairing mode) C =
      if mode C then -fkMedialLoopCanonicalVerticalFlux pairing C
      else fkMedialLoopCanonicalVerticalFlux pairing C := by
  classical
  unfold fkOrientedMedialLoopVerticalFlux
    fkMedialLoopCanonicalVerticalFlux
  by_cases hm : mode C
  · rw [if_pos hm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne
      rw [FKMedialTurningFiber.incoming_arrowsOfMode]
      unfold FKMedialTurningFiber.modeIncoming
      rw [hC, hm]
      simp
    · rw [if_neg hC, if_neg hC, neg_zero]
  · rw [if_neg hm]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq
      rw [FKMedialTurningFiber.incoming_arrowsOfMode]
      unfold FKMedialTurningFiber.modeIncoming
      rw [hC, if_neg hm]
    · rw [if_neg hC, if_neg hC]



def fkMedialDownwardVerticalMode
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) : Bool :=
  decide (0 ≤ fkMedialLoopCanonicalVerticalFlux pairing C)

theorem fkOrientedMedialLoopVerticalFlux_downwardMode
    (pairing : FKMedialLoopPairing T) (C : FKMedialLoop T pairing) :
    fkOrientedMedialLoopVerticalFlux pairing
        (FKMedialTurningFiber.arrowsOfMode pairing
          (fkMedialDownwardVerticalMode pairing)) C =
      -((fkMedialLoopCanonicalVerticalFlux pairing C).natAbs : Int) := by
  rw [fkOrientedMedialLoopVerticalFlux_arrowsOfMode]
  unfold fkMedialDownwardVerticalMode
  by_cases h : 0 ≤ fkMedialLoopCanonicalVerticalFlux pairing C
  · simp [h, Int.natAbs_of_nonneg h]
  · rw [if_neg (by simpa using h)]
    rcases Int.natAbs_eq
        (fkMedialLoopCanonicalVerticalFlux pairing C) with hz | hz
    · exfalso
      apply h
      rw [hz]
      positivity
    · exact hz



theorem sum_fkOrientedMedialLoopVerticalFlux_eq
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T) :
    (∑ C : FKMedialLoop T pairing,
        fkOrientedMedialLoopVerticalFlux pairing arrows C) =
      fkOrientedLoopVerticalFlux T arrows := by
  classical
  unfold fkOrientedMedialLoopVerticalFlux fkOrientedLoopVerticalFlux
    fkOrientedVerticalSeamSign
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp



theorem fkOrientedLoopVerticalFlux_downwardMode
    (pairing : FKMedialLoopPairing T) :
    fkOrientedLoopVerticalFlux T
        (FKMedialTurningFiber.arrowsOfMode pairing
          (fkMedialDownwardVerticalMode pairing)) =
      -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
  rw [← sum_fkOrientedMedialLoopVerticalFlux_eq pairing]
  simp_rw [fkOrientedMedialLoopVerticalFlux_downwardMode]
  change (∑ C ∈ (Finset.univ : Finset (FKMedialLoop T pairing)),
      -((fkMedialLoopCanonicalVerticalFlux pairing C).natAbs : Int)) = _
  rw [Finset.sum_neg_distrib]
  congr 1
  unfold fkMedialUnorientedVerticalWindingTotal
  exact (Nat.cast_sum (R := Int)
    (Finset.univ : Finset (FKMedialLoop T pairing))
    (fun C => (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs)).symm




theorem fkOrientedLoopVerticalFlux_eq_downwardMode_of_eq_on_windingComponents
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing -> Bool)
    (hmode : forall C, C ∈ fkMedialVerticallyWindingComponents pairing ->
      mode C = fkMedialDownwardVerticalMode pairing C) :
    fkOrientedLoopVerticalFlux T
        (FKMedialTurningFiber.arrowsOfMode pairing mode) =
      -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
  rw [← sum_fkOrientedMedialLoopVerticalFlux_eq pairing]
  calc
    (∑ C : FKMedialLoop T pairing,
        fkOrientedMedialLoopVerticalFlux pairing
          (FKMedialTurningFiber.arrowsOfMode pairing mode) C) =
        ∑ C : FKMedialLoop T pairing,
          fkOrientedMedialLoopVerticalFlux pairing
            (FKMedialTurningFiber.arrowsOfMode pairing
              (fkMedialDownwardVerticalMode pairing)) C := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [fkOrientedMedialLoopVerticalFlux_arrowsOfMode,
        fkOrientedMedialLoopVerticalFlux_arrowsOfMode]
      by_cases hflux : fkMedialLoopCanonicalVerticalFlux pairing C = 0
      · simp [hflux]
      · have hmem : C ∈ fkMedialVerticallyWindingComponents pairing := by
          simp [fkMedialVerticallyWindingComponents, hflux]
        rw [hmode C hmem]
    _ = -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
      rw [sum_fkOrientedMedialLoopVerticalFlux_eq]
      exact fkOrientedLoopVerticalFlux_downwardMode pairing

private theorem even_natAbs_cast_sub_self (z : Int) :
    Even ((z.natAbs : Int) - z) := by
  rw [Int.even_sub', Int.odd_coe_nat, Int.natAbs_odd]




theorem even_fkMedialUnorientedVerticalWindingTotal
    (pairing : FKMedialLoopPairing T) :
    Even (fkMedialUnorientedVerticalWindingTotal pairing) := by
  let arrows := fkMedialCheckerArrows T
  let f := fkOrientedMedialLoopVerticalFlux pairing arrows
  let g : FKMedialLoop T pairing → Int :=
    fun C => Int.ofNat (f C).natAbs - f C
  have habs (C : FKMedialLoop T pairing) :
      (f C).natAbs =
        (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
    exact fkOrientedMedialLoopVerticalFlux_natAbs pairing arrows
      (fkMedialCheckerArrows_compatible T pairing) C
  have hdiff : Even (∑ C : FKMedialLoop T pairing, g C) := by
    apply Finset.even_sum
    intro C hC
    exact even_natAbs_cast_sub_self (f C)
  have hflux : Even (∑ C : FKMedialLoop T pairing, f C) := by
    rw [sum_fkOrientedMedialLoopVerticalFlux_eq]
    rw [fkOrientedLoopVerticalFlux_eq_charge]
    have hwidth : Even (T.width : Int) :=
      (Int.even_coe_nat _).2 T.width_even
    exact (Even.mul_right even_two _).sub hwidth
  have hcast :
      Even ((fkMedialUnorientedVerticalWindingTotal pairing : Nat) : Int) := by
    have hadd := hdiff.add hflux
    simp only [g] at hadd
    rw [Finset.sum_sub_distrib, sub_add_cancel] at hadd
    change Even (Int.ofNat (∑ C : FKMedialLoop T pairing,
      (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs))
    rw [show Int.ofNat (∑ C : FKMedialLoop T pairing,
          (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs) =
        ∑ C : FKMedialLoop T pairing,
          Int.ofNat (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs by
      simpa using Nat.cast_sum (R := Int)
        (Finset.univ : Finset (FKMedialLoop T pairing))
        (fun C => (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs)]
    simpa only [habs] using hadd
  exact (Int.even_coe_nat _).1 hcast



theorem two_mul_half_fkMedialUnorientedVerticalWindingTotal
    (pairing : FKMedialLoopPairing T) :
    2 * (fkMedialUnorientedVerticalWindingTotal pairing / 2) =
      fkMedialUnorientedVerticalWindingTotal pairing := by
  exact Nat.two_mul_div_two_of_even
    (even_fkMedialUnorientedVerticalWindingTotal pairing)




theorem card_fkMedialVerticallyWindingComponents_le_two_of_half_eq_one
    (pairing : FKMedialLoopPairing T)
    (hU : fkMedialUnorientedVerticalWindingTotal pairing / 2 = 1) :
    (fkMedialVerticallyWindingComponents pairing).card ≤ 2 := by
  calc
    (fkMedialVerticallyWindingComponents pairing).card ≤
        fkMedialUnorientedVerticalWindingTotal pairing :=
      card_fkMedialVerticallyWindingComponents_le_total pairing
    _ = 2 * (fkMedialUnorientedVerticalWindingTotal pairing / 2) :=
      (two_mul_half_fkMedialUnorientedVerticalWindingTotal pairing).symm
    _ = 2 := by rw [hU]



theorem natAbs_fkOrientedLoopVerticalFlux_le_unorientedWindingTotal
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v) :
    (fkOrientedLoopVerticalFlux T arrows).natAbs ≤
      fkMedialUnorientedVerticalWindingTotal pairing := by
  rw [← sum_fkOrientedMedialLoopVerticalFlux_eq pairing arrows]
  calc
    (∑ C : FKMedialLoop T pairing,
        fkOrientedMedialLoopVerticalFlux pairing arrows C).natAbs ≤
        ∑ C : FKMedialLoop T pairing,
          (fkOrientedMedialLoopVerticalFlux pairing arrows C).natAbs := by
      simpa using Int.natAbs_sum_le Finset.univ
        (fun C : FKMedialLoop T pairing =>
          fkOrientedMedialLoopVerticalFlux pairing arrows C)
    _ = fkMedialUnorientedVerticalWindingTotal pairing := by
      unfold fkMedialUnorientedVerticalWindingTotal
      apply Finset.sum_congr rfl
      intro C hC
      exact fkOrientedMedialLoopVerticalFlux_natAbs
        pairing arrows hcompat C



theorem two_mul_le_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (r : Nat)
    (hflux : fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int))) :
    2 * r ≤ fkMedialUnorientedVerticalWindingTotal pairing := by
  have hbound :=
    natAbs_fkOrientedLoopVerticalFlux_le_unorientedWindingTotal
      pairing arrows hcompat
  rw [hflux] at hbound
  norm_num at hbound ⊢
  exact hbound


theorem le_half_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (r : Nat)
    (hflux : fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int))) :
    r ≤ fkMedialUnorientedVerticalWindingTotal pairing / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  simpa [mul_comm] using
    two_mul_le_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
      pairing arrows hcompat r hflux



theorem fkOrientedLoopPairingWeight_ne_zero_iff_compatible
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (arrows : SixVertexArrows T) :
    fkOrientedLoopPairingWeight lam pairing arrows ≠ 0 ↔
      ∀ v, fkLoopPairingCompatible (pairing v) arrows v := by
  classical
  unfold fkOrientedLoopPairingWeight
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h v
    by_contra hbad
    have hv := h v (Finset.mem_univ v)
    simp [fkOrientedLoopLocalWeight, hbad] at hv
  · intro h v hv
    simp only [fkOrientedLoopLocalWeight, if_pos (h v)]
    split
    · split <;> exact Real.exp_ne_zero _
    · norm_num

theorem fkOrientedLoopPairingWeight_nonneg
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (arrows : SixVertexArrows T) :
    0 ≤ fkOrientedLoopPairingWeight lam pairing arrows := by
  classical
  unfold fkOrientedLoopPairingWeight
  apply Finset.prod_nonneg
  intro v hv
  unfold fkOrientedLoopLocalWeight
  split
  · split
    · split <;> positivity
    · norm_num
  · norm_num





theorem exists_positive_weight_verticalFlux_eq_neg_two_mul_half
    (lam : Real) (pairing : FKMedialLoopPairing T) :
    ∃ arrows : SixVertexArrows T,
      0 < fkOrientedLoopPairingWeight lam pairing arrows ∧
      fkOrientedLoopVerticalFlux T arrows =
        -(2 * ((fkMedialUnorientedVerticalWindingTotal pairing / 2 : Nat) : Int)) := by
  let arrows := FKMedialTurningFiber.arrowsOfMode pairing
    (fkMedialDownwardVerticalMode pairing)
  refine ⟨arrows, ?_, ?_⟩
  · have hne : fkOrientedLoopPairingWeight lam pairing arrows ≠ 0 :=
      (fkOrientedLoopPairingWeight_ne_zero_iff_compatible
        lam pairing arrows).2
        (FKMedialTurningFiber.compatible_arrowsOfMode pairing _)
    exact lt_of_le_of_ne (fkOrientedLoopPairingWeight_nonneg lam pairing arrows)
      (Ne.symm hne)
  · have hhalf :=
      two_mul_half_fkMedialUnorientedVerticalWindingTotal pairing
    have hcast : (fkMedialUnorientedVerticalWindingTotal pairing : Int) =
        2 * ((fkMedialUnorientedVerticalWindingTotal pairing / 2 : Nat) : Int) := by
      exact_mod_cast hhalf.symm
    rw [show fkOrientedLoopVerticalFlux T arrows =
        -(fkMedialUnorientedVerticalWindingTotal pairing : Int) by
      exact fkOrientedLoopVerticalFlux_downwardMode pairing]
    rw [hcast]

end

end StatMech.FrontierD
