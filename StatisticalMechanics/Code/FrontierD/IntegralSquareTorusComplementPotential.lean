/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedBoundaryOpenPathPotential











namespace StatMech.FrontierD

open StatMech.Onsager
open IntegralSquareTorusCycle

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def sub (C D : IntegralSquareTorusCycle L) : IntegralSquareTorusCycle L where
  horizontal p := C.horizontal p - D.horizontal p
  vertical p := C.vertical p - D.vertical p
  divergence_zero p := by
    have hC := C.divergence_zero p
    have hD := D.divergence_zero p
    linear_combination hC - hD

@[simp] theorem sub_horizontal (C D : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) :
    (C.sub D).horizontal p = C.horizontal p - D.horizontal p :=
  rfl

@[simp] theorem sub_vertical (C D : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) :
    (C.sub D).vertical p = C.vertical p - D.vertical p :=
  rfl

theorem sub_xFlux (C D : IntegralSquareTorusCycle L) (x : ZMod L) :
    (C.sub D).xFlux x = C.xFlux x - D.xFlux x := by
  unfold xFlux
  simp only [sub_horizontal, Finset.sum_sub_distrib]

theorem sub_yFlux (C D : IntegralSquareTorusCycle L) (y : ZMod L) :
    (C.sub D).yFlux y = C.yFlux y - D.yFlux y := by
  unfold yFlux
  simp only [sub_vertical, Finset.sum_sub_distrib]

theorem zeroFluxHorizontal_eq_horizontal_of_xFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.xFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.zeroFluxHorizontal p = C.horizontal p := by
  simp [zeroFluxHorizontal, hC]

theorem zeroFluxVertical_eq_vertical_of_yFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.yFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.zeroFluxVertical p = C.vertical p := by
  simp [zeroFluxVertical, hC]



theorem streamPotential_west_sub_of_yFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.yFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.streamPotential (p.1 - 1, p.2) - C.streamPotential p =
      C.vertical p := by
  rw [C.streamPotential_vertical_boundary,
    C.zeroFluxVertical_eq_vertical_of_yFlux_eq_zero hC]



theorem streamPotential_north_sub_of_xFlux_eq_zero
    (C : IntegralSquareTorusCycle L) (hC : C.xFlux (-1) = 0)
    (p : ZMod L × ZMod L) :
    C.streamPotential p - C.streamPotential (p.1, p.2 - 1) =
      C.horizontal p := by
  rw [C.streamPotential_horizontal_boundary,
    C.zeroFluxHorizontal_eq_horizontal_of_xFlux_eq_zero hC]

end IntegralSquareTorusCycle

variable {L : Nat} [Fact (8 < L)]

private instance complementPotentialFactTwo : Fact (2 < L) := ⟨by
  have hL : 8 < L := Fact.out
  omega⟩


def integralSquareTorusPotentialIncrement
    (C : IntegralSquareTorusCycle L) (d : ons_Dart L) : Int :=
  C.streamPotential (ons_dirStep L d.2 d.1) - C.streamPotential d.1




def integralSquareTorusCycleListInteraction
    (C : IntegralSquareTorusCycle L) (l : List (ons_Dart L)) : Int :=
  ∑ p : ZMod L × ZMod L,
    (C.horizontal p *
        (l.map (fun d => dartVertical d (p.1, p.2 - 1))).sum -
      C.vertical p *
        (l.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum)

theorem integralSquareTorusCycleListInteraction_sub
    (C D : IntegralSquareTorusCycle L) (l : List (ons_Dart L)) :
    integralSquareTorusCycleListInteraction (C.sub D) l =
      integralSquareTorusCycleListInteraction C l -
        integralSquareTorusCycleListInteraction D l := by
  classical
  unfold integralSquareTorusCycleListInteraction
  simp only [IntegralSquareTorusCycle.sub_horizontal,
    IntegralSquareTorusCycle.sub_vertical, sub_mul,
    Finset.sum_sub_distrib]
  abel

theorem integralSquareTorusCycleListInteraction_ofDartList
    (a : List (ons_Dart L)) (ha : DartListBalanced a)
    (l : List (ons_Dart L)) :
    integralSquareTorusCycleListInteraction (ofDartList a ha) l =
      fkRectRefinedRawInteraction a l :=
  rfl

private theorem sum_ite_west (f : (ZMod L × ZMod L) → Int)
    (x y : ZMod L) :
    (∑ p : ZMod L × ZMod L,
      if p.1 - 1 = x ∧ p.2 = y then f p else 0) = f (x + 1, y) := by
  classical
  rw [Finset.sum_eq_single (x + 1, y)]
  · simp
  · intro b hb hne
    rw [if_neg]
    rintro ⟨hx, hy⟩
    apply hne
    apply Prod.ext
    · dsimp
      rw [← hx]
      ring
    · exact hy
  · simp

private theorem sum_ite_south (f : (ZMod L × ZMod L) → Int)
    (x y : ZMod L) :
    (∑ p : ZMod L × ZMod L,
      if p.1 = x ∧ p.2 - 1 = y then f p else 0) = f (x, y + 1) := by
  classical
  rw [Finset.sum_eq_single (x, y + 1)]
  · simp
  · intro b hb hne
    rw [if_neg]
    rintro ⟨hx, hy⟩
    apply hne
    apply Prod.ext
    · exact hx
    · dsimp
      rw [← hy]
      ring
  · simp

private theorem sum_ite_point (f : (ZMod L × ZMod L) → Int)
    (x y : ZMod L) :
    (∑ p : ZMod L × ZMod L,
      if p.1 = x ∧ p.2 = y then f p else 0) = f (x, y) := by
  classical
  rw [Finset.sum_eq_single (x, y)]
  · simp
  · intro b hb hne
    rw [if_neg]
    exact fun h => hne (Prod.ext h.1 h.2)
  · simp



theorem fkRectRefinedRawInteraction_singleton_eq_potentialIncrement
    (C : IntegralSquareTorusCycle L)
    (hx : C.xFlux (-1) = 0) (hy : C.yFlux (-1) = 0)
    (d : ons_Dart L) :
    (∑ p : ZMod L × ZMod L,
      (C.horizontal p *
          (([d].map (fun e => dartVertical e (p.1, p.2 - 1))).sum) -
        C.vertical p *
          (([d].map (fun e => dartHorizontal e (p.1 - 1, p.2))).sum))) =
      integralSquareTorusPotentialIncrement C d := by
  classical
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · have hwest := C.streamPotential_west_sub_of_yFlux_eq_zero hy
      (x + 1, y)
    simp only [add_sub_cancel_right] at hwest
    simp [dartVertical, dartHorizontal, pointMass,
      integralSquareTorusPotentialIncrement, ons_dirStep]
    rw [sum_ite_west]
    linarith
  · have hnorth := C.streamPotential_north_sub_of_xFlux_eq_zero hx
      (x, y + 1)
    simp only [add_sub_cancel_right] at hnorth
    simp [dartVertical, dartHorizontal, pointMass,
      integralSquareTorusPotentialIncrement, ons_dirStep]
    rw [sum_ite_south]
    exact hnorth.symm
  · have hwest := C.streamPotential_west_sub_of_yFlux_eq_zero hy
      (x, y)
    simp [dartVertical, dartHorizontal, pointMass,
      integralSquareTorusPotentialIncrement, ons_dirStep]
    rw [sum_ite_point]
    exact hwest.symm
  · have hnorth := C.streamPotential_north_sub_of_xFlux_eq_zero hx
      (x, y)
    simp [dartVertical, dartHorizontal, pointMass,
      integralSquareTorusPotentialIncrement, ons_dirStep]
    rw [sum_ite_point]
    linarith



theorem integralSquareTorusCycleListInteraction_eq_streamPotential_sub
    (C : IntegralSquareTorusCycle L)
    (hx : C.xFlux (-1) = 0) (hy : C.yFlux (-1) = 0)
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath p q l) :
    integralSquareTorusCycleListInteraction C
        (l.map (fkRectIntegralSquareDartMod L)) =
      C.streamPotential (fkRectIntegralSquarePointMod L q) -
        C.streamPotential (fkRectIntegralSquarePointMod L p) := by
  induction hl with
  | nil p =>
      simp [integralSquareTorusCycleListInteraction,
        fkRectIntegralSquarePointMod]
  | @cons d q r l hend tail ih =>
      rw [List.map_cons]
      change integralSquareTorusCycleListInteraction C
          ([fkRectIntegralSquareDartMod L d] ++
            l.map (fkRectIntegralSquareDartMod L)) = _
      rw [show integralSquareTorusCycleListInteraction C
            ([fkRectIntegralSquareDartMod L d] ++
              l.map (fkRectIntegralSquareDartMod L)) =
          integralSquareTorusCycleListInteraction C
              [fkRectIntegralSquareDartMod L d] +
            integralSquareTorusCycleListInteraction C
              (l.map (fkRectIntegralSquareDartMod L)) by
        classical
        unfold integralSquareTorusCycleListInteraction
        simp only [List.map_append, List.sum_append, mul_add,
          Finset.sum_add_distrib, Finset.sum_sub_distrib]
        ring,
        ih]
      have hsingle :=
        fkRectRefinedRawInteraction_singleton_eq_potentialIncrement
          C hx hy (fkRectIntegralSquareDartMod L d)
      change integralSquareTorusCycleListInteraction C
          [fkRectIntegralSquareDartMod L d] = _ at hsingle
      rw [hsingle]
      unfold integralSquareTorusPotentialIncrement
      rw [fkRectIntegralSquareDartMod_end, hend]
      change C.streamPotential (fkRectIntegralSquarePointMod L q) -
          C.streamPotential (fkRectIntegralSquarePointMod L d.1) +
          (C.streamPotential (fkRectIntegralSquarePointMod L r) -
            C.streamPotential (fkRectIntegralSquarePointMod L q)) =
        C.streamPotential (fkRectIntegralSquarePointMod L r) -
          C.streamPotential (fkRectIntegralSquarePointMod L d.1)
      ring




theorem fkRectRefinedRawInteraction_sub_eq_of_equalFlux
    (a b : List (ons_Dart L))
    (ha : DartListBalanced a) (hb : DartListBalanced b)
    (hx : (ofDartList a ha).xFlux (-1) =
      (ofDartList b hb).xFlux (-1))
    (hy : (ofDartList a ha).yFlux (-1) =
      (ofDartList b hb).yFlux (-1))
    {p q : Int × Int}
    {l k : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath p q l)
    (hk : FKRectIntegralSquareDartPath p q k) :
    fkRectRefinedRawInteraction a
          (l.map (fkRectIntegralSquareDartMod L)) -
        fkRectRefinedRawInteraction b
          (l.map (fkRectIntegralSquareDartMod L)) =
      fkRectRefinedRawInteraction a
          (k.map (fkRectIntegralSquareDartMod L)) -
        fkRectRefinedRawInteraction b
          (k.map (fkRectIntegralSquareDartMod L)) := by
  let C := (ofDartList a ha).sub (ofDartList b hb)
  have hCx : C.xFlux (-1) = 0 := by
    rw [IntegralSquareTorusCycle.sub_xFlux, hx, sub_self]
  have hCy : C.yFlux (-1) = 0 := by
    rw [IntegralSquareTorusCycle.sub_yFlux, hy, sub_self]
  have hleft :=
    integralSquareTorusCycleListInteraction_eq_streamPotential_sub
      C hCx hCy hl
  have hright :=
    integralSquareTorusCycleListInteraction_eq_streamPotential_sub
      C hCx hCy hk
  rw [integralSquareTorusCycleListInteraction_sub,
    integralSquareTorusCycleListInteraction_ofDartList,
    integralSquareTorusCycleListInteraction_ofDartList] at hleft hright
  exact hleft.trans hright.symm



theorem fkRectRefinedRawInteraction_eq_streamPotential_sub
    (a : List (ons_Dart L)) (ha : DartListBalanced a)
    (hx : (ofDartList a ha).xFlux (-1) = 0)
    (hy : (ofDartList a ha).yFlux (-1) = 0)
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (hl : FKRectIntegralSquareDartPath p q l) :
    fkRectRefinedRawInteraction a
        (l.map (fkRectIntegralSquareDartMod L)) =
      (ofDartList a ha).streamPotential
          (fkRectIntegralSquarePointMod L q) -
        (ofDartList a ha).streamPotential
          (fkRectIntegralSquarePointMod L p) := by
  rw [← integralSquareTorusCycleListInteraction_ofDartList]
  exact integralSquareTorusCycleListInteraction_eq_streamPotential_sub
    (ofDartList a ha) hx hy hl

end

end StatMech.FrontierD
