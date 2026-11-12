/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.TorusIntersection











open scoped BigOperators
open Finset

namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section




structure IntegralSquareTorusCycle (L : Nat) [NeZero L] where
  horizontal : (ZMod L × ZMod L) → Int
  vertical : (ZMod L × ZMod L) → Int
  divergence_zero : ∀ p,
    horizontal p + vertical p -
      horizontal (p.1 - 1, p.2) -
      vertical (p.1, p.2 - 1) = 0

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def xFlux (C : IntegralSquareTorusCycle L) (x : ZMod L) : Int :=
  ∑ y : ZMod L, C.horizontal (x, y)


def yFlux (C : IntegralSquareTorusCycle L) (y : ZMod L) : Int :=
  ∑ x : ZMod L, C.vertical (x, y)

theorem xFlux_pred (C : IntegralSquareTorusCycle L) (x : ZMod L) :
    C.xFlux x = C.xFlux (x - 1) := by
  have hsum :
      ∑ y : ZMod L,
        (C.horizontal (x, y) + C.vertical (x, y) -
          C.horizontal (x - 1, y) - C.vertical (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    exact C.divergence_zero (x, y)
  have hvshift :
      (∑ y : ZMod L, C.vertical (x, y - 1)) =
        ∑ y : ZMod L, C.vertical (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun y => C.vertical (x, y)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hvshift] at hsum
  unfold xFlux
  linarith

theorem yFlux_pred (C : IntegralSquareTorusCycle L) (y : ZMod L) :
    C.yFlux y = C.yFlux (y - 1) := by
  have hsum :
      ∑ x : ZMod L,
        (C.horizontal (x, y) + C.vertical (x, y) -
          C.horizontal (x - 1, y) - C.vertical (x, y - 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact C.divergence_zero (x, y)
  have hhshift :
      (∑ x : ZMod L, C.horizontal (x - 1, y)) =
        ∑ x : ZMod L, C.horizontal (x, y) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
        (fun x => C.horizontal (x, y)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [hhshift] at hsum
  unfold yFlux
  linarith

theorem xFlux_eq_neg_one (C : IntegralSquareTorusCycle L) (x : ZMod L) :
    C.xFlux x = C.xFlux (-1) :=
  ons_zmod_eq_neg_one_of_eq_pred C.xFlux C.xFlux_pred x

theorem yFlux_eq_neg_one (C : IntegralSquareTorusCycle L) (y : ZMod L) :
    C.yFlux y = C.yFlux (-1) :=
  ons_zmod_eq_neg_one_of_eq_pred C.yFlux C.yFlux_pred y


def zeroFluxHorizontal (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) : Int :=
  C.horizontal p - if p.2 = 0 then C.xFlux (-1) else 0


def zeroFluxVertical (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) : Int :=
  C.vertical p - if p.1 = 0 then C.yFlux (-1) else 0

theorem zeroFlux_divergence_zero (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) :
    C.zeroFluxHorizontal p + C.zeroFluxVertical p -
      C.zeroFluxHorizontal (p.1 - 1, p.2) -
      C.zeroFluxVertical (p.1, p.2 - 1) = 0 := by
  unfold zeroFluxHorizontal zeroFluxVertical
  have h := C.divergence_zero p
  linarith

theorem zeroFluxHorizontal_sum_zero (C : IntegralSquareTorusCycle L)
    (x : ZMod L) :
    ∑ y : ZMod L, C.zeroFluxHorizontal (x, y) = 0 := by
  unfold zeroFluxHorizontal
  rw [Finset.sum_sub_distrib]
  change C.xFlux x -
    (∑ y : ZMod L, if y = 0 then C.xFlux (-1) else 0) = 0
  rw [C.xFlux_eq_neg_one x]
  simp

theorem zeroFluxVertical_sum_zero (C : IntegralSquareTorusCycle L)
    (y : ZMod L) :
    ∑ x : ZMod L, C.zeroFluxVertical (x, y) = 0 := by
  unfold zeroFluxVertical
  rw [Finset.sum_sub_distrib]
  change C.yFlux y -
    (∑ x : ZMod L, if x = 0 then C.yFlux (-1) else 0) = 0
  rw [C.yFlux_eq_neg_one y]
  simp

theorem zmodPrefix_sub_pred_of_sum_zero
    (f : ZMod L → Int) (hsum : ∑ z, f z = 0) (z : ZMod L) :
    ons_zmodPrefix f z - ons_zmodPrefix f (z - 1) = f z := by
  by_cases hz : z = 0
  · subst z
    have hrange := ons_sum_zmod_eq_sum_range L f
    have hgt : 2 < L := Fact.out
    have hL : L = (L - 1) + 1 := by omega
    have hdecomp :
        (∑ i ∈ Finset.range L, f (i : ZMod L)) =
          f 0 + ∑ i ∈ Finset.range (L - 1),
            f ((i + 1 : Nat) : ZMod L) := by
      rw [show Finset.range L = Finset.range ((L - 1) + 1) by
        exact congrArg Finset.range hL]
      simpa only [Nat.cast_zero] using
        ons_sum_range_succ_first (fun i : Nat => f (i : ZMod L)) (L - 1)
    rw [hdecomp, hsum] at hrange
    have hprefix :
        (∑ i ∈ Finset.range (L - 1),
          f ((i + 1 : Nat) : ZMod L)) = ons_zmodPrefix f (-1) := by
      unfold ons_zmodPrefix
      rw [ons_zmod_val_neg_one]
    have hpref : ons_zmodPrefix f (-1) = -f 0 := by
      rw [← hprefix]
      linarith
    rw [zero_sub, ons_zmodPrefix_zero, hpref]
    ring
  · rw [ons_zmodPrefix_eq_add_pred f z hz]
    abel


def streamPotential (C : IntegralSquareTorusCycle L)
    (p : ZMod L × ZMod L) : Int :=
  ons_zmodPrefix (fun y => C.zeroFluxHorizontal (0, y)) p.2 -
    ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2)) p.1

theorem streamPotential_vertical_boundary
    (C : IntegralSquareTorusCycle L) (p : ZMod L × ZMod L) :
    C.streamPotential (p.1 - 1, p.2) - C.streamPotential p =
      C.zeroFluxVertical p := by
  have hv := zmodPrefix_sub_pred_of_sum_zero
    (fun x => C.zeroFluxVertical (x, p.2))
    (C.zeroFluxVertical_sum_zero p.2) p.1
  unfold streamPotential
  linarith

theorem streamPotential_horizontal_boundary
    (C : IntegralSquareTorusCycle L) (p : ZMod L × ZMod L) :
    C.streamPotential p - C.streamPotential (p.1, p.2 - 1) =
      C.zeroFluxHorizontal p := by
  have hh := zmodPrefix_sub_pred_of_sum_zero
    (fun y => C.zeroFluxHorizontal (0, y))
    (C.zeroFluxHorizontal_sum_zero 0) p.2
  have hprefixDiff :
      ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2)) p.1 -
        ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2 - 1)) p.1 =
      C.zeroFluxHorizontal (0, p.2) -
        C.zeroFluxHorizontal (p.1, p.2) := by
    unfold ons_zmodPrefix
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ i ∈ Finset.range p.1.val,
          (C.zeroFluxVertical (((i + 1 : Nat) : ZMod L), p.2) -
            C.zeroFluxVertical (((i + 1 : Nat) : ZMod L), p.2 - 1))) =
          ∑ i ∈ Finset.range p.1.val,
            (C.zeroFluxHorizontal (((i : Nat) : ZMod L), p.2) -
              C.zeroFluxHorizontal (((i + 1 : Nat) : ZMod L), p.2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hdiv := C.zeroFlux_divergence_zero
              (((i + 1 : Nat) : ZMod L), p.2)
            have hsub : (((i + 1 : Nat) : ZMod L) - 1) =
                (i : ZMod L) := by
              rw [Nat.cast_add, Nat.cast_one]
              ring
            rw [hsub] at hdiv
            linarith
      _ = C.zeroFluxHorizontal (0, p.2) -
          C.zeroFluxHorizontal (((p.1.val : Nat) : ZMod L), p.2) := by
            rw [Finset.sum_range_sub']
            simp only [Nat.cast_zero]
      _ = C.zeroFluxHorizontal (0, p.2) -
          C.zeroFluxHorizontal (p.1, p.2) := by
            rw [ZMod.natCast_zmod_val]
  change
    (ons_zmodPrefix (fun y => C.zeroFluxHorizontal (0, y)) p.2 -
        ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2)) p.1) -
      (ons_zmodPrefix (fun y => C.zeroFluxHorizontal (0, y)) (p.2 - 1) -
        ons_zmodPrefix (fun x => C.zeroFluxVertical (x, p.2 - 1)) p.1) =
      C.zeroFluxHorizontal p
  linarith



def intersection (C D : IntegralSquareTorusCycle L) : Int :=
  ∑ p : ZMod L × ZMod L,
    (C.horizontal p * D.vertical (p.1, p.2 - 1) -
      C.vertical p * D.horizontal (p.1 - 1, p.2))

theorem zeroFlux_intersection_eq_zero
    (C D : IntegralSquareTorusCycle L) :
    ∑ p : ZMod L × ZMod L,
      (C.zeroFluxHorizontal p * D.vertical (p.1, p.2 - 1) -
        C.zeroFluxVertical p * D.horizontal (p.1 - 1, p.2)) = 0 := by
  let P := C.streamPotential
  have hvshift :
      (∑ p : ZMod L × ZMod L,
        P (p.1, p.2 - 1) * D.vertical (p.1, p.2 - 1)) =
      ∑ p : ZMod L × ZMod L, P p * D.vertical p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.refl (ZMod L))
          (Equiv.addRight (-1 : ZMod L)))
        (fun p : ZMod L × ZMod L => P p * D.vertical p))
  have hhshift :
      (∑ p : ZMod L × ZMod L,
        P (p.1 - 1, p.2) * D.horizontal (p.1 - 1, p.2)) =
      ∑ p : ZMod L × ZMod L, P p * D.horizontal p := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.addRight (-1 : ZMod L))
          (Equiv.refl (ZMod L)))
        (fun p : ZMod L × ZMod L => P p * D.horizontal p))
  simp_rw [← C.streamPotential_horizontal_boundary,
    ← C.streamPotential_vertical_boundary]
  change (∑ p : ZMod L × ZMod L,
    ((P p - P (p.1, p.2 - 1)) * D.vertical (p.1, p.2 - 1) -
      (P (p.1 - 1, p.2) - P p) * D.horizontal (p.1 - 1, p.2))) = 0
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hvshift, hhshift]
  calc
    (∑ p, P p * D.vertical (p.1, p.2 - 1)) -
          (∑ p, P p * D.vertical p) -
        ((∑ p, P p * D.horizontal p) -
          ∑ p, P p * D.horizontal (p.1 - 1, p.2)) =
      ∑ p, P p *
        (D.vertical (p.1, p.2 - 1) - D.vertical p -
          D.horizontal p + D.horizontal (p.1 - 1, p.2)) := by
            simp only [mul_add, mul_sub, Finset.sum_add_distrib,
              Finset.sum_sub_distrib]
            ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      have hdiv := D.divergence_zero p
      rw [show D.vertical (p.1, p.2 - 1) - D.vertical p -
          D.horizontal p + D.horizontal (p.1 - 1, p.2) = 0 by
        linarith]
      ring

theorem intersection_eq_flux_det (C D : IntegralSquareTorusCycle L) :
    C.intersection D =
      C.xFlux (-1) * D.yFlux (-1) -
        C.yFlux (-1) * D.xFlux (-1) := by
  unfold intersection
  have hH : ∀ p, C.horizontal p = C.zeroFluxHorizontal p +
      if p.2 = 0 then C.xFlux (-1) else 0 := by
    intro p
    unfold zeroFluxHorizontal
    ring
  have hV : ∀ p, C.vertical p = C.zeroFluxVertical p +
      if p.1 = 0 then C.yFlux (-1) else 0 := by
    intro p
    unfold zeroFluxVertical
    ring
  simp_rw [hH, hV]
  calc
    (∑ p : ZMod L × ZMod L,
      ((C.zeroFluxHorizontal p + if p.2 = 0 then C.xFlux (-1) else 0) *
          D.vertical (p.1, p.2 - 1) -
        (C.zeroFluxVertical p + if p.1 = 0 then C.yFlux (-1) else 0) *
          D.horizontal (p.1 - 1, p.2))) =
        (∑ p : ZMod L × ZMod L,
          (C.zeroFluxHorizontal p * D.vertical (p.1, p.2 - 1) -
          C.zeroFluxVertical p * D.horizontal (p.1 - 1, p.2))) +
        (∑ p : ZMod L × ZMod L,
          (if p.2 = 0 then C.xFlux (-1) else 0) *
          D.vertical (p.1, p.2 - 1)) -
        (∑ p : ZMod L × ZMod L,
          (if p.1 = 0 then C.yFlux (-1) else 0) *
          D.horizontal (p.1 - 1, p.2)) := by
            simp only [add_mul, Finset.sum_sub_distrib,
              Finset.sum_add_distrib]
            ring
    _ = C.xFlux (-1) * D.yFlux (-1) -
        C.yFlux (-1) * D.xFlux (-1) := by
      rw [C.zeroFlux_intersection_eq_zero D, zero_add]
      have hx :
          (∑ p : ZMod L × ZMod L,
            (if p.2 = 0 then C.xFlux (-1) else 0) *
              D.vertical (p.1, p.2 - 1)) =
            C.xFlux (-1) * D.yFlux (-1) := by
        rw [Fintype.sum_prod_type]
        simp
        unfold yFlux
        rw [Finset.mul_sum]
      have hy :
          (∑ p : ZMod L × ZMod L,
            (if p.1 = 0 then C.yFlux (-1) else 0) *
              D.horizontal (p.1 - 1, p.2)) =
            C.yFlux (-1) * D.xFlux (-1) := by
        rw [Fintype.sum_prod_type]
        simp
        unfold xFlux
        rw [Finset.mul_sum]
      rw [hx, hy]



def LocallyDisjoint (C D : IntegralSquareTorusCycle L) : Prop :=
  ∀ p,
    (C.horizontal p = 0 ∧ C.vertical p = 0) ∨
      (D.horizontal (p.1 - 1, p.2) = 0 ∧
        D.vertical (p.1, p.2 - 1) = 0)

theorem intersection_eq_zero_of_locallyDisjoint
    {C D : IntegralSquareTorusCycle L} (h : C.LocallyDisjoint D) :
    C.intersection D = 0 := by
  unfold intersection
  apply Finset.sum_eq_zero
  intro p _
  rcases h p with hC | hD
  · rw [hC.1, hC.2]
    ring
  · rw [hD.1, hD.2]
    ring



theorem flux_det_eq_zero_of_locallyDisjoint
    {C D : IntegralSquareTorusCycle L} (h : C.LocallyDisjoint D) :
    C.xFlux (-1) * D.yFlux (-1) -
      C.yFlux (-1) * D.xFlux (-1) = 0 := by
  rw [← C.intersection_eq_flux_det D,
    C.intersection_eq_zero_of_locallyDisjoint h]




def pointMass (a p : ZMod L × ZMod L) : Int :=
  if p = a then 1 else 0

theorem pointMass_west (a p : ZMod L × ZMod L) :
    pointMass a (p.1 - 1, p.2) = pointMass (a.1 + 1, a.2) p := by
  unfold pointMass
  congr 1
  apply propext
  simp only [Prod.ext_iff]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨by rw [← hx]; ring, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨by rw [hx]; ring, hy⟩

theorem pointMass_south (a p : ZMod L × ZMod L) :
    pointMass a (p.1, p.2 - 1) = pointMass (a.1, a.2 + 1) p := by
  unfold pointMass
  congr 1
  apply propext
  simp only [Prod.ext_iff]
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨hx, by rw [← hy]; ring⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, by rw [hy]; ring⟩


def dartHorizontal (d : ons_Dart L) (p : ZMod L × ZMod L) : Int :=
  if d.2 = 0 then pointMass d.1 p
  else if d.2 = 2 then -pointMass (d.1.1 - 1, d.1.2) p
  else 0


def dartVertical (d : ons_Dart L) (p : ZMod L × ZMod L) : Int :=
  if d.2 = 1 then pointMass d.1 p
  else if d.2 = 3 then -pointMass (d.1.1, d.1.2 - 1) p
  else 0

theorem dart_divergence
    (d : ons_Dart L) (p : ZMod L × ZMod L) :
    dartHorizontal d p + dartVertical d p -
        dartHorizontal d (p.1 - 1, p.2) -
        dartVertical d (p.1, p.2 - 1) =
      pointMass d.1 p - pointMass (ons_dirStep L d.2 d.1) p := by
  classical
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [dartHorizontal, dartVertical, ons_dirStep,
      pointMass_west, pointMass_south] <;> ring



def ofDarts {n : Nat} [NeZero n] (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    IntegralSquareTorusCycle L where
  horizontal p := ∑ k, dartHorizontal (v k) p
  vertical p := ∑ k, dartVertical (v k) p
  divergence_zero p := by
    rw [show (∑ k, dartHorizontal (v k) p) +
          (∑ k, dartVertical (v k) p) -
          (∑ k, dartHorizontal (v k) (p.1 - 1, p.2)) -
          (∑ k, dartVertical (v k) (p.1, p.2 - 1)) =
        ∑ k, (dartHorizontal (v k) p + dartVertical (v k) p -
          dartHorizontal (v k) (p.1 - 1, p.2) -
          dartVertical (v k) (p.1, p.2 - 1)) by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]]
    simp_rw [dart_divergence]
    have hshift :
        (∑ k, pointMass (ons_dirStep L (v k).2 (v k).1) p) =
          ∑ k, pointMass (v k).1 p := by
      calc
        (∑ k, pointMass (ons_dirStep L (v k).2 (v k).1) p) =
            ∑ k, pointMass
              (ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) p := by
                simpa using
                  (Equiv.sum_comp (Equiv.addRight (1 : Fin n))
                    (fun k => pointMass
                      (ons_dirStep L (v k).2 (v k).1) p)).symm
        _ = ∑ k, pointMass (v k).1 p := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hvalid k]
    rw [Finset.sum_sub_distrib, hshift, sub_self]

theorem dartHorizontal_xSeam_sum (d : ons_Dart L) :
    (∑ y : ZMod L, dartHorizontal d (-1, y)) = ons_xWrapSign d := by
  classical
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · by_cases hx : x = -1
    · subst x
      simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff]
    · simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff,
        hx, eq_comm]
  · simp [dartHorizontal, ons_xWrapSign]
  · by_cases hx : x = 0
    · subst x
      simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff]
    · simp [dartHorizontal, pointMass, ons_xWrapSign, Prod.ext_iff,
        hx, eq_comm]
  · simp [dartHorizontal, ons_xWrapSign]

theorem dartVertical_ySeam_sum (d : ons_Dart L) :
    (∑ x : ZMod L, dartVertical d (x, -1)) = ons_yWrapSign d := by
  classical
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [dartVertical, ons_yWrapSign]
  · by_cases hy : y = -1
    · subst y
      simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff]
    · simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff,
        hy, eq_comm]
  · simp [dartVertical, ons_yWrapSign]
  · by_cases hy : y = 0
    · subst y
      simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff]
    · simp [dartVertical, pointMass, ons_yWrapSign, Prod.ext_iff,
        hy, eq_comm]

theorem ofDarts_xFlux {n : Nat} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    (ofDarts v hvalid).xFlux (-1) = ∑ k, ons_xWrapSign (v k) := by
  unfold xFlux ofDarts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact dartHorizontal_xSeam_sum (v k)

theorem ofDarts_yFlux {n : Nat} [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
    (ofDarts v hvalid).yFlux (-1) = ∑ k, ons_yWrapSign (v k) := by
  unfold yFlux ofDarts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact dartVertical_ySeam_sum (v k)



theorem dartLoop_winding_det_eq_zero_of_locallyDisjoint
    {n m : Nat} [NeZero n] [NeZero m]
    (v : Fin n → ons_Dart L)
    (hv : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (w : Fin m → ons_Dart L)
    (hw : ∀ k : Fin m,
      (w k).1 = ons_dirStep L (w (k + 1)).2 (w (k + 1)).1)
    (hdisj : (ofDarts v hv).LocallyDisjoint (ofDarts w hw)) :
    (∑ k, ons_xWrapSign (v k)) * (∑ k, ons_yWrapSign (w k)) -
      (∑ k, ons_yWrapSign (v k)) * (∑ k, ons_xWrapSign (w k)) = 0 := by
  have h := flux_det_eq_zero_of_locallyDisjoint hdisj
  rwa [ofDarts_xFlux, ofDarts_yFlux,
    ofDarts_xFlux, ofDarts_yFlux] at h






def DartListBalanced (l : List (ons_Dart L)) : Prop :=
  ∀ p : ZMod L × ZMod L,
    (l.map (fun d => pointMass d.1 p)).sum =
      (l.map (fun d => pointMass (ons_dirStep L d.2 d.1) p)).sum


def ofDartList (l : List (ons_Dart L)) (hbalanced : DartListBalanced l) :
    IntegralSquareTorusCycle L where
  horizontal p := (l.map (fun d => dartHorizontal d p)).sum
  vertical p := (l.map (fun d => dartVertical d p)).sum
  divergence_zero p := by
    calc
      (l.map (fun d => dartHorizontal d p)).sum +
            (l.map (fun d => dartVertical d p)).sum -
          (l.map (fun d => dartHorizontal d (p.1 - 1, p.2))).sum -
          (l.map (fun d => dartVertical d (p.1, p.2 - 1))).sum =
        (l.map (fun d =>
          dartHorizontal d p + dartVertical d p -
            dartHorizontal d (p.1 - 1, p.2) -
            dartVertical d (p.1, p.2 - 1))).sum := by
          have hcombine : ∀ l' : List (ons_Dart L),
              (l'.map (fun d => dartHorizontal d p)).sum +
                    (l'.map (fun d => dartVertical d p)).sum -
                  (l'.map (fun d =>
                    dartHorizontal d (p.1 - 1, p.2))).sum -
                  (l'.map (fun d =>
                    dartVertical d (p.1, p.2 - 1))).sum =
                (l'.map (fun d =>
                  dartHorizontal d p + dartVertical d p -
                    dartHorizontal d (p.1 - 1, p.2) -
                    dartVertical d (p.1, p.2 - 1))).sum := by
            intro l'
            induction l' with
            | nil => simp
            | cons d l' ih =>
                simp only [List.map_cons, List.sum_cons] at ih ⊢
                linear_combination ih
          exact hcombine l
      _ = (l.map (fun d => pointMass d.1 p -
          pointMass (ons_dirStep L d.2 d.1) p)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro d _
            exact dart_divergence d p
      _ = 0 := by
        have hsub : ∀ l' : List (ons_Dart L),
            (l'.map (fun d => pointMass d.1 p -
                pointMass (ons_dirStep L d.2 d.1) p)).sum =
              (l'.map (fun d => pointMass d.1 p)).sum -
                (l'.map (fun d =>
                  pointMass (ons_dirStep L d.2 d.1) p)).sum := by
          intro l'
          induction l' with
          | nil => simp
          | cons d l' ih =>
              simp only [List.map_cons, List.sum_cons] at ih ⊢
              linear_combination ih
        rw [hsub l]
        rw [hbalanced p, sub_self]

theorem ofDartList_xFlux (l : List (ons_Dart L))
    (hbalanced : DartListBalanced l) :
    (ofDartList l hbalanced).xFlux (-1) =
      (l.map ons_xWrapSign).sum := by
  unfold xFlux ofDartList
  change (∑ y : ZMod L,
    (l.map (fun d => dartHorizontal d (-1, y))).sum) = _
  clear hbalanced
  induction l with
  | nil => simp
  | cons d l ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [dartHorizontal_xSeam_sum, ih]

theorem ofDartList_yFlux (l : List (ons_Dart L))
    (hbalanced : DartListBalanced l) :
    (ofDartList l hbalanced).yFlux (-1) =
      (l.map ons_yWrapSign).sum := by
  unfold yFlux ofDartList
  change (∑ x : ZMod L,
    (l.map (fun d => dartVertical d (x, -1))).sum) = _
  clear hbalanced
  induction l with
  | nil => simp
  | cons d l ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [dartVertical_ySeam_sum, ih]



theorem dartList_winding_det_eq_zero_of_locallyDisjoint
    (v : List (ons_Dart L)) (hv : DartListBalanced v)
    (w : List (ons_Dart L)) (hw : DartListBalanced w)
    (hdisj : (ofDartList v hv).LocallyDisjoint (ofDartList w hw)) :
    (v.map ons_xWrapSign).sum * (w.map ons_yWrapSign).sum -
      (v.map ons_yWrapSign).sum * (w.map ons_xWrapSign).sum = 0 := by
  have h := flux_det_eq_zero_of_locallyDisjoint hdisj
  rwa [ofDartList_xFlux, ofDartList_yFlux,
    ofDartList_xFlux, ofDartList_yFlux] at h

end IntegralSquareTorusCycle

end

end StatMech.FrontierD
