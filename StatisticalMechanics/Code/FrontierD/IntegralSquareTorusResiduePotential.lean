/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.IntegralSquareTorusIntersection











open scoped BigOperators

namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

namespace IntegralSquareTorusCycle

variable {L : Nat} [Fact (2 < L)]


def residuePotential (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (z : ZMod L × ZMod L) : ZMod p :=
  C.streamPotential z



def residueHorizontalCoeff (C : IntegralSquareTorusCycle L)
    (p : Nat) [NeZero p] (z : ZMod L × ZMod L) : Int :=
  ((C.residuePotential p z).val : Int) -
    (C.residuePotential p (z.1, z.2 - 1)).val



def residueVerticalCoeff (C : IntegralSquareTorusCycle L)
    (p : Nat) [NeZero p] (z : ZMod L × ZMod L) : Int :=
  ((C.residuePotential p (z.1 - 1, z.2)).val : Int) -
    (C.residuePotential p z).val

theorem residueHorizontalCoeff_cast
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (hx : (p : Int) ∣ C.xFlux (-1)) (z : ZMod L × ZMod L) :
    (C.residueHorizontalCoeff p z : ZMod p) =
      (C.horizontal z : ZMod p) := by
  have hflux : (C.xFlux (-1) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hx
  have hstream := C.streamPotential_horizontal_boundary z
  have hstreamCast := congrArg (fun a : Int => (a : ZMod p)) hstream
  push_cast at hstreamCast
  unfold residueHorizontalCoeff residuePotential
  push_cast
  simp only [ZMod.natCast_zmod_val]
  calc
    (C.streamPotential z : ZMod p) -
        (C.streamPotential (z.1, z.2 - 1) : ZMod p) =
      (C.zeroFluxHorizontal z : ZMod p) := hstreamCast
    _ = (C.horizontal z : ZMod p) := by
      unfold zeroFluxHorizontal
      split
      · push_cast
        rw [hflux, sub_zero]
      · simp

theorem residueVerticalCoeff_cast
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (hy : (p : Int) ∣ C.yFlux (-1)) (z : ZMod L × ZMod L) :
    (C.residueVerticalCoeff p z : ZMod p) =
      (C.vertical z : ZMod p) := by
  have hflux : (C.yFlux (-1) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hy
  have hstream := C.streamPotential_vertical_boundary z
  have hstreamCast := congrArg (fun a : Int => (a : ZMod p)) hstream
  push_cast at hstreamCast
  unfold residueVerticalCoeff residuePotential
  push_cast
  simp only [ZMod.natCast_zmod_val]
  calc
    (C.streamPotential (z.1 - 1, z.2) : ZMod p) -
        (C.streamPotential z : ZMod p) =
      (C.zeroFluxVertical z : ZMod p) := hstreamCast
    _ = (C.vertical z : ZMod p) := by
      unfold zeroFluxVertical
      split
      · push_cast
        rw [hflux, sub_zero]
      · simp

theorem abs_residueHorizontalCoeff_lt
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (z : ZMod L × ZMod L) :
    |C.residueHorizontalCoeff p z| < (p : Int) := by
  have ha := ZMod.val_lt (C.residuePotential p z)
  have hb := ZMod.val_lt (C.residuePotential p (z.1, z.2 - 1))
  unfold residueHorizontalCoeff
  rw [abs_lt]
  constructor <;> omega

theorem abs_residueVerticalCoeff_lt
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (z : ZMod L × ZMod L) :
    |C.residueVerticalCoeff p z| < (p : Int) := by
  have ha := ZMod.val_lt (C.residuePotential p (z.1 - 1, z.2))
  have hb := ZMod.val_lt (C.residuePotential p z)
  unfold residueVerticalCoeff
  rw [abs_lt]
  constructor <;> omega

theorem residueHorizontalCoeff_eq_zero_of_horizontal_eq_zero
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (hx : (p : Int) ∣ C.xFlux (-1)) (z : ZMod L × ZMod L)
    (hz : C.horizontal z = 0) :
    C.residueHorizontalCoeff p z = 0 := by
  apply Int.eq_zero_of_abs_lt_dvd
    (m := (p : Int))
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [C.residueHorizontalCoeff_cast p hx, hz]
    norm_num
  · exact C.abs_residueHorizontalCoeff_lt p z

theorem residueVerticalCoeff_eq_zero_of_vertical_eq_zero
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (hy : (p : Int) ∣ C.yFlux (-1)) (z : ZMod L × ZMod L)
    (hz : C.vertical z = 0) :
    C.residueVerticalCoeff p z = 0 := by
  apply Int.eq_zero_of_abs_lt_dvd
    (m := (p : Int))
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [C.residueVerticalCoeff_cast p hy, hz]
    norm_num
  · exact C.abs_residueVerticalCoeff_lt p z

theorem residueHorizontalCoeff_ne_zero_of_horizontal_eq_one
    (C : IntegralSquareTorusCycle L) (p : Nat) [Fact (1 < p)]
    (hx : (p : Int) ∣ C.xFlux (-1)) (z : ZMod L × ZMod L)
    (hz : C.horizontal z = 1) :
    C.residueHorizontalCoeff p z ≠ 0 := by
  intro hzero
  have hcast := C.residueHorizontalCoeff_cast p hx z
  rw [hzero, hz] at hcast
  have h : (0 : ZMod p) = 1 := by simpa using hcast
  exact zero_ne_one h

theorem residueHorizontalCoeff_ne_zero_of_horizontal_eq_neg_one
    (C : IntegralSquareTorusCycle L) (p : Nat) [Fact (1 < p)]
    (hx : (p : Int) ∣ C.xFlux (-1)) (z : ZMod L × ZMod L)
    (hz : C.horizontal z = -1) :
    C.residueHorizontalCoeff p z ≠ 0 := by
  intro hzero
  have hcast := C.residueHorizontalCoeff_cast p hx z
  rw [hzero, hz] at hcast
  have h : (0 : ZMod p) = -1 := by simpa using hcast
  exact (neg_ne_zero.mpr one_ne_zero) h.symm

theorem residueVerticalCoeff_ne_zero_of_vertical_eq_one
    (C : IntegralSquareTorusCycle L) (p : Nat) [Fact (1 < p)]
    (hy : (p : Int) ∣ C.yFlux (-1)) (z : ZMod L × ZMod L)
    (hz : C.vertical z = 1) :
    C.residueVerticalCoeff p z ≠ 0 := by
  intro hzero
  have hcast := C.residueVerticalCoeff_cast p hy z
  rw [hzero, hz] at hcast
  have h : (0 : ZMod p) = 1 := by simpa using hcast
  exact zero_ne_one h

theorem residueVerticalCoeff_ne_zero_of_vertical_eq_neg_one
    (C : IntegralSquareTorusCycle L) (p : Nat) [Fact (1 < p)]
    (hy : (p : Int) ∣ C.yFlux (-1)) (z : ZMod L × ZMod L)
    (hz : C.vertical z = -1) :
    C.residueVerticalCoeff p z ≠ 0 := by
  intro hzero
  have hcast := C.residueVerticalCoeff_cast p hy z
  rw [hzero, hz] at hcast
  have h : (0 : ZMod p) = -1 := by simpa using hcast
  exact (neg_ne_zero.mpr one_ne_zero) h.symm



theorem residueCoeff_divergence
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p]
    (z : ZMod L × ZMod L) :
    C.residueHorizontalCoeff p z + C.residueVerticalCoeff p z -
        C.residueHorizontalCoeff p (z.1 - 1, z.2) -
        C.residueVerticalCoeff p (z.1, z.2 - 1) = 0 := by
  unfold residueHorizontalCoeff residueVerticalCoeff
  ring



theorem sum_residueHorizontalCoeff_eq_zero
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p] :
    ∑ z : ZMod L × ZMod L, C.residueHorizontalCoeff p z = 0 := by
  unfold residueHorizontalCoeff
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ z : ZMod L × ZMod L,
          ((C.residuePotential p (z.1, z.2 - 1)).val : Int)) =
        ∑ z : ZMod L × ZMod L,
          ((C.residuePotential p z).val : Int) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.refl (ZMod L))
          (Equiv.addRight (-1 : ZMod L)))
        (fun z : ZMod L × ZMod L =>
          ((C.residuePotential p z).val : Int)))
  rw [hshift, sub_self]



theorem sum_residueVerticalCoeff_eq_zero
    (C : IntegralSquareTorusCycle L) (p : Nat) [NeZero p] :
    ∑ z : ZMod L × ZMod L, C.residueVerticalCoeff p z = 0 := by
  unfold residueVerticalCoeff
  rw [Finset.sum_sub_distrib]
  have hshift :
      (∑ z : ZMod L × ZMod L,
          ((C.residuePotential p (z.1 - 1, z.2)).val : Int)) =
        ∑ z : ZMod L × ZMod L,
          ((C.residuePotential p z).val : Int) := by
    simpa [sub_eq_add_neg] using
      (Equiv.sum_comp
        (Equiv.prodCongr (Equiv.addRight (-1 : ZMod L))
          (Equiv.refl (ZMod L)))
        (fun z : ZMod L × ZMod L =>
          ((C.residuePotential p z).val : Int)))
  rw [hshift, sub_self]

end IntegralSquareTorusCycle

end

end StatMech.FrontierD
