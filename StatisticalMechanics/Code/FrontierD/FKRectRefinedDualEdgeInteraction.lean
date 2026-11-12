/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDualEdgeCarrier
import Code.FrontierD.FKRectRefinedIntersection



open scoped BigOperators
open Finset

namespace StatMech.FrontierD

open StatMech.Onsager IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

local instance : Fact (2 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩

local instance : Fact (1 < L) :=
  ⟨lt_trans (by omega) (Fact.out : 8 < L)⟩

private theorem dualPointMass_mul_sum (a b : ZMod L × ZMod L) :
    (∑ p, pointMass a p * pointMass b p) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [pointMass]
  · have hs : ¬ b = a := fun hba => h hba.symm
    simp [pointMass, h, hs]

private theorem dualPointMass_west_normalized
    (a p : ZMod L × ZMod L) :
    pointMass a (-1 + p.1, p.2) =
      pointMass (a.1 + 1, a.2) p := by
  convert pointMass_west a p using 1 <;> ring

private theorem dualPointMass_south_normalized
    (a p : ZMod L × ZMod L) :
    pointMass a (p.1, -1 + p.2) =
      pointMass (a.1, a.2 + 1) p := by
  convert pointMass_south a p using 1 <;> ring

private theorem dualSmallNatCast_ne_zero
    (k : Nat) (hk : 0 < k) (hkL : k < L) :
    (k : ZMod L) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have := Nat.le_of_dvd hk hd
  omega



theorem fkRectRefined_perpendicular_centerlines_interaction
    (pairing : Bool) (c : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedPrimalCenterlineDarts (!pairing) c).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts pairing c).map
          (fkRectIntegralSquareDartMod L)) =
      if pairing then 1 else -1 := by
  cases pairing
  · change fkRectRefinedRawInteraction
      (([((c.1 + 2, c.2), 2), ((c.1 + 1, c.2), 2), ((c.1, c.2), 2),
          ((c.1 - 1, c.2), 2)]).map (fkRectIntegralSquareDartMod L))
      (([((c.1, c.2 - 2), 1), ((c.1, c.2 - 1), 1), ((c.1, c.2), 1),
          ((c.1, c.2 + 1), 1)]).map (fkRectIntegralSquareDartMod L)) = -1
    unfold fkRectRefinedRawInteraction
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fkRectIntegralSquareDartMod, dartHorizontal, dartVertical,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, add_zero, if_false, if_true,
      neg_zero, zero_mul, mul_zero]
    ring_nf
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    simp_rw [dualPointMass_south_normalized (L := L),
      dualPointMass_mul_sum (L := L)]
    have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
    have h2 : (2 : ZMod L) ≠ 0 := dualSmallNatCast_ne_zero 2
      (by omega) (by have := (Fact.out : 8 < L); omega)
    have hA (z : ZMod L) : -1 + (2 + z) ≠ z := by
      intro h
      apply h1
      calc
        1 = (-1 + (2 + z)) - z := by ring
        _ = 0 := by rw [h]; ring
    have hB (z : ZMod L) : -1 + (-1 + z) ≠ z := by
      intro h
      apply h2
      calc
        2 = z - (-1 + (-1 + z)) := by ring
        _ = 0 := by rw [h]; ring
    have hC (z : ZMod L) : z ≠ -2 + z + 1 := by
      intro h
      apply h1
      calc
        1 = z - (-2 + z + 1) := by ring
        _ = 0 := by rw [← h]; ring
    have hD (z : ZMod L) : z ≠ 1 + z + 1 := by
      intro h
      apply h2
      calc
        2 = (1 + z + 1) - z := by ring
        _ = 0 := by rw [← h]; ring
    simp only [Prod.mk.injEq]
    simp [hA, hB, hC, hD]
  · change fkRectRefinedRawInteraction
      (([((c.1, c.2 - 2), 1), ((c.1, c.2 - 1), 1), ((c.1, c.2), 1),
          ((c.1, c.2 + 1), 1)]).map (fkRectIntegralSquareDartMod L))
      (([((c.1 + 2, c.2), 2), ((c.1 + 1, c.2), 2), ((c.1, c.2), 2),
          ((c.1 - 1, c.2), 2)]).map (fkRectIntegralSquareDartMod L)) = 1
    unfold fkRectRefinedRawInteraction
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fkRectIntegralSquareDartMod, dartHorizontal, dartVertical,
      Fin.isValue, Fin.reduceEq, ↓reduceIte, add_zero, if_false, if_true,
      neg_zero, zero_mul, mul_zero]
    ring_nf
    repeat' rw [Finset.sum_add_distrib]
    simp_rw [dualPointMass_west_normalized (L := L),
      dualPointMass_mul_sum (L := L)]
    have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
    have h2 : (2 : ZMod L) ≠ 0 := dualSmallNatCast_ne_zero 2
      (by omega) (by have := (Fact.out : 8 < L); omega)
    have h3 : (3 : ZMod L) ≠ 0 := dualSmallNatCast_ne_zero 3
      (by omega) (by have := (Fact.out : 8 < L); omega)
    have h4 : (4 : ZMod L) ≠ 0 := dualSmallNatCast_ne_zero 4
      (by omega) (by have := (Fact.out : 8 < L); omega)
    simp only [Prod.mk.injEq]
    simp_all

end

end StatMech.FrontierD
