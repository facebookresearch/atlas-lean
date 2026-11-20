/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquarePathSplice
import Code.Universality.IsingFermionicLocalSwitching








open Finset Complex

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section



def fkIsingSquareLocalCarrierDarts (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Fin 4 -> FKIsingSquareMedialCarrier n
  | 0 => .dart (e, .west)
  | 1 => .dart (e, .east)
  | 2 => .dart (e, .south)
  | 3 => .dart (e, .north)

theorem fkIsingSquare_closed_west_south_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    (fkIsingSquareDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .south)) =
      isingLambda⁻¹ *
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareDobrushinDomain n hn)
    (setClosed e.1 omega) (setClosed e.1 omega)
    (.dart (e, .west)) (.dart (e, .south)) (-(Real.pi / 2))]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv]
  · simpa only [fkIsingSquareDobrushinDomain] using
      fkIsingSquare_closed_west_south_winding n hn omega e h

theorem fkIsingSquare_closed_east_north_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .north)) =
      isingLambda⁻¹ *
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareDobrushinDomain n hn)
    (setClosed e.1 omega) (setClosed e.1 omega)
    (.dart (e, .east)) (.dart (e, .north)) (-(Real.pi / 2))]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv]
  · simpa only [fkIsingSquareDobrushinDomain] using
      fkIsingSquare_closed_east_north_winding n hn omega e h

theorem fkIsingSquare_open_west_north_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    (fkIsingSquareDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .north)) =
      isingLambda *
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareDobrushinDomain n hn)
    (setOpen e.1 omega) (setOpen e.1 omega)
    (.dart (e, .west)) (.dart (e, .north)) (Real.pi / 2)]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_pi_div_two_eq_isingLambda]
  · simpa only [fkIsingSquareDobrushinDomain] using
      fkIsingSquare_open_west_north_winding n hn omega e h

theorem fkIsingSquare_open_east_south_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    (fkIsingSquareDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .south)) =
      isingLambda *
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .east)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareDobrushinDomain n hn)
    (setOpen e.1 omega) (setOpen e.1 omega)
    (.dart (e, .east)) (.dart (e, .south)) (Real.pi / 2)]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_pi_div_two_eq_isingLambda]
  · simpa only [fkIsingSquareDobrushinDomain] using
      fkIsingSquare_open_east_south_winding n hn omega e h


theorem FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M)
    (omega omega' : ConfigSpace (Sym2 P.V)) (e e' : M)
    (h : D.winding omega' e' = D.winding omega e + 4 * Real.pi) :
    D.windingPhase omega' e' = D.windingPhase omega e := by
  unfold FKIsingDobrushinDomain.windingPhase
  rw [h]
  have hexp :
      Complex.I * ((((D.winding omega e + 4 * Real.pi) / 2 : Real)) : Complex) =
        2 * Real.pi * Complex.I +
          Complex.I * (((D.winding omega e / 2 : Real)) : Complex) := by
    push_cast
    ring
  rw [hexp, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]



theorem fkIsingSquare_double_visit_terminal_side_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧
      (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) ∨
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧
      (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) := by
  rcases fkIsingSquare_double_visit_terminal_side_winding
      n hn omega e hwest heast with ⟨horder, hwind⟩ | ⟨horder, hwind⟩
  · left
    refine ⟨horder, ?_⟩
    unfold FKIsingDobrushinDomain.windingPhase
    simpa only [fkIsingSquareDobrushinDomain, hwind]
  · right
    refine ⟨horder, ?_⟩
    unfold FKIsingDobrushinDomain.windingPhase
    simpa only [fkIsingSquareDobrushinDomain, hwind]


theorem fkIsingSquare_caseThree_westNorth_balance_algebra
    (m cW cE cS cN oW oN : Complex)
    (hcS : cS = isingLambda⁻¹ * cW)
    (hcN : cN = isingLambda⁻¹ * cE)
    (hoN : oN = isingLambda * oW)
    (hterminal : oN = cN) (hsource : oW = cW) :
    (m * cW + (Real.sqrt 2 : Complex) * m * oW) + m * cE =
      m * cS + (m * cN + (Real.sqrt 2 : Complex) * m * oN) := by
  have hcE : cE = isingLambda ^ 2 * cW := by
    calc
      cE = isingLambda * (isingLambda⁻¹ * cE) := by
        field_simp [isingLambda_ne]
      _ = isingLambda * cN := by rw [← hcN]
      _ = isingLambda * oN := by rw [hterminal]
      _ = isingLambda * (isingLambda * oW) := by rw [hoN]
      _ = isingLambda ^ 2 * cW := by rw [hsource]; ring
  rw [hterminal, hcS, hcN, hsource, hcE,
    isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  rw [hs3]
  ring


theorem fkIsingSquare_caseThree_eastSouth_balance_algebra
    (m cW cE cS cN oE oS : Complex)
    (hcS : cS = isingLambda⁻¹ * cW)
    (hcN : cN = isingLambda⁻¹ * cE)
    (hoS : oS = isingLambda * oE)
    (hterminal : oS = cS) (hsource : oE = cE) :
    m * cW + (m * cE + (Real.sqrt 2 : Complex) * m * oE) =
      (m * cS + (Real.sqrt 2 : Complex) * m * oS) + m * cN := by
  have hcW : cW = isingLambda ^ 2 * cE := by
    calc
      cW = isingLambda * (isingLambda⁻¹ * cW) := by
        field_simp [isingLambda_ne]
      _ = isingLambda * cS := by rw [← hcS]
      _ = isingLambda * oS := by rw [hterminal]
      _ = isingLambda * (isingLambda * oE) := by rw [hoS]
      _ = isingLambda ^ 2 * cE := by rw [hsource]; ring
  rw [hterminal, hcS, hcN, hsource, hcW,
    isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  rw [hs3]
  ring

end

end StatMech.Universality
