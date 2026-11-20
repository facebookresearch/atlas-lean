/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointFailure
import Code.Universality.IsingFermionicExitAssembly
















namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section

private theorem reflectedStart_horizontalEndpoint_diffusive_abs_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q| <=
      3276 / (rho : Real) ^ 2 := by
  by_cases hhalf : R <= 2 * level
  · exact
      isingLeapfrogStoppedKernel_reflectedStart_horizontalEndpoint_diffusive_abs_le_of_rightHalf
        R level rho p p' q hstart hmirror hρ hleft hright hhalf hqHorizontal
  · let pr := isingLeapfrogBoxReflectX R p'
    let pr' := isingLeapfrogBoxReflectX R p
    let qr := isingLeapfrogBoxReflectX R q
    have hlevelR : level <= R := by omega
    have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
      rw [hmirror]
      unfold reflectedEndpoint
      dsimp
      omega
    have hrStart : (isingLeapfrogBoxInt pr).1 + 1 = (R - level : Nat) := by
      dsimp [pr]
      rw [boxInt_reflectX]
      dsimp
      rw [hp'x, Nat.cast_sub hlevelR]
      omega
    have hrMirror : isingLeapfrogBoxInt pr' =
        reflectedEndpoint ((R - level : Nat) : Int) (isingLeapfrogBoxInt pr) := by
      dsimp [pr, pr']
      rw [boxInt_reflectX, boxInt_reflectX, hmirror]
      unfold reflectedEndpoint
      dsimp
      rw [Nat.cast_sub hlevelR]
      apply Prod.ext <;> dsimp <;> ring
    have hrHorizontal : qr.1.1 = 0 ∨ qr.1.1 = R := by
      dsimp [qr]
      rcases hqHorizontal with hq0 | hqR
      · right; simp [isingLeapfrogBoxReflectX, hq0]
      · left; simp [isingLeapfrogBoxReflectX, hqR]
    have hr :=
      isingLeapfrogStoppedKernel_reflectedStart_horizontalEndpoint_diffusive_abs_le_of_rightHalf
        R (R - level) rho pr pr' qr hrStart hrMirror hρ (by omega)
          (by omega) (by omega) hrHorizontal
    have hpRef := isingLeapfrogStoppedKernel_reflectX R (rho * rho) p q
    have hp'Ref := isingLeapfrogStoppedKernel_reflectX R (rho * rho) p' q
    dsimp [pr, pr', qr] at hr
    rw [hpRef, hp'Ref] at hr
    simpa [abs_sub_comm] using hr

private theorem reflectedStart_boundary_diffusive_abs_le
    (R level rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
    (hρ : 0 < rho) (hleft : rho <= level)
    (hright : level + rho <= R)
    (hbottom : rho <= p.2.1) (htop : p.2.1 + rho <= R)
    (hbottom' : rho <= p'.2.1) (htop' : p'.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q| <=
      10296 / (rho : Real) ^ 2 := by
  by_cases hhalf : R <= 2 * level
  · exact
      isingLeapfrogStoppedKernel_reflectedStart_boundary_diffusive_abs_le_of_rightHalf
        R level rho p p' q hstart hmirror hρ hleft hright hhalf hbottom htop
          hbottom' htop' hqBoundary
  · let pr := isingLeapfrogBoxReflectX R p'
    let pr' := isingLeapfrogBoxReflectX R p
    let qr := isingLeapfrogBoxReflectX R q
    have hlevelR : level <= R := by omega
    have hp'x : (isingLeapfrogBoxInt p').1 = (level : Int) + 1 := by
      rw [hmirror]
      unfold reflectedEndpoint
      dsimp
      omega
    have hrStart : (isingLeapfrogBoxInt pr).1 + 1 = (R - level : Nat) := by
      dsimp [pr]
      rw [boxInt_reflectX]
      dsimp
      rw [hp'x, Nat.cast_sub hlevelR]
      omega
    have hrMirror : isingLeapfrogBoxInt pr' =
        reflectedEndpoint ((R - level : Nat) : Int) (isingLeapfrogBoxInt pr) := by
      dsimp [pr, pr']
      rw [boxInt_reflectX, boxInt_reflectX, hmirror]
      unfold reflectedEndpoint
      dsimp
      rw [Nat.cast_sub hlevelR]
      apply Prod.ext <;> dsimp <;> ring
    have hrBoundary : isingLeapfrogBoxBoundary R qr := by
      exact (isingLeapfrogBoxBoundary_reflectX_iff R q).2 hqBoundary
    have hr :=
      isingLeapfrogStoppedKernel_reflectedStart_boundary_diffusive_abs_le_of_rightHalf
        R (R - level) rho pr pr' qr hrStart hrMirror hρ (by omega)
          (by omega) (by omega)
          (by simpa [pr, isingLeapfrogBoxReflectX] using hbottom')
          (by simpa [pr, isingLeapfrogBoxReflectX] using htop')
          (by simpa [pr', isingLeapfrogBoxReflectX] using hbottom)
          (by simpa [pr', isingLeapfrogBoxReflectX] using htop) hrBoundary
    have hpRef := isingLeapfrogStoppedKernel_reflectX R (rho * rho) p q
    have hp'Ref := isingLeapfrogStoppedKernel_reflectX R (rho * rho) p' q
    dsimp [pr, pr', qr] at hr
    rw [hpRef, hp'Ref] at hr
    simpa [abs_sub_comm] using hr

theorem isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
    (R level rho : Nat) (west east q : IsingLeapfrogBox R)
    (hwest : west.1.1 + 1 = level) (heast : east.1.1 = level + 1)
    (hy : west.2.1 = east.2.1)
    (hρ : 0 < rho) (hleft : rho <= level) (hright : level + rho <= R)
    (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
    |isingLeapfrogStoppedKernel R (rho * rho) west q -
        isingLeapfrogStoppedKernel R (rho * rho) east q| <=
      3276 / (rho : Real) ^ 2 := by
  have hstart : (isingLeapfrogBoxInt west).1 + 1 = (level : Int) := by
    unfold isingLeapfrogBoxInt
    dsimp
    exact_mod_cast hwest
  have hmirror : isingLeapfrogBoxInt east =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt west) := by
    apply Prod.ext
    · dsimp [isingLeapfrogBoxInt, reflectedEndpoint]
      push_cast
      omega
    · dsimp [isingLeapfrogBoxInt, reflectedEndpoint]
      exact_mod_cast hy.symm
  exact reflectedStart_horizontalEndpoint_diffusive_abs_le R level rho west
    east q hstart hmirror hρ hleft hright hqHorizontal

theorem isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le
    (R level rho : Nat) (west east q : IsingLeapfrogBox R)
    (hwest : west.1.1 + 1 = level) (heast : east.1.1 = level + 1)
    (hy : west.2.1 = east.2.1)
    (hρ : 0 < rho) (hleft : rho <= level) (hright : level + rho <= R)
    (hbottom : rho <= west.2.1) (htop : west.2.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    |isingLeapfrogStoppedKernel R (rho * rho) west q -
        isingLeapfrogStoppedKernel R (rho * rho) east q| <=
      10296 / (rho : Real) ^ 2 := by
  have hstart : (isingLeapfrogBoxInt west).1 + 1 = (level : Int) := by
    unfold isingLeapfrogBoxInt
    dsimp
    exact_mod_cast hwest
  have hmirror : isingLeapfrogBoxInt east =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt west) := by
    apply Prod.ext
    · dsimp [isingLeapfrogBoxInt, reflectedEndpoint]
      push_cast
      omega
    · dsimp [isingLeapfrogBoxInt, reflectedEndpoint]
      exact_mod_cast hy.symm
  exact reflectedStart_boundary_diffusive_abs_le R level rho west east q hstart
    hmirror hρ hleft hright hbottom htop (by simpa [hy] using hbottom)
      (by simpa [hy] using htop) hqBoundary

theorem isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
    (R level rho : Nat) (south north q : IsingLeapfrogBox R)
    (hsouth : south.2.1 + 1 = level) (hnorth : north.2.1 = level + 1)
    (hx : south.1.1 = north.1.1)
    (hρ : 0 < rho) (hbottom : rho <= level) (htop : level + rho <= R)
    (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
    |isingLeapfrogStoppedKernel R (rho * rho) south q -
        isingLeapfrogStoppedKernel R (rho * rho) north q| <=
      3276 / (rho : Real) ^ 2 := by
  have hs := isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
    R level rho (isingLeapfrogBoxSwap R south) (isingLeapfrogBoxSwap R north)
      (isingLeapfrogBoxSwap R q) hsouth hnorth hx hρ hbottom htop hqVertical
  rw [isingLeapfrogStoppedKernel_swap, isingLeapfrogStoppedKernel_swap] at hs
  exact hs

theorem isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le
    (R level rho : Nat) (south north q : IsingLeapfrogBox R)
    (hsouth : south.2.1 + 1 = level) (hnorth : north.2.1 = level + 1)
    (hx : south.1.1 = north.1.1)
    (hρ : 0 < rho) (hbottom : rho <= level) (htop : level + rho <= R)
    (hleft : rho <= south.1.1) (hright : south.1.1 + rho <= R)
    (hqBoundary : isingLeapfrogBoxBoundary R q) :
    |isingLeapfrogStoppedKernel R (rho * rho) south q -
        isingLeapfrogStoppedKernel R (rho * rho) north q| <=
      10296 / (rho : Real) ^ 2 := by
  have hs := isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le
    R level rho (isingLeapfrogBoxSwap R south) (isingLeapfrogBoxSwap R north)
      (isingLeapfrogBoxSwap R q) hsouth hnorth hx hρ hbottom htop hleft hright
      ((isingLeapfrogBoxBoundary_swap_iff R q).2 hqBoundary)
  rw [isingLeapfrogStoppedKernel_swap, isingLeapfrogStoppedKernel_swap] at hs
  exact hs

private theorem exitKernel_neighbor_timeOffset_abs_le_of_predecessors
    (R t : Nat) (p p' q : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p')
    (hq : isingLeapfrogBoxBoundary R q) (C : Real)
    (hpred :
      |isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogStoppedKernel R t p q| +
      |isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogStoppedKernel R t p q| +
      |isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
          isingLeapfrogStoppedKernel R t p q| +
      |isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
          isingLeapfrogStoppedKernel R t p q| <= C) :
    |isingLeapfrogExitKernel R t p q -
        isingLeapfrogExitKernel R (t + 1) p' q| <= C / 4 := by
  simp only [isingLeapfrogExitKernel, hq, if_true]
  rw [abs_sub_comm,
    isingLeapfrogStoppedKernel_neighbor_timeOffset_eq R t p p' q hp', abs_div]
  norm_num
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have h1 := abs_add_le
    (isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
      isingLeapfrogStoppedKernel R t p q)
    (isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
      isingLeapfrogStoppedKernel R t p q)
  have h2 := abs_add_le
    ((isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
        isingLeapfrogStoppedKernel R t p q) +
      (isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
        isingLeapfrogStoppedKernel R t p q))
    (isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
      isingLeapfrogStoppedKernel R t p q)
  have h3 := abs_add_le
    (((isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogStoppedKernel R t p q) +
        (isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogStoppedKernel R t p q)) +
      (isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
        isingLeapfrogStoppedKernel R t p q))
    (isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
      isingLeapfrogStoppedKernel R t p q)
  linarith



theorem isingLeapfrogExitKernel_neighbor_timeOffset_boundary_diffusive_abs_le
    (R rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hρ : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p')
    (hq : isingLeapfrogBoxBoundary R q) :
    |isingLeapfrogExitKernel R (rho * rho) p q -
        isingLeapfrogExitKernel R (rho * rho + 1) p' q| <=
      6786 / (rho : Real) ^ 2 := by
  have hp'nb : ¬ isingLeapfrogBoxBoundary R p' := by
    unfold isingLeapfrogBoxBoundary
    rcases hp' with ⟨hxLeft, hxRight, hyBottom, hyTop⟩
    omega
  have hp'x0 : 0 < p'.1.1 := lt_of_lt_of_le hρ hp'.1
  have hp'y0 : 0 < p'.2.1 := lt_of_lt_of_le hρ hp'.2.2.1
  let sw := isingLeapfrogSW R p'
  let se := isingLeapfrogSE R p' hp'nb
  let nw := isingLeapfrogNW R p' hp'nb
  let ne := isingLeapfrogNE R p' hp'nb
  let dist : IsingLeapfrogBox R -> IsingLeapfrogBox R -> Real := fun a b =>
    |isingLeapfrogStoppedKernel R (rho * rho) a q -
      isingLeapfrogStoppedKernel R (rho * rho) b q|
  have dist_self (a : IsingLeapfrogBox R) : dist a a = 0 := by simp [dist]
  have dist_symm (a b : IsingLeapfrogBox R) : dist a b = dist b a := by
    exact abs_sub_comm _ _
  have dist_triangle (a b c : IsingLeapfrogBox R) :
      dist a c <= dist a b + dist b c := by
    dsimp [dist]
    have h := abs_add_le
      (isingLeapfrogStoppedKernel R (rho * rho) a q -
        isingLeapfrogStoppedKernel R (rho * rho) b q)
      (isingLeapfrogStoppedKernel R (rho * rho) b q -
        isingLeapfrogStoppedKernel R (rho * rho) c q)
    convert h using 1 <;> ring
  have hneighbors := isingLeapfrogDiagonalAdjacent_eq_neighbor p p' hp'nb hpp'
  have hqSide : (q.1.1 = 0 ∨ q.1.1 = R) ∨
      (q.2.1 = 0 ∨ q.2.1 = R) := by
    unfold isingLeapfrogBoxBoundary at hq
    rcases hq with hx0 | hxR | hy0 | hyR
    · exact Or.inl (Or.inl hx0)
    · exact Or.inl (Or.inr (by omega))
    · exact Or.inr (Or.inl hy0)
    · exact Or.inr (Or.inr (by omega))
  have finish (hsum : dist sw p + dist se p + dist nw p + dist ne p <=
      27144 / (rho : Real) ^ 2) :
      |isingLeapfrogExitKernel R (rho * rho) p q -
          isingLeapfrogExitKernel R (rho * rho + 1) p' q| <=
        6786 / (rho : Real) ^ 2 := by
    have h := exitKernel_neighbor_timeOffset_abs_le_of_predecessors
      R (rho * rho) p p' q hp'nb hq (27144 / (rho : Real) ^ 2) hsum
    exact h.trans_eq (by ring)
  rcases hqSide with hqHorizontal | hqVertical
  · rcases hneighbors with hpSW | hpSE | hpNW | hpNE
    · subst p
      have hA : dist sw se <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho sw se q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogWest]; omega
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogEast]
        · dsimp [sw, se]
          simp [isingLeapfrogSW, isingLeapfrogSE, isingLeapfrogSouth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hB : dist sw nw <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le
          R p'.2.1 rho sw nw q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogSouth]; omega
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogNorth]
        · dsimp [sw, nw]
          simp [isingLeapfrogSW, isingLeapfrogNW, isingLeapfrogWest]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hp.1
        · exact hp.2.1
        · exact hq
      have hD : dist nw ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho nw ne q
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogWest]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogEast]
        · dsimp [nw, ne]
          simp [isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogNorth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hdiag := dist_triangle sw nw ne
      apply finish
      rw [dist_self sw, dist_symm se sw, dist_symm nw sw, dist_symm ne sw]
      calc
        0 + dist sw se + dist sw nw + dist sw ne <=
            0 + 3276 / (rho : Real) ^ 2 + 10296 / (rho : Real) ^ 2 +
              (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) := by
          exact add_le_add (add_le_add (add_le_add (le_refl 0) hA) hB)
            (hdiag.trans (add_le_add hB hD))
        _ = 27144 / (rho : Real) ^ 2 := by ring
    · subst p
      have hA : dist sw se <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho sw se q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogWest]; omega
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogEast]
        · dsimp [sw, se]
          simp [isingLeapfrogSW, isingLeapfrogSE, isingLeapfrogSouth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hC : dist se ne <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le
          R p'.2.1 rho se ne q
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogSouth]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogNorth]
        · dsimp [se, ne]
          simp [isingLeapfrogSE, isingLeapfrogNE, isingLeapfrogEast]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hp.1
        · exact hp.2.1
        · exact hq
      have hD : dist nw ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho nw ne q
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogWest]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogEast]
        · dsimp [nw, ne]
          simp [isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogNorth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hdiag := dist_triangle se ne nw
      apply finish
      rw [dist_self se, dist_symm sw se, dist_symm nw se, dist_symm ne se]
      calc
        dist se sw + 0 + dist se nw + dist se ne <=
            3276 / (rho : Real) ^ 2 + 0 +
              (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) +
              10296 / (rho : Real) ^ 2 := by
          exact add_le_add (add_le_add (add_le_add
            (by simpa [dist_symm] using hA) (le_refl 0))
            (hdiag.trans (add_le_add hC (by simpa [dist_symm] using hD)))) hC
        _ = 27144 / (rho : Real) ^ 2 := by ring
    · subst p
      have hB : dist sw nw <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le
          R p'.2.1 rho sw nw q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogSouth]; omega
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogNorth]
        · dsimp [sw, nw]
          simp [isingLeapfrogSW, isingLeapfrogNW, isingLeapfrogWest]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hp.1
        · exact hp.2.1
        · exact hq
      have hA : dist sw se <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho sw se q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogWest]; omega
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogEast]
        · dsimp [sw, se]
          simp [isingLeapfrogSW, isingLeapfrogSE, isingLeapfrogSouth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hD : dist nw ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho nw ne q
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogWest]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogEast]
        · dsimp [nw, ne]
          simp [isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogNorth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hdiag := dist_triangle nw sw se
      apply finish
      rw [dist_self nw, dist_symm sw nw, dist_symm se nw, dist_symm ne nw]
      calc
        dist nw sw + dist nw se + 0 + dist nw ne <=
            10296 / (rho : Real) ^ 2 +
              (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) + 0 +
              3276 / (rho : Real) ^ 2 := by
          exact add_le_add (add_le_add (add_le_add
            (by simpa [dist_symm] using hB)
            (hdiag.trans (add_le_add (by simpa [dist_symm] using hB) hA)))
              (le_refl 0)) hD
        _ = 27144 / (rho : Real) ^ 2 := by ring
    · subst p
      have hC : dist se ne <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_boundary_diffusive_abs_le
          R p'.2.1 rho se ne q
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogSouth]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogNorth]
        · dsimp [se, ne]
          simp [isingLeapfrogSE, isingLeapfrogNE, isingLeapfrogEast]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hp.1
        · exact hp.2.1
        · exact hq
      have hA : dist sw se <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho sw se q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogWest]; omega
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogEast]
        · dsimp [sw, se]
          simp [isingLeapfrogSW, isingLeapfrogSE, isingLeapfrogSouth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hD : dist nw ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_horizontalEndpoint_diffusive_abs_le
          R p'.1.1 rho nw ne q
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogWest]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogEast]
        · dsimp [nw, ne]
          simp [isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogNorth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hqHorizontal
      have hdiag := dist_triangle ne se sw
      apply finish
      rw [dist_self ne, dist_symm sw ne, dist_symm se ne, dist_symm nw ne]
      calc
        dist ne sw + dist ne se + dist ne nw + 0 <=
            (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) +
              10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2 + 0 := by
          exact add_le_add (add_le_add (add_le_add
            (hdiag.trans (add_le_add (by simpa [dist_symm] using hC)
              (by simpa [dist_symm] using hA)))
            (by simpa [dist_symm] using hC)) (by simpa [dist_symm] using hD))
              (le_refl 0)
        _ = 27144 / (rho : Real) ^ 2 := by ring
  · rcases hneighbors with hpSW | hpSE | hpNW | hpNE
    · subst p
      have hA : dist sw se <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le
          R p'.1.1 rho sw se q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogWest]; omega
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogEast]
        · dsimp [sw, se]
          simp [isingLeapfrogSW, isingLeapfrogSE, isingLeapfrogSouth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hp.2.2.1
        · exact hp.2.2.2
        · exact hq
      have hB : dist sw nw <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho sw nw q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogSouth]; omega
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogNorth]
        · dsimp [sw, nw]
          simp [isingLeapfrogSW, isingLeapfrogNW, isingLeapfrogWest]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hC : dist se ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho se ne q
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogSouth]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogNorth]
        · dsimp [se, ne]
          simp [isingLeapfrogSE, isingLeapfrogNE, isingLeapfrogEast]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hdiag := dist_triangle sw se ne
      apply finish
      rw [dist_self sw, dist_symm se sw, dist_symm nw sw, dist_symm ne sw]
      calc
        0 + dist sw se + dist sw nw + dist sw ne <=
            0 + 10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2 +
              (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) := by
          exact add_le_add (add_le_add (add_le_add (le_refl 0) hA) hB)
            (hdiag.trans (add_le_add hA hC))
        _ = 27144 / (rho : Real) ^ 2 := by ring
    · subst p
      have hA : dist sw se <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le
          R p'.1.1 rho sw se q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogWest]; omega
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogEast]
        · dsimp [sw, se]
          simp [isingLeapfrogSW, isingLeapfrogSE, isingLeapfrogSouth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hp.2.2.1
        · exact hp.2.2.2
        · exact hq
      have hB : dist sw nw <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho sw nw q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogSouth]; omega
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogNorth]
        · dsimp [sw, nw]
          simp [isingLeapfrogSW, isingLeapfrogNW, isingLeapfrogWest]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hC : dist se ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho se ne q
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogSouth]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogNorth]
        · dsimp [se, ne]
          simp [isingLeapfrogSE, isingLeapfrogNE, isingLeapfrogEast]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hdiag := dist_triangle se sw nw
      apply finish
      rw [dist_self se, dist_symm sw se, dist_symm nw se, dist_symm ne se]
      calc
        dist se sw + 0 + dist se nw + dist se ne <=
            10296 / (rho : Real) ^ 2 + 0 +
              (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) +
              3276 / (rho : Real) ^ 2 := by
          exact add_le_add (add_le_add (add_le_add
            (by simpa [dist_symm] using hA) (le_refl 0))
            (hdiag.trans (add_le_add (by simpa [dist_symm] using hA) hB))) hC
        _ = 27144 / (rho : Real) ^ 2 := by ring
    · subst p
      have hD : dist nw ne <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le
          R p'.1.1 rho nw ne q
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogWest]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogEast]
        · dsimp [nw, ne]
          simp [isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogNorth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hp.2.2.1
        · exact hp.2.2.2
        · exact hq
      have hB : dist sw nw <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho sw nw q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogSouth]; omega
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogNorth]
        · dsimp [sw, nw]
          simp [isingLeapfrogSW, isingLeapfrogNW, isingLeapfrogWest]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hC : dist se ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho se ne q
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogSouth]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogNorth]
        · dsimp [se, ne]
          simp [isingLeapfrogSE, isingLeapfrogNE, isingLeapfrogEast]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hdiag := dist_triangle nw ne se
      apply finish
      rw [dist_self nw, dist_symm sw nw, dist_symm se nw, dist_symm ne nw]
      calc
        dist nw sw + dist nw se + 0 + dist nw ne <=
            3276 / (rho : Real) ^ 2 +
              (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) + 0 +
              10296 / (rho : Real) ^ 2 := by
          exact add_le_add (add_le_add (add_le_add (by simpa [dist_symm] using hB)
            (hdiag.trans (add_le_add hD (by simpa [dist_symm] using hC))))
              (le_refl 0)) hD
        _ = 27144 / (rho : Real) ^ 2 := by ring
    · subst p
      have hD : dist nw ne <= 10296 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartX_boundary_diffusive_abs_le
          R p'.1.1 rho nw ne q
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogWest]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogEast]
        · dsimp [nw, ne]
          simp [isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogNorth]
        · exact hρ
        · exact hp'.1
        · exact hp'.2.1
        · exact hp.2.2.1
        · exact hp.2.2.2
        · exact hq
      have hB : dist sw nw <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho sw nw q
        · dsimp [sw]; simp [isingLeapfrogSW, isingLeapfrogSouth]; omega
        · dsimp [nw]; simp [isingLeapfrogNW, isingLeapfrogNorth]
        · dsimp [sw, nw]
          simp [isingLeapfrogSW, isingLeapfrogNW, isingLeapfrogWest]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hC : dist se ne <= 3276 / (rho : Real) ^ 2 := by
        apply isingLeapfrogStoppedKernel_twoApartY_verticalEndpoint_diffusive_abs_le
          R p'.2.1 rho se ne q
        · dsimp [se]; simp [isingLeapfrogSE, isingLeapfrogSouth]; omega
        · dsimp [ne]; simp [isingLeapfrogNE, isingLeapfrogNorth]
        · dsimp [se, ne]
          simp [isingLeapfrogSE, isingLeapfrogNE, isingLeapfrogEast]
        · exact hρ
        · exact hp'.2.2.1
        · exact hp'.2.2.2
        · exact hqVertical
      have hdiag := dist_triangle ne nw sw
      apply finish
      rw [dist_self ne, dist_symm sw ne, dist_symm se ne, dist_symm nw ne]
      calc
        dist ne sw + dist ne se + dist ne nw + 0 <=
            (10296 / (rho : Real) ^ 2 + 3276 / (rho : Real) ^ 2) +
              3276 / (rho : Real) ^ 2 + 10296 / (rho : Real) ^ 2 + 0 := by
          exact add_le_add (add_le_add (add_le_add
            (hdiag.trans (add_le_add (by simpa [dist_symm] using hD)
              (by simpa [dist_symm] using hB)))
            (by simpa [dist_symm] using hC)) (by simpa [dist_symm] using hD))
              (le_refl 0)
        _ = 27144 / (rho : Real) ^ 2 := by ring



theorem isingLeapfrogExitKernel_neighbor_timeOffset_diffusive_abs_le
    (R rho : Nat) (p p' q : IsingLeapfrogBox R)
    (hρ : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    |isingLeapfrogExitKernel R (rho * rho) p q -
        isingLeapfrogExitKernel R (rho * rho + 1) p' q| <=
      6786 / (rho : Real) ^ 2 := by
  by_cases hq : isingLeapfrogBoxBoundary R q
  · exact isingLeapfrogExitKernel_neighbor_timeOffset_boundary_diffusive_abs_le
      R rho p p' q hρ hp hp' hpp' hq
  · simp [isingLeapfrogExitKernel, hq]
    positivity


theorem isingLeapfrogDiffusiveExitInputs_fermionic :
    IsingLeapfrogDiffusiveExitInputs 6786 152 := by
  apply isingLeapfrogDiffusiveExitInputs_of_pointwise 6786 (by norm_num)
  intro R rho p p' hρ hp hp' hpp' q
  exact isingLeapfrogExitKernel_neighbor_timeOffset_diffusive_abs_le
    R rho p p' q hρ hp hp' hpp'


theorem isingLeapfrogDiffusiveGradientBound_fermionic :
    IsingLeapfrogDiffusiveGradientBound 1032080 := by
  convert isingLeapfrogDiffusiveExitInputs_fermionic.gradientBound using 1 <;>
    norm_num



theorem fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le_diffusive
    (n m baseI baseJ R rho : Nat) (hn : 0 < n) (hm : m <= n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p p' : IsingLeapfrogBox R) (hρ : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p -
          fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ p') <=
      (1032080 / (rho : Real) ^ 3) *
        ∑ q, Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ q) := by
  exact
    (fkIsingSquareRadialPatchFullObservableWindow_harmonic
      n m baseI baseJ R hn hm hfitI hfitJ).normSq_sub_le_of_diffusiveGradient
        isingLeapfrogDiffusiveGradientBound_fermionic p p' hρ hp hp' hpp'



theorem fkIsingSquareRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive
    (n m baseI baseJ R rho : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m <= n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh)
    (p p' : IsingLeapfrogBox R) (hρ : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) <=
      (1032080 / (rho : Real) ^ 3) *
        ∑ q, Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ q /
            (Real.sqrt (2 * mesh) : Complex)) := by
  have hsqrt : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrt
  have hraw :=
    fkIsingSquareRadialPatchFullObservableWindow_normSq_sub_le_diffusive
      n m baseI baseJ R rho hn hm hfitI hfitJ p p' hρ hp hp' hpp'
  rw [← sub_div] at ⊢
  rw [hnorm]
  simp_rw [hnorm, ← Finset.sum_div]
  have hden : 0 < 2 * mesh := by positivity
  calc
    _ <= (1032080 / (rho : Real) ^ 3 *
        ∑ q, Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ q)) / (2 * mesh) :=
      div_le_div_of_nonneg_right hraw hden.le
    _ = _ := by ring

end

end StatMech.Universality
