/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicStoppedCoupling









namespace StatMech.Universality

open Finset
open IsingDiagonalWalkHitSplit

noncomputable section


def isingLeapfrogBoxSwap (R : Nat) (p : IsingLeapfrogBox R) :
    IsingLeapfrogBox R :=
  (p.2, p.1)

@[simp] theorem isingLeapfrogBoxSwap_involutive (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxSwap R (isingLeapfrogBoxSwap R p) = p := rfl

@[simp] theorem isingLeapfrogBoxSwap_eq_iff (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogBoxSwap R p = isingLeapfrogBoxSwap R q ↔ p = q :=
  (Function.Involutive.injective
    (isingLeapfrogBoxSwap_involutive R)).eq_iff

def isingLeapfrogBoxSwapEquiv (R : Nat) :
    IsingLeapfrogBox R ≃ IsingLeapfrogBox R where
  toFun := isingLeapfrogBoxSwap R
  invFun := isingLeapfrogBoxSwap R
  left_inv := isingLeapfrogBoxSwap_involutive R
  right_inv := isingLeapfrogBoxSwap_involutive R

theorem isingLeapfrogBoxBoundary_swap_iff (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxBoundary R (isingLeapfrogBoxSwap R p) ↔
      isingLeapfrogBoxBoundary R p := by
  unfold isingLeapfrogBoxBoundary isingLeapfrogBoxSwap
  tauto

private theorem isingLeapfrogBoxSwap_SW (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxSwap R (isingLeapfrogSW R p) =
      isingLeapfrogSW R (isingLeapfrogBoxSwap R p) := rfl

private theorem isingLeapfrogBoxSwap_SE (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxSwap R (isingLeapfrogSE R p hp) =
      isingLeapfrogNW R (isingLeapfrogBoxSwap R p)
        (mt (isingLeapfrogBoxBoundary_swap_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [isingLeapfrogBoxSwap, isingLeapfrogSE, isingLeapfrogNW,
      isingLeapfrogEast, isingLeapfrogNorth, isingLeapfrogSouth,
      isingLeapfrogWest]

private theorem isingLeapfrogBoxSwap_NW (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxSwap R (isingLeapfrogNW R p hp) =
      isingLeapfrogSE R (isingLeapfrogBoxSwap R p)
        (mt (isingLeapfrogBoxBoundary_swap_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [isingLeapfrogBoxSwap, isingLeapfrogSE, isingLeapfrogNW,
      isingLeapfrogEast, isingLeapfrogNorth, isingLeapfrogSouth,
      isingLeapfrogWest]

private theorem isingLeapfrogBoxSwap_NE (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxSwap R (isingLeapfrogNE R p hp) =
      isingLeapfrogNE R (isingLeapfrogBoxSwap R p)
        (mt (isingLeapfrogBoxBoundary_swap_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [isingLeapfrogBoxSwap, isingLeapfrogNE, isingLeapfrogEast,
      isingLeapfrogNorth]


theorem isingLeapfrogStoppedKernel_swap (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t (isingLeapfrogBoxSwap R p)
        (isingLeapfrogBoxSwap R q) =
      isingLeapfrogStoppedKernel R t p q := by
  induction t generalizing p with
  | zero => simp [isingLeapfrogStoppedKernel]
  | succ t ih =>
      by_cases hp : isingLeapfrogBoxBoundary R p
      · have hps := (isingLeapfrogBoxBoundary_swap_iff R p).2 hp
        simp only [isingLeapfrogStoppedKernel, dif_pos hp, dif_pos hps]
        exact ih p
      · have hps : ¬ isingLeapfrogBoxBoundary R
            (isingLeapfrogBoxSwap R p) :=
          mt (isingLeapfrogBoxBoundary_swap_iff R p).mp hp
        simp only [isingLeapfrogStoppedKernel, dif_neg hp, dif_neg hps]
        rw [← isingLeapfrogBoxSwap_SW R p,
          ← isingLeapfrogBoxSwap_NW R p hp,
          ← isingLeapfrogBoxSwap_SE R p hp,
          ← isingLeapfrogBoxSwap_NE R p hp]
        rw [ih, ih, ih, ih]
        ring

theorem isingLeapfrogBoxInt_swap (R : Nat) (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxInt (isingLeapfrogBoxSwap R p) =
      ((isingLeapfrogBoxInt p).2, (isingLeapfrogBoxInt p).1) := rfl


theorem isingLeapfrogStoppedKernel_reflectedStartY_diffusive_l1_le
    (R level rho : Nat) (p p' : IsingLeapfrogBox R)
    (hstart : (isingLeapfrogBoxInt p).2 + 1 = level)
    (hmirror : isingLeapfrogBoxInt p' =
      ((isingLeapfrogBoxInt p).1,
        2 * (level : Int) - (isingLeapfrogBoxInt p).2))
    (hρ : 0 < rho) (hbottom : rho ≤ level) (htop : level + rho ≤ R)
    (hleft : rho ≤ p.1.1) (hright : p.1.1 + rho ≤ R) :
    (∑ q : IsingLeapfrogBox R,
      |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q|) ≤
      76 / (rho : Real) := by
  let ps := isingLeapfrogBoxSwap R p
  let ps' := isingLeapfrogBoxSwap R p'
  have hsStart : (isingLeapfrogBoxInt ps).1 + 1 = level := by
    simpa [ps, isingLeapfrogBoxInt_swap] using hstart
  have hsMirror : isingLeapfrogBoxInt ps' =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt ps) := by
    rw [isingLeapfrogBoxInt_swap, isingLeapfrogBoxInt_swap, hmirror]
    simp [ps, ps', reflectedEndpoint]
  have hs := isingLeapfrogStoppedKernel_reflectedStart_diffusive_l1_le
    R level rho ps ps' hsStart hsMirror hρ hbottom htop hleft hright
  have hreindex := (isingLeapfrogBoxSwapEquiv R).sum_comp
    (fun q : IsingLeapfrogBox R =>
      |isingLeapfrogStoppedKernel R (rho * rho) p q -
        isingLeapfrogStoppedKernel R (rho * rho) p' q|)
  rw [← hreindex]
  apply le_trans _ hs
  apply Finset.sum_le_sum
  intro q hq
  have hpSwap := isingLeapfrogStoppedKernel_swap R (rho * rho) p
    (isingLeapfrogBoxSwap R q)
  have hp'Swap := isingLeapfrogStoppedKernel_swap R (rho * rho) p'
    (isingLeapfrogBoxSwap R q)
  simp only [isingLeapfrogBoxSwap_involutive] at hpSwap hp'Swap
  change |isingLeapfrogStoppedKernel R (rho * rho) p
      (isingLeapfrogBoxSwap R q) -
    isingLeapfrogStoppedKernel R (rho * rho) p'
      (isingLeapfrogBoxSwap R q)| ≤
    |isingLeapfrogStoppedKernel R (rho * rho) ps q -
      isingLeapfrogStoppedKernel R (rho * rho) ps' q|
  rw [show isingLeapfrogStoppedKernel R (rho * rho) ps q =
      isingLeapfrogStoppedKernel R (rho * rho) p
        (isingLeapfrogBoxSwap R q) by simpa [ps] using hpSwap,
    show isingLeapfrogStoppedKernel R (rho * rho) ps' q =
      isingLeapfrogStoppedKernel R (rho * rho) p'
        (isingLeapfrogBoxSwap R q) by simpa [ps'] using hp'Swap]


theorem isingLeapfrogStoppedKernel_l1_le_two (R t t' : Nat)
    (p p' : IsingLeapfrogBox R) :
    (∑ q, |isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t' p' q|) ≤ 2 := by
  calc
    _ ≤ ∑ q, (isingLeapfrogStoppedKernel R t p q +
        isingLeapfrogStoppedKernel R t' p' q) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_sub_le_iff]
      constructor
      · linarith [isingLeapfrogStoppedKernel_nonneg R t' p' q]
      · linarith [isingLeapfrogStoppedKernel_nonneg R t p q]
    _ = 2 := by
      rw [Finset.sum_add_distrib,
        isingLeapfrogStoppedKernel_sum_eq_one,
        isingLeapfrogStoppedKernel_sum_eq_one]
      norm_num


theorem isingLeapfrogStoppedKernel_l1_triangle (R t : Nat)
    (p p' p'' : IsingLeapfrogBox R) :
    (∑ q, |isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t p'' q|) ≤
      (∑ q, |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t p' q|) +
      ∑ q, |isingLeapfrogStoppedKernel R t p' q -
        isingLeapfrogStoppedKernel R t p'' q| := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  have h := abs_add_le
    (isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t p' q)
    (isingLeapfrogStoppedKernel R t p' q -
      isingLeapfrogStoppedKernel R t p'' q)
  convert h using 1 <;> ring



theorem isingLeapfrogStoppedKernel_twoApartX_diffusive_l1_le
    (R level rho : Nat) (west east : IsingLeapfrogBox R)
    (hwest : west.1.1 + 1 = level) (heast : east.1.1 = level + 1)
    (hy : west.2.1 = east.2.1)
    (hρ : 0 < rho) (hleft : rho ≤ level) (hright : level + rho ≤ R)
    (hbottom : rho ≤ west.2.1) (htop : west.2.1 + rho ≤ R) :
    (∑ q, |isingLeapfrogStoppedKernel R (rho * rho) west q -
      isingLeapfrogStoppedKernel R (rho * rho) east q|) ≤
      76 / (rho : Real) := by
  have hmirror : isingLeapfrogBoxInt east =
      reflectedEndpoint (level : Int) (isingLeapfrogBoxInt west) := by
    apply Prod.ext
    · dsimp [isingLeapfrogBoxInt, reflectedEndpoint]
      push_cast
      omega
    · dsimp [isingLeapfrogBoxInt, reflectedEndpoint]
      exact_mod_cast hy.symm
  have hstart : (isingLeapfrogBoxInt west).1 + 1 = (level : Int) := by
    change (west.1.1 : Int) + 1 = (level : Int)
    exact_mod_cast hwest
  exact isingLeapfrogStoppedKernel_reflectedStart_diffusive_l1_le
    R level rho west east hstart hmirror hρ hleft hright
      hbottom htop



theorem isingLeapfrogStoppedKernel_twoApartY_diffusive_l1_le
    (R level rho : Nat) (south north : IsingLeapfrogBox R)
    (hsouth : south.2.1 + 1 = level) (hnorth : north.2.1 = level + 1)
    (hx : south.1.1 = north.1.1)
    (hρ : 0 < rho) (hbottom : rho ≤ level) (htop : level + rho ≤ R)
    (hleft : rho ≤ south.1.1) (hright : south.1.1 + rho ≤ R) :
    (∑ q, |isingLeapfrogStoppedKernel R (rho * rho) south q -
      isingLeapfrogStoppedKernel R (rho * rho) north q|) ≤
      76 / (rho : Real) := by
  have hmirror : isingLeapfrogBoxInt north =
      ((isingLeapfrogBoxInt south).1,
        2 * (level : Int) - (isingLeapfrogBoxInt south).2) := by
    apply Prod.ext
    · dsimp [isingLeapfrogBoxInt]
      exact_mod_cast hx.symm
    · dsimp [isingLeapfrogBoxInt]
      push_cast
      omega
  have hstart : (isingLeapfrogBoxInt south).2 + 1 = (level : Int) := by
    change (south.2.1 : Int) + 1 = (level : Int)
    exact_mod_cast hsouth
  exact isingLeapfrogStoppedKernel_reflectedStartY_diffusive_l1_le
    R level rho south north hstart hmirror hρ hbottom htop
      hleft hright


theorem isingLeapfrogStoppedKernel_twoApartX_later_l1_le
    (R t level radius : Nat) (west east : IsingLeapfrogBox R)
    (ht : radius * radius ≤ t)
    (hwest : west.1.1 + 1 = level) (heast : east.1.1 = level + 1)
    (hy : west.2.1 = east.2.1)
    (hradius : 0 < radius) (hleft : radius ≤ level)
    (hright : level + radius ≤ R)
    (hbottom : radius ≤ west.2.1) (htop : west.2.1 + radius ≤ R) :
    (∑ q, |isingLeapfrogStoppedKernel R t west q -
      isingLeapfrogStoppedKernel R t east q|) ≤
      76 / (radius : Real) := by
  have hcontract := isingLeapfrogStoppedKernel_l1_add_le R
    (radius * radius) (radius * radius) (t - radius * radius) west east
  rw [Nat.add_sub_of_le ht] at hcontract
  exact le_trans hcontract
    (isingLeapfrogStoppedKernel_twoApartX_diffusive_l1_le R level radius
      west east hwest heast hy hradius hleft hright hbottom htop)


theorem isingLeapfrogStoppedKernel_twoApartY_later_l1_le
    (R t level radius : Nat) (south north : IsingLeapfrogBox R)
    (ht : radius * radius ≤ t)
    (hsouth : south.2.1 + 1 = level) (hnorth : north.2.1 = level + 1)
    (hx : south.1.1 = north.1.1)
    (hradius : 0 < radius) (hbottom : radius ≤ level)
    (htop : level + radius ≤ R)
    (hleft : radius ≤ south.1.1) (hright : south.1.1 + radius ≤ R) :
    (∑ q, |isingLeapfrogStoppedKernel R t south q -
      isingLeapfrogStoppedKernel R t north q|) ≤
      76 / (radius : Real) := by
  have hcontract := isingLeapfrogStoppedKernel_l1_add_le R
    (radius * radius) (radius * radius) (t - radius * radius) south north
  rw [Nat.add_sub_of_le ht] at hcontract
  exact le_trans hcontract
    (isingLeapfrogStoppedKernel_twoApartY_diffusive_l1_le R level radius
      south north hsouth hnorth hx hradius hbottom htop hleft hright)



theorem isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors
    (R t : Nat) (p p' : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p') (C : Real)
    (hpred :
      (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
        isingLeapfrogStoppedKernel R t p q|) +
      (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
        isingLeapfrogStoppedKernel R t p q|) +
      (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
        isingLeapfrogStoppedKernel R t p q|) +
      (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
        isingLeapfrogStoppedKernel R t p q|) ≤ C) :
    (∑ q, |isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R (t + 1) p' q|) ≤ C / 4 := by
  have hpoint (q : IsingLeapfrogBox R) :
      |isingLeapfrogStoppedKernel R (t + 1) p' q -
          isingLeapfrogStoppedKernel R t p q| ≤
        (|isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
            isingLeapfrogStoppedKernel R t p q| +
          |isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
            isingLeapfrogStoppedKernel R t p q| +
          |isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
            isingLeapfrogStoppedKernel R t p q| +
          |isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
            isingLeapfrogStoppedKernel R t p q|) / 4 := by
    rw [isingLeapfrogStoppedKernel_neighbor_timeOffset_eq R t p p' q hp',
      abs_div]
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
  calc
    _ = ∑ q, |isingLeapfrogStoppedKernel R (t + 1) p' q -
        isingLeapfrogStoppedKernel R t p q| := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [abs_sub_comm]
    _ ≤ ∑ q,
        (|isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
            isingLeapfrogStoppedKernel R t p q| +
          |isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
            isingLeapfrogStoppedKernel R t p q| +
          |isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
            isingLeapfrogStoppedKernel R t p q| +
          |isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
            isingLeapfrogStoppedKernel R t p q|) / 4 :=
      Finset.sum_le_sum (fun q _ => hpoint q)
    _ = ((∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
            isingLeapfrogStoppedKernel R t p q|) +
          (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
            isingLeapfrogStoppedKernel R t p q|) +
          (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
            isingLeapfrogStoppedKernel R t p q|) +
          (∑ q, |isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
            isingLeapfrogStoppedKernel R t p q|)) / 4 := by
      rw [← Finset.sum_div]
      repeat' rw [Finset.sum_add_distrib]
    _ ≤ C / 4 := div_le_div_of_nonneg_right hpred (by norm_num)




theorem isingLeapfrogStoppedKernel_neighbor_timeOffset_diffusive_l1_le
    (R rho : Nat) (p p' : IsingLeapfrogBox R)
    (hρ : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    (∑ q, |isingLeapfrogStoppedKernel R (rho * rho) p q -
      isingLeapfrogStoppedKernel R (rho * rho + 1) p' q|) ≤
      152 / (rho : Real) := by
  by_cases hsmall : rho = 1
  · subst rho
    have htwo := isingLeapfrogStoppedKernel_l1_le_two R 1 2 p p'
    norm_num at htwo ⊢
    exact le_trans htwo (by norm_num)
  have htwo : 2 ≤ rho := by omega
  let radius := rho - 1
  have hradius : 0 < radius := by simp [radius]; omega
  have htime : radius * radius ≤ rho * rho := by
    exact Nat.mul_le_mul (Nat.sub_le rho 1) (Nat.sub_le rho 1)
  rcases hp' with ⟨hxLeft, hxRight, hyBottom, hyTop⟩
  have hp'nb : ¬ isingLeapfrogBoxBoundary R p' := by
    unfold isingLeapfrogBoxBoundary
    omega
  let sw := isingLeapfrogSW R p'
  let se := isingLeapfrogSE R p' hp'nb
  let nw := isingLeapfrogNW R p' hp'nb
  let ne := isingLeapfrogNE R p' hp'nb
  let dist : IsingLeapfrogBox R → IsingLeapfrogBox R → Real :=
    fun a b => ∑ q, |isingLeapfrogStoppedKernel R (rho * rho) a q -
      isingLeapfrogStoppedKernel R (rho * rho) b q|
  have dist_self (a : IsingLeapfrogBox R) : dist a a = 0 := by
    simp [dist]
  have dist_symm (a b : IsingLeapfrogBox R) : dist a b = dist b a := by
    apply Finset.sum_congr rfl
    intro q hq
    exact abs_sub_comm _ _
  have dist_triangle (a b c : IsingLeapfrogBox R) :
      dist a c ≤ dist a b + dist b c := by
    simpa [dist] using isingLeapfrogStoppedKernel_l1_triangle
      R (rho * rho) a b c
  have hA : dist sw se ≤ 76 / (radius : Real) := by
    apply isingLeapfrogStoppedKernel_twoApartX_later_l1_le
      R (rho * rho) p'.1.1 radius sw se htime
    · dsimp [sw]
      simp [isingLeapfrogSW, isingLeapfrogWest]
      omega
    · dsimp [se]
      simp [isingLeapfrogSE, isingLeapfrogEast]
    · dsimp [sw, se]
      simp [isingLeapfrogSW, isingLeapfrogSE, isingLeapfrogSouth]
    · exact hradius
    · dsimp [radius]
      omega
    · dsimp [radius]
      omega
    · dsimp [radius, sw]
      simp [isingLeapfrogSW, isingLeapfrogSouth]
      omega
    · dsimp [radius, sw]
      simp [isingLeapfrogSW, isingLeapfrogSouth]
      omega
  have hB : dist sw nw ≤ 76 / (radius : Real) := by
    apply isingLeapfrogStoppedKernel_twoApartY_later_l1_le
      R (rho * rho) p'.2.1 radius sw nw htime
    · dsimp [sw]
      simp [isingLeapfrogSW, isingLeapfrogSouth]
      omega
    · dsimp [nw]
      simp [isingLeapfrogNW, isingLeapfrogNorth]
    · dsimp [sw, nw]
      simp [isingLeapfrogSW, isingLeapfrogNW, isingLeapfrogWest]
    · exact hradius
    · dsimp [radius]
      omega
    · dsimp [radius]
      omega
    · dsimp [radius, sw]
      simp [isingLeapfrogSW, isingLeapfrogWest]
      omega
    · dsimp [radius, sw]
      simp [isingLeapfrogSW, isingLeapfrogWest]
      omega
  have hC : dist se ne ≤ 76 / (radius : Real) := by
    apply isingLeapfrogStoppedKernel_twoApartY_later_l1_le
      R (rho * rho) p'.2.1 radius se ne htime
    · dsimp [se]
      simp [isingLeapfrogSE, isingLeapfrogSouth]
      omega
    · dsimp [ne]
      simp [isingLeapfrogNE, isingLeapfrogNorth]
    · dsimp [se, ne]
      simp [isingLeapfrogSE, isingLeapfrogNE, isingLeapfrogEast]
    · exact hradius
    · dsimp [radius]
      omega
    · dsimp [radius]
      omega
    · dsimp [radius, se]
      simp [isingLeapfrogSE, isingLeapfrogEast]
      omega
    · dsimp [radius, se]
      simp [isingLeapfrogSE, isingLeapfrogEast]
      omega
  have hD : dist nw ne ≤ 76 / (radius : Real) := by
    apply isingLeapfrogStoppedKernel_twoApartX_later_l1_le
      R (rho * rho) p'.1.1 radius nw ne htime
    · dsimp [nw]
      simp [isingLeapfrogNW, isingLeapfrogWest]
      omega
    · dsimp [ne]
      simp [isingLeapfrogNE, isingLeapfrogEast]
    · dsimp [nw, ne]
      simp [isingLeapfrogNW, isingLeapfrogNE, isingLeapfrogNorth]
    · exact hradius
    · dsimp [radius]
      omega
    · dsimp [radius]
      omega
    · dsimp [radius, nw]
      simp [isingLeapfrogNW, isingLeapfrogNorth]
      omega
    · dsimp [radius, nw]
      simp [isingLeapfrogNW, isingLeapfrogNorth]
      omega
  have hscale : 304 / (radius : Real) ≤ 608 / (rho : Real) := by
    have hradiusReal : (0 : Real) < radius := by positivity
    have hρReal : (0 : Real) < rho := by positivity
    apply (div_le_div_iff₀ hradiusReal hρReal).2
    have hradiusCast : (radius : Real) = (rho : Real) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hradiusCast]
    have htwoReal : (2 : Real) ≤ rho := by exact_mod_cast htwo
    nlinarith
  have hneighbors := isingLeapfrogDiagonalAdjacent_eq_neighbor p p' hp'nb hpp'
  rcases hneighbors with hpSW | hpSE | hpNW | hpNE
  · subst p
    apply le_trans
      (isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors
        R (rho * rho) sw p' hp'nb (608 / (rho : Real)) ?_)
    · ring_nf
      exact le_rfl
    · change dist sw sw + dist se sw + dist nw sw + dist ne sw ≤
          608 / (rho : Real)
      have hA' : dist se sw ≤ 76 / (radius : Real) := by
        rw [dist_symm]
        exact hA
      have hB' : dist nw sw ≤ 76 / (radius : Real) := by
        rw [dist_symm]
        exact hB
      have hC' : dist ne se ≤ 76 / (radius : Real) := by
        rw [dist_symm]
        exact hC
      have hdiag := dist_triangle ne se sw
      have hdiagBound : dist ne sw ≤
          76 / (radius : Real) + 76 / (radius : Real) :=
        le_trans hdiag (add_le_add hC' hA')
      have hsum : dist sw sw + dist se sw + dist nw sw + dist ne sw ≤
          304 / (radius : Real) := by
        calc
          _ ≤ 0 + 76 / (radius : Real) + 76 / (radius : Real) +
              (76 / (radius : Real) + 76 / (radius : Real)) :=
            add_le_add (add_le_add (add_le_add
              (le_of_eq (dist_self sw)) hA') hB') hdiagBound
          _ = _ := by ring
      exact le_trans hsum hscale
  · subst p
    apply le_trans
      (isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors
        R (rho * rho) se p' hp'nb (608 / (rho : Real)) ?_)
    · ring_nf
      exact le_rfl
    · change dist sw se + dist se se + dist nw se + dist ne se ≤
          608 / (rho : Real)
      have hB' : dist nw sw ≤ 76 / (radius : Real) := by
        rw [dist_symm]
        exact hB
      have hC' : dist ne se ≤ 76 / (radius : Real) := by
        rw [dist_symm]
        exact hC
      have hdiag := dist_triangle nw sw se
      have hdiagBound : dist nw se ≤
          76 / (radius : Real) + 76 / (radius : Real) :=
        le_trans hdiag (add_le_add hB' hA)
      have hsum : dist sw se + dist se se + dist nw se + dist ne se ≤
          304 / (radius : Real) := by
        calc
          _ ≤ 76 / (radius : Real) + 0 +
              (76 / (radius : Real) + 76 / (radius : Real)) +
              76 / (radius : Real) :=
            add_le_add (add_le_add (add_le_add hA
              (le_of_eq (dist_self se))) hdiagBound) hC'
          _ = _ := by ring
      exact le_trans hsum hscale
  · subst p
    apply le_trans
      (isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors
        R (rho * rho) nw p' hp'nb (608 / (rho : Real)) ?_)
    · ring_nf
      exact le_rfl
    · change dist sw nw + dist se nw + dist nw nw + dist ne nw ≤
          608 / (rho : Real)
      have hA' : dist se sw ≤ 76 / (radius : Real) := by
        rw [dist_symm]
        exact hA
      have hD' : dist ne nw ≤ 76 / (radius : Real) := by
        rw [dist_symm]
        exact hD
      have hdiag := dist_triangle se sw nw
      have hdiagBound : dist se nw ≤
          76 / (radius : Real) + 76 / (radius : Real) :=
        le_trans hdiag (add_le_add hA' hB)
      have hsum : dist sw nw + dist se nw + dist nw nw + dist ne nw ≤
          304 / (radius : Real) := by
        calc
          _ ≤ 76 / (radius : Real) +
              (76 / (radius : Real) + 76 / (radius : Real)) + 0 +
              76 / (radius : Real) :=
            add_le_add (add_le_add (add_le_add hB hdiagBound)
              (le_of_eq (dist_self nw))) hD'
          _ = _ := by ring
      exact le_trans hsum hscale
  · subst p
    apply le_trans
      (isingLeapfrogStoppedKernel_neighbor_timeOffset_l1_le_of_predecessors
        R (rho * rho) ne p' hp'nb (608 / (rho : Real)) ?_)
    · ring_nf
      exact le_rfl
    · change dist sw ne + dist se ne + dist nw ne + dist ne ne ≤
          608 / (rho : Real)
      have hdiag := dist_triangle sw se ne
      have hdiagBound : dist sw ne ≤
          76 / (radius : Real) + 76 / (radius : Real) :=
        le_trans hdiag (add_le_add hA hC)
      have hsum : dist sw ne + dist se ne + dist nw ne + dist ne ne ≤
          304 / (radius : Real) := by
        calc
          _ ≤ (76 / (radius : Real) + 76 / (radius : Real)) +
              76 / (radius : Real) + 76 / (radius : Real) + 0 :=
            add_le_add (add_le_add (add_le_add hdiagBound hC) hD)
              (le_of_eq (dist_self ne))
          _ = _ := by ring
      exact le_trans hsum hscale

end

end StatMech.Universality
