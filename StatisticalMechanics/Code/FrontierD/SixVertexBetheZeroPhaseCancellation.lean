/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheZeroPhasePerturbation

open Finset

namespace StatMech.FrontierD

noncomputable section


def sixVertexBethePerturbedWordTerm
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) (sigma : Equiv.Perm (Fin (n + 1))) :
    Complex :=
  sixVertexBetheAmplitude c p sigma *
    sixVertexBetheWordCoefficient c
      (fun j => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps j)) sigma w *
    sixVertexBetheWordMonomial N
      (fun j => sixVertexBethePhase
        (sixVertexBethePerturbRoot p ell eps j)) sigma x w

theorem sixVertexBetheAmplitude_perturbedWordCoefficient_adjacent_cancel
    {c : Real} (hc : 2 < c) {n : Nat} (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real)
    (sigma : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) (i : Fin n)
    (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (ha : sigma i.castSucc ≠ ell) (hb : sigma i.succ ≠ ell)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    sixVertexBetheAmplitude c p
        (sigma * Equiv.swap i.castSucc i.succ) *
        sixVertexBetheWordCoefficient c
          (fun j => sixVertexBethePhase
            (sixVertexBethePerturbRoot p ell eps j))
          (sigma * Equiv.swap i.castSucc i.succ) w =
      -(sixVertexBetheAmplitude c p sigma *
        sixVertexBetheWordCoefficient c
          (fun j => sixVertexBethePhase
            (sixVertexBethePerturbRoot p ell eps j)) sigma w) := by
  let z : Fin (n + 1) → Complex := fun j => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps j)
  have hrem := sixVertexBetheWordCoefficientRemainder_adjacent_invariant
    c z sigma w i hiM hiL
  rw [sixVertexBetheWordCoefficient_eq_ML_mul_remainder c z _ w i hiM hiL,
    sixVertexBetheWordCoefficient_eq_ML_mul_remainder c z sigma w i hiM hiL]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  rw [hrem]
  have hza : z (sigma i.castSucc) =
      sixVertexBethePhase (p (sigma i.castSucc)) := by
    simp [z, sixVertexBethePerturbRoot, ha]
  have hzb : z (sigma i.succ) =
      sixVertexBethePhase (p (sigma i.succ)) := by
    simp [z, sixVertexBethePerturbRoot, hb]
  have hlocal := sixVertexBetheAmplitude_adjacent_ML_cancel hc p sigma i
    (hphase _ ha) (hphase _ hb)
  rw [hza, hzb]
  calc
    _ = (sixVertexBetheAmplitude c p
          (sigma * Equiv.swap i.castSucc i.succ) *
        (sixVertexBetheM c (sixVertexBethePhase (p (sigma i.succ))) *
          sixVertexBetheL c
            (sixVertexBethePhase (p (sigma i.castSucc))) - 1)) *
        sixVertexBetheWordCoefficientRemainder c z sigma w i.castSucc := by
          ring
    _ = (-sixVertexBetheAmplitude c p sigma *
        (sixVertexBetheM c
            (sixVertexBethePhase (p (sigma i.castSucc))) *
          sixVertexBetheL c (sixVertexBethePhase (p (sigma i.succ))) - 1)) *
        sixVertexBetheWordCoefficientRemainder c z sigma w i.castSucc := by
          rw [hlocal]
    _ = _ := by ring



theorem sixVertexBethePerturbedWordTerm_adjacent_cancel
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) (i : Fin n)
    (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (sigma : Equiv.Perm (Fin (n + 1)))
    (ha : sigma i.castSucc ≠ ell) (hb : sigma i.succ ≠ ell) :
    sixVertexBethePerturbedWordTerm N c p ell eps x w
        (sigma * Equiv.swap i.castSucc i.succ) =
      -sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
  unfold sixVertexBethePerturbedWordTerm
  rw [sixVertexBetheWordMonomial_adjacent_invariant
    (fun j => sixVertexBethePhase
      (sixVertexBethePerturbRoot p ell eps j)) sigma x w i hiM hiL]
  rw [sixVertexBetheAmplitude_perturbedWordCoefficient_adjacent_cancel
    hc p ell eps sigma w i hiM hiL ha hb hphase]
  ring



theorem sum_sixVertexBethePerturbedWordTerm_adjacent_away_zero_eq_zero
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) (i : Fin n)
    (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)) with
        sigma i.castSucc ≠ ell ∧ sigma i.succ ≠ ell,
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  let tau := Equiv.swap i.castSucc i.succ
  let good : Equiv.Perm (Fin (n + 1)) → Prop := fun sigma =>
    sigma i.castSucc ≠ ell ∧ sigma i.succ ≠ ell
  let F : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
    if good sigma then
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
    else 0
  have hsum : (∑ sigma, F sigma) = 0 := by
    apply sum_perm_eq_zero_of_swap_neg i.castSucc i.succ
    intro sigma
    have hgood : good (sigma * tau) ↔ good sigma := by
      simp [good, tau, Equiv.Perm.mul_apply, and_comm]
    by_cases hsigma : good sigma
    · have hswap : good (sigma * tau) := hgood.mpr hsigma
      rw [show F (sigma * tau) =
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * tau) by simp [F, hswap],
        show F sigma =
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma by
            simp [F, hsigma]]
      exact sixVertexBethePerturbedWordTerm_adjacent_cancel
        hc p ell eps x w i hiM hiL hphase sigma hsigma.1 hsigma.2
    · have hswap : ¬ good (sigma * tau) := by
        simpa [hgood] using hsigma
      rw [show F (sigma * Equiv.swap i.castSucc i.succ) = 0 by
          apply if_neg
          simpa [tau] using hswap,
        show F sigma = 0 by simp [F, hsigma]]
      simp
  rw [Finset.sum_filter]
  simpa [F, good] using hsum



theorem sixVertexBethePerturbedWordTerm_boundary_cancel
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (haM : Fin.last (n + 1) ∉ w) (hbL : (0 : Fin (n + 2)) ∈ w)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (sigma : Equiv.Perm (Fin (n + 2)))
    (ha : sigma (Fin.last (n + 1)) ≠ ell) (hb : sigma 0 ≠ ell) :
    sixVertexBethePerturbedWordTerm N c p ell eps x w
        (sigma * Equiv.swap (Fin.last (n + 1)) 0) =
      -sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
  let z : Fin (n + 2) → Complex := fun j => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps j)
  let a : Fin (n + 2) := Fin.last (n + 1)
  let tau : Equiv.Perm (Fin (n + 2)) :=
    (finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2)
  have hrot : finRotate (n + 2) a = 0 := by
    apply Fin.ext
    simp [a]
  have htau : tau = Equiv.swap a 0 := by
    simpa [tau, a] using sixVertexBetheBoundaryPermutation_eq_swap n
  have hza : z (sigma a) = sixVertexBethePhase (p (sigma a)) := by
    simp [z, sixVertexBethePerturbRoot, a, ha]
  have hzb : z (sigma 0) = sixVertexBethePhase (p (sigma 0)) := by
    simp [z, sixVertexBethePerturbRoot, hb]
  let B : Equiv.Perm (Fin (n + 2)) → Complex := fun rho =>
    sixVertexBetheWordCoefficientRemainder c z rho w a *
      sixVertexBetheWordMonomial N z rho x w
  have hB (rho : Equiv.Perm (Fin (n + 2)))
      (hra : rho a ≠ ell) (hrb : rho 0 ≠ ell) :
      sixVertexBethePhase (p (rho a)) ^ N * B (rho * tau) =
        sixVertexBethePhase (p (rho 0)) ^ N * B rho := by
    have hrem := sixVertexBetheWordCoefficientRemainder_swap_invariant
      c z rho w haM hbL hrot
    have hmon := sixVertexBetheWordMonomial_boundary_covariant (N := N)
      z (fun j => Complex.exp_ne_zero _) rho x w haM hbL
    have hzra : z (rho a) = sixVertexBethePhase (p (rho a)) := by
      simp [z, sixVertexBethePerturbRoot, hra]
    have hzrb : z (rho 0) = sixVertexBethePhase (p (rho 0)) := by
      simp [z, sixVertexBethePerturbRoot, hrb]
    dsimp [B]
    rw [htau, hrem]
    calc
      sixVertexBethePhase (p (rho a)) ^ N *
          (sixVertexBetheWordCoefficientRemainder c z rho w a *
            sixVertexBetheWordMonomial N z
              (rho * Equiv.swap a 0) x w) =
        sixVertexBetheWordCoefficientRemainder c z rho w a *
          (z (rho a) ^ N * sixVertexBetheWordMonomial N z
            (rho * Equiv.swap a 0) x w) := by rw [hzra]; ring
      _ = sixVertexBetheWordCoefficientRemainder c z rho w a *
          (z (rho 0) ^ N *
            sixVertexBetheWordMonomial N z rho x w) := by rw [hmon]
      _ = _ := by rw [hzrb]; ring
  have hlocal := sixVertexBetheAmplitude_boundary_ML_cancel
    hc p hp sigma B (hphase _ ha) (hphase _ hb) (hB sigma ha hb)
  change sixVertexBetheAmplitude c p (sigma * tau) *
      (sixVertexBetheM c (sixVertexBethePhase (p (sigma 0))) *
        sixVertexBetheL c
          (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) - 1) *
      B (sigma * tau) =
    -sixVertexBetheAmplitude c p sigma *
      (sixVertexBetheM c
          (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) *
        sixVertexBetheL c (sixVertexBethePhase (p (sigma 0))) - 1) *
      B sigma at hlocal
  have htau' : tau = Equiv.swap (Fin.last (n + 1)) 0 := by
    simpa [a] using htau
  unfold sixVertexBethePerturbedWordTerm
  change sixVertexBetheAmplitude c p (sigma * Equiv.swap a 0) *
      sixVertexBetheWordCoefficient c z (sigma * Equiv.swap a 0) w *
        sixVertexBetheWordMonomial N z (sigma * Equiv.swap a 0) x w = _
  rw [sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder
      c z (sigma * Equiv.swap a 0) w haM hbL hrot,
    sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder
      c z sigma w haM hbL hrot]
  dsimp only [a] at hza ha hlocal ⊢
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  rw [hza, hzb]
  calc
    _ = sixVertexBetheAmplitude c p
          (sigma * Equiv.swap (Fin.last (n + 1)) 0) *
        (sixVertexBetheM c (sixVertexBethePhase (p (sigma 0))) *
          sixVertexBetheL c
            (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) - 1) *
        B (sigma * Equiv.swap (Fin.last (n + 1)) 0) := by
          dsimp [B, a]
          ring
    _ = -(sixVertexBetheAmplitude c p sigma *
        (sixVertexBetheM c
            (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) *
          sixVertexBetheL c (sixVertexBethePhase (p (sigma 0))) - 1) *
        B sigma) := by
          rw [← htau']
          simpa only [neg_mul] using hlocal
    _ = _ := by
      dsimp [B, a]
      ring



theorem sum_sixVertexBethePerturbedWordTerm_boundary_away_zero_eq_zero
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (haM : Fin.last (n + 1) ∉ w) (hbL : (0 : Fin (n + 2)) ∈ w)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 2)) with
        sigma (Fin.last (n + 1)) ≠ ell ∧ sigma 0 ≠ ell,
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  let a : Fin (n + 2) := Fin.last (n + 1)
  let tau := Equiv.swap a 0
  let good : Equiv.Perm (Fin (n + 2)) → Prop := fun sigma =>
    sigma a ≠ ell ∧ sigma 0 ≠ ell
  let F : Equiv.Perm (Fin (n + 2)) → Complex := fun sigma =>
    if good sigma then
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
    else 0
  have hsum : (∑ sigma, F sigma) = 0 := by
    apply sum_perm_eq_zero_of_swap_neg a 0
    intro sigma
    have hgood : good (sigma * tau) ↔ good sigma := by
      simp [good, tau, Equiv.Perm.mul_apply, and_comm]
    by_cases hsigma : good sigma
    · have hswap : good (sigma * tau) := hgood.mpr hsigma
      rw [show F (sigma * tau) =
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * tau) by simp [F, hswap],
        show F sigma =
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma by
            simp [F, hsigma]]
      exact sixVertexBethePerturbedWordTerm_boundary_cancel
        hc p hp ell eps x w haM hbL hphase sigma hsigma.1 hsigma.2
    · have hswap : ¬ good (sigma * tau) := by
        simpa [hgood] using hsigma
      rw [show F (sigma * tau) = 0 by
          apply if_neg
          simpa using hswap,
        show F sigma = 0 by simp [F, hsigma]]
      simp
  rw [Finset.sum_filter]
  simpa [F, good, a] using hsum


def sixVertexBetheMLBoundarySet {n : Nat}
    (w : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => i ∉ w ∧ finRotate (n + 1) i ∈ w

theorem mem_sixVertexBetheMLBoundarySet {n : Nat}
    (w : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    i ∈ sixVertexBetheMLBoundarySet w ↔
      i ∉ w ∧ finRotate (n + 1) i ∈ w := by
  simp [sixVertexBetheMLBoundarySet]



theorem exists_sixVertexBetheMLBoundary_away_of_one_lt_card
    {n : Nat} (w : Finset (Fin (n + 1)))
    (hcard : 1 < (sixVertexBetheMLBoundarySet w).card)
    (a : Fin (n + 1)) :
    ∃ i ∈ sixVertexBetheMLBoundarySet w,
      i ≠ a ∧ finRotate (n + 1) i ≠ a := by
  let b := (finRotate (n + 1)).symm a
  by_cases hb : b ∈ sixVertexBetheMLBoundarySet w
  · obtain ⟨i, hi, hib⟩ :=
      (sixVertexBetheMLBoundarySet w).exists_mem_ne hcard b
    refine ⟨i, hi, ?_, ?_⟩
    · intro hia
      subst i
      have hb' := (mem_sixVertexBetheMLBoundarySet w b).mp hb
      have ha' := (mem_sixVertexBetheMLBoundarySet w a).mp hi
      exact ha'.1 (by simpa [b] using hb'.2)
    · intro hrot
      apply hib
      apply (finRotate (n + 1)).injective
      simpa [b] using hrot
  · obtain ⟨i, hi, hia⟩ :=
      (sixVertexBetheMLBoundarySet w).exists_mem_ne hcard a
    refine ⟨i, hi, hia, ?_⟩
    intro hrot
    apply hb
    have : i = b := by
      apply (finRotate (n + 1)).injective
      simpa [b] using hrot
    simpa [this] using hi



theorem sum_sixVertexBethePerturbedWordTerm_adjacent_fixed_zeroSlot_eq_zero
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) (i : Fin n)
    (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (a : Fin (n + 1)) (ha : a ≠ i.castSucc) (hb : a ≠ i.succ)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell,
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  let tau := Equiv.swap i.castSucc i.succ
  let F : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
    if sigma a = ell then
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
    else 0
  have hsum : (∑ sigma, F sigma) = 0 := by
    apply sum_perm_eq_zero_of_swap_neg i.castSucc i.succ
    intro sigma
    have hfix : (sigma * tau) a = sigma a := by
      simp [tau, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne ha hb]
    by_cases hsigma : sigma a = ell
    · have hswap : (sigma * tau) a = ell := hfix.trans hsigma
      have hleft : sigma i.castSucc ≠ ell := by
        intro h
        exact ha (sigma.injective (hsigma.trans h.symm))
      have hright : sigma i.succ ≠ ell := by
        intro h
        exact hb (sigma.injective (hsigma.trans h.symm))
      rw [show F (sigma * tau) =
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * tau) by simp [F, hswap],
        show F sigma =
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma by
            simp [F, hsigma]]
      exact sixVertexBethePerturbedWordTerm_adjacent_cancel
        hc p ell eps x w i hiM hiL hphase sigma hleft hright
    · have hswap : (sigma * tau) a ≠ ell := by
        rw [hfix]
        exact hsigma
      rw [show F (sigma * tau) = 0 by
          apply if_neg
          exact hswap,
        show F sigma = 0 by simp [F, hsigma]]
      simp
  rw [Finset.sum_filter]
  simpa [F] using hsum



theorem sum_sixVertexBethePerturbedWordTerm_boundary_fixed_zeroSlot_eq_zero
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (hlastM : Fin.last (n + 1) ∉ w) (hzeroL : (0 : Fin (n + 2)) ∈ w)
    (a : Fin (n + 2)) (ha : a ≠ Fin.last (n + 1)) (hb : a ≠ 0)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma a = ell,
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  let tau := Equiv.swap (Fin.last (n + 1)) 0
  let F : Equiv.Perm (Fin (n + 2)) → Complex := fun sigma =>
    if sigma a = ell then
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
    else 0
  have hsum : (∑ sigma, F sigma) = 0 := by
    apply sum_perm_eq_zero_of_swap_neg (Fin.last (n + 1)) 0
    intro sigma
    have hfix : (sigma * tau) a = sigma a := by
      simp [tau, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne ha hb]
    by_cases hsigma : sigma a = ell
    · have hswap : (sigma * tau) a = ell := hfix.trans hsigma
      have hleft : sigma (Fin.last (n + 1)) ≠ ell := by
        intro h
        exact ha (sigma.injective (hsigma.trans h.symm))
      have hright : sigma 0 ≠ ell := by
        intro h
        exact hb (sigma.injective (hsigma.trans h.symm))
      rw [show F (sigma * tau) =
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * tau) by simp [F, hswap],
        show F sigma =
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma by
            simp [F, hsigma]]
      exact sixVertexBethePerturbedWordTerm_boundary_cancel
        hc p hp ell eps x w hlastM hzeroL hphase sigma hleft hright
    · have hswap : (sigma * tau) a ≠ ell := by
        rw [hfix]
        exact hsigma
      rw [show F (sigma * tau) = 0 by
          apply if_neg
          exact hswap,
        show F sigma = 0 by simp [F, hsigma]]
      simp
  rw [Finset.sum_filter]
  simpa [F] using hsum



theorem sum_sixVertexBethePerturbedWordTerm_eq_sum_fixed_zeroSlot
    {N n : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) =
      ∑ a : Fin (n + 1),
        ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell,
        sixVertexBethePerturbedWordTerm N c p ell eps x w sigma := by
  symm
  calc
    (∑ a : Fin (n + 1),
        ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell,
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) =
      ∑ a : Fin (n + 1), ∑ sigma : Equiv.Perm (Fin (n + 1)),
        if sigma a = ell then
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
        else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_filter]
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)), ∑ a : Fin (n + 1),
        if sigma a = ell then
          sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
        else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      have hiff (a : Fin (n + 1)) : sigma a = ell ↔
          a = sigma.symm ell := by
        constructor
        · intro h
          exact sigma.injective
            (h.trans (sigma.apply_symm_apply ell).symm)
        · rintro rfl
          exact sigma.apply_symm_apply ell
      simp only [hiff]
      simp



theorem sum_sixVertexBethePerturbedWordTerm_eq_zero_of_multiple_ML
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (hcard : 1 < (sixVertexBetheMLBoundarySet w).card)
    (hphase : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 2)),
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = 0 := by
  rw [sum_sixVertexBethePerturbedWordTerm_eq_sum_fixed_zeroSlot]
  apply Finset.sum_eq_zero
  intro a hauniv
  obtain ⟨i, hi, hia, hirot⟩ :=
    exists_sixVertexBetheMLBoundary_away_of_one_lt_card w hcard a
  have hiML := (mem_sixVertexBetheMLBoundarySet w i).mp hi
  by_cases hilast : i = Fin.last (n + 1)
  · subst i
    apply sum_sixVertexBethePerturbedWordTerm_boundary_fixed_zeroSlot_eq_zero
      hc p hp ell eps x w hiML.1
    · simpa using hiML.2
    · exact Ne.symm hia
    · exact Ne.symm (by simpa using hirot)
    · exact hphase
  · have hival : i.val < n + 1 := by
      have hle : i.val ≤ n + 1 := by omega
      have hne : i.val ≠ n + 1 := by
        intro h
        apply hilast
        apply Fin.ext
        simpa using h
      omega
    let j : Fin (n + 1) := ⟨i.val, hival⟩
    have hjcast : j.castSucc = i := by
      apply Fin.ext
      rfl
    have hjrot : finRotate (n + 2) i = j.succ := by
      apply Fin.ext
      rw [coe_finRotate_of_ne_last hilast]
      rfl
    apply sum_sixVertexBethePerturbedWordTerm_adjacent_fixed_zeroSlot_eq_zero
      hc p ell eps x w j
    · simpa [hjcast] using hiML.1
    · simpa [hjrot] using hiML.2
    · intro h
      exact hia (hjcast.symm.trans h.symm)
    · intro h
      exact hirot (hjrot.trans h.symm)
    · exact hphase

end

end StatMech.FrontierD
