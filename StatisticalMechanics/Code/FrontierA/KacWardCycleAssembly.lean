/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.KacWardForest
import Code.Onsager.GeneralUmlaufsatz
import Mathlib.GroupTheory.Perm.Fin

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open Matrix
open StatMech.Onsager StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.GeneralUmlaufsatz


noncomputable def kwWeightedCycleTransition {E : Type*} [Fintype E]
    [DecidableEq E] (sigma : Equiv.Perm E) (weight : E -> ℂ) :
    Matrix E E ℂ :=
  fun i j => if j = sigma i then weight i else 0




theorem kw_perm_eq_one_or_inv_of_cycle {E : Type*} [Finite E] [Nonempty E]
    (sigma tau : Equiv.Perm E) (hcycle : sigma.IsCycle)
    (hfree : ∀ i, sigma i ≠ i)
    (hchoice : ∀ i, tau i = i ∨ tau i = sigma⁻¹ i) :
    tau = 1 ∨ tau = sigma⁻¹ := by
  by_cases hid : ∀ i, tau i = i
  · left
    ext i
    simpa using hid i
  · right
    push Not at hid
    obtain ⟨a, ha⟩ := hid
    have haStep : tau a = sigma⁻¹ a := (hchoice a).resolve_left ha
    have hinvFree : ∀ i, sigma⁻¹ i ≠ i := by
      intro i hi
      apply hfree i
      calc
        sigma i = sigma (sigma⁻¹ i) := congrArg sigma hi.symm
        _ = i := sigma.apply_symm_apply i
    have hpropagate : ∀ z, tau z = sigma⁻¹ z ->
        tau (sigma⁻¹ z) = sigma⁻¹ (sigma⁻¹ z) := by
      intro z hz
      rcases hchoice (sigma⁻¹ z) with hstay | hstep
      · exfalso
        have := tau.injective (hz.trans hstay.symm)
        exact hinvFree z this.symm
      · exact hstep
    have hiterate : ∀ n : ℕ,
        tau ((sigma⁻¹ ^ n) a) = sigma⁻¹ ((sigma⁻¹ ^ n) a) := by
      intro n
      induction n with
      | zero => simpa using haStep
      | succ n ih => simpa [pow_succ'] using hpropagate _ ih
    ext b
    obtain ⟨n, hn⟩ := hcycle.inv.exists_pow_eq (hinvFree a) (hinvFree b)
    rw [<- hn]
    exact hiterate n


theorem kw_one_sub_weightedCycle_apply {E : Type*} [Fintype E]
    [DecidableEq E] (sigma tau : Equiv.Perm E) (weight : E -> ℂ)
    (hfree : ∀ i, sigma i ≠ i) (i : E) :
    (1 - kwWeightedCycleTransition sigma weight) (tau i) i =
      if tau i = i then 1
      else if tau i = sigma⁻¹ i then -weight (sigma⁻¹ i)
      else 0 := by
  have hinvFree : sigma⁻¹ i ≠ i := by
    intro hi
    apply hfree i
    calc
      sigma i = sigma (sigma⁻¹ i) := congrArg sigma hi.symm
      _ = i := sigma.apply_symm_apply i
  by_cases hti : tau i = i
  · rw [if_pos hti, hti]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      kwWeightedCycleTransition]
    rw [if_neg (hfree i).symm]
    simp
  · by_cases hstep : tau i = sigma⁻¹ i
    · rw [if_neg hti, if_pos hstep, hstep]
      rw [Matrix.sub_apply, Matrix.one_apply_ne hinvFree]
      rw [kwWeightedCycleTransition, if_pos (by simp)]
      simp
    · have hedge : i ≠ sigma (tau i) := by
        intro hedge
        apply hstep
        exact sigma.injective (by simpa using hedge.symm)
      rw [if_neg hti, if_neg hstep]
      rw [Matrix.sub_apply, Matrix.one_apply_ne hti]
      rw [kwWeightedCycleTransition, if_neg hedge]
      simp



theorem kw_det_one_sub_weightedCycle {E : Type*} [Fintype E]
    [DecidableEq E] [Nonempty E]
    (sigma : Equiv.Perm E) (weight : E -> ℂ)
    (hcycle : sigma.IsCycle) (hfree : ∀ i, sigma i ≠ i) :
    (1 - kwWeightedCycleTransition sigma weight).det =
      1 - ∏ i, weight i := by
  rw [Matrix.det_apply]
  have hterm : ∀ tau : Equiv.Perm E,
      Equiv.Perm.sign tau •
          ∏ i, (1 - kwWeightedCycleTransition sigma weight) (tau i) i =
        if tau = 1 then 1
        else if tau = sigma⁻¹ then -(∏ i, weight i)
        else 0 := by
    intro tau
    by_cases hone : tau = 1
    · subst tau
      have hdiag : ∀ i,
          (1 - kwWeightedCycleTransition sigma weight) ((1 : Equiv.Perm E) i) i = 1 := by
        intro i
        rw [kw_one_sub_weightedCycle_apply sigma 1 weight hfree]
        simp
      simp_rw [hdiag]
      simp
    · rw [if_neg hone]
      by_cases hinv : tau = sigma⁻¹
      · subst tau
        rw [if_pos rfl]
        have hinvFree : ∀ i, sigma⁻¹ i ≠ i := by
          intro i hi
          apply hfree i
          calc
            sigma i = sigma (sigma⁻¹ i) := congrArg sigma hi.symm
            _ = i := sigma.apply_symm_apply i
        have hentry : ∀ i,
            (1 - kwWeightedCycleTransition sigma weight) (sigma⁻¹ i) i =
              -weight (sigma⁻¹ i) := by
          intro i
          rw [kw_one_sub_weightedCycle_apply sigma sigma⁻¹ weight hfree]
          rw [if_neg (hinvFree i), if_pos rfl]
        simp_rw [hentry]
        rw [Equiv.Perm.sign_inv, hcycle.sign]
        have hsupport : sigma.support = Finset.univ := by
          ext i
          simp [hfree i]
        rw [hsupport, Finset.card_univ]
        have hprodNeg : (∏ i, -weight (sigma⁻¹ i)) =
            (-1 : ℂ) ^ Fintype.card E * ∏ i, weight i := by
          calc
            (∏ i, -weight (sigma⁻¹ i)) =
                (-1 : ℂ) ^ Fintype.card E * ∏ i, weight (sigma⁻¹ i) := by
              simpa using Finset.prod_neg (s := (Finset.univ : Finset E))
                (fun i => weight (sigma⁻¹ i))
            _ = (-1 : ℂ) ^ Fintype.card E * ∏ i, weight i := by
              rw [Equiv.prod_comp sigma⁻¹ weight]
        rw [hprodNeg]
        rw [Units.neg_smul]
        congr 1
        rw [Units.smul_def, <- Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
        simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
          Int.cast_pow, Int.cast_neg, Int.cast_one]
        calc
          (-1 : ℂ) ^ Fintype.card E *
              ((-1 : ℂ) ^ Fintype.card E * ∏ i, weight i) =
              (((-1 : ℂ) ^ Fintype.card E) *
                ((-1 : ℂ) ^ Fintype.card E)) * ∏ i, weight i := by ring
          _ = (((-1 : ℂ) * (-1)) ^ Fintype.card E) * ∏ i, weight i := by
            rw [mul_pow]
          _ = ∏ i, weight i := by norm_num
      · rw [if_neg hinv]
        have hnotChoice : ¬ ∀ i, tau i = i ∨ tau i = sigma⁻¹ i := by
          intro hc
          rcases kw_perm_eq_one_or_inv_of_cycle sigma tau hcycle hfree hc with h | h
          · exact hone h
          · exact hinv h
        push Not at hnotChoice
        obtain ⟨i, hne, hneInv⟩ := hnotChoice
        have hzero :
            (1 - kwWeightedCycleTransition sigma weight) (tau i) i = 0 := by
          rw [kw_one_sub_weightedCycle_apply sigma tau weight hfree]
          rw [if_neg hne, if_neg hneInv]
        have hprodZero :
            (∏ j, (1 - kwWeightedCycleTransition sigma weight) (tau j) j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) hzero
        rw [hprodZero, smul_zero]
  simp_rw [hterm]
  have hsigmaNeOne : sigma ≠ 1 := by
    intro h
    exact hfree (Classical.choice inferInstance) (by simp [h])
  have honeNeInv : (1 : Equiv.Perm E) ≠ sigma⁻¹ := by
    intro h
    have hsigma : sigma = 1 := by
      rw [<- inv_inv sigma, <- h]
      simp
    exact hfree (Classical.choice inferInstance) (by simp [hsigma])
  let f : Equiv.Perm E -> ℂ := fun tau =>
    if tau = 1 then 1
    else if tau = sigma⁻¹ then -(∏ i, weight i)
    else 0
  change ∑ tau, f tau = 1 - ∏ i, weight i
  rw [Finset.sum_eq_add_sum_diff_singleton (i := (1 : Equiv.Perm E))
    (f := f) (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ \ {(1 : Equiv.Perm E)})
    (i := sigma⁻¹) (f := f) (by simp [hsigmaNeOne])]
  have hrest : ∑ tau ∈ (Finset.univ \ {(1 : Equiv.Perm E)}) \ {sigma⁻¹}, f tau = 0 := by
    apply Finset.sum_eq_zero
    intro tau htau
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
      true_and] at htau
    simp [f, htau.1, htau.2]
  rw [hrest]
  dsimp [f]
  rw [if_pos rfl, if_neg honeNeInv.symm, if_pos rfl]
  ring






noncomputable def kwTwoOrientationCycleTransition
    {E : Type*} [Fintype E] [DecidableEq E]
    (sigma : Equiv.Perm E) (weight : Bool -> E -> ℂ) :
    Matrix (E × Bool) (E × Bool) ℂ :=
  Matrix.blockDiagonal fun b => kwWeightedCycleTransition sigma (weight b)



theorem kw_det_twoOrientationCycle {E : Type*} [Fintype E]
    [DecidableEq E] [Nonempty E]
    (sigma : Equiv.Perm E) (weight : Bool -> E -> ℂ)
    (hcycle : sigma.IsCycle) (hfree : ∀ i, sigma i ≠ i) :
    (1 - kwTwoOrientationCycleTransition sigma weight).det =
      (1 - ∏ i, weight false i) * (1 - ∏ i, weight true i) := by
  have hone : (1 : Matrix (E × Bool) (E × Bool) ℂ) =
      Matrix.blockDiagonal (fun _ : Bool => (1 : Matrix E E ℂ)) :=
    Matrix.blockDiagonal_one.symm
  rw [hone, kwTwoOrientationCycleTransition, <- Matrix.blockDiagonal_sub,
    Matrix.det_blockDiagonal]
  calc
    _ = ∏ b : Bool, (1 - ∏ i, weight b i) := by
      apply Finset.prod_congr rfl
      intro b _
      simpa using kw_det_one_sub_weightedCycle sigma (weight b) hcycle hfree
    _ = _ := by rw [Fintype.prod_bool]; ring



noncomputable def kwAbstractCycleEvenPolynomial
    {E : Type*} [Fintype E] (edgeWeight : E -> ℂ) : ℂ :=
  1 + ∏ i, edgeWeight i







theorem kacWard_abstract_cycle_of_phase_sign
    {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    (sigma : Equiv.Perm E) (edgeWeight : E -> ℂ)
    (phase : Bool -> E -> ℂ)
    (hcycle : sigma.IsCycle) (hfree : ∀ i, sigma i ≠ i)
    (hphase : ∀ b, ∏ i, phase b i = -1) :
    (1 - kwTwoOrientationCycleTransition sigma
        (fun b i => edgeWeight i * phase b i)).det =
      (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
  rw [kw_det_twoOrientationCycle sigma _ hcycle hfree]
  have hweight : ∀ b,
      ∏ i, edgeWeight i * phase b i = -(∏ i, edgeWeight i) := by
    intro b
    rw [Finset.prod_mul_distrib, hphase b]
    ring
  rw [hweight false, hweight true]
  unfold kwAbstractCycleEvenPolynomial
  ring





theorem kw_finRotate_free {n : ℕ} (hn : 2 ≤ n) :
    ∀ i : Fin n, finRotate n i ≠ i := by
  have hsupport := support_finRotate_of_le hn
  intro i
  exact Equiv.Perm.mem_support.mp (by rw [hsupport]; exact Finset.mem_univ i)





theorem kacWard_rectilinear_cycle
    {n : ℕ} [NeZero n]
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (d : Fin n -> Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hn : 3 ≤ n) (hnu : ∀ i, d (i + 1) ≠ d i + 2)
    (edgeWeight : Fin n -> ℂ) :
    (1 - kwTwoOrientationCycleTransition (finRotate n)
        (fun _ i => edgeWeight i * ons_turnW omega (d i) (d (i + 1)))).det =
      (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
  apply kacWard_abstract_cycle_of_phase_sign
      (finRotate n) edgeWeight
      (fun _ i => ons_turnW omega (d i) (d (i + 1)))
  · exact isCycle_finRotate_of_le (by omega)
  · exact kw_finRotate_free (by omega)
  · intro _
    exact turnWeightProduct_eq_neg_one omega homega hI d
      hclosed hsimple hn hnu

end StatMech.FrontierA
