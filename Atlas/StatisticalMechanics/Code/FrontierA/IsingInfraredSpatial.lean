/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingInfraredReduction
import Code.FrontierA.IsingTorusDissemination
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

open Finset
open scoped BigOperators ComplexConjugate

namespace StatMech.FrontierA

variable {Gamma : Type*} [Fintype Gamma] [AddCommGroup Gamma]

private theorem addChar_apply_mul_conj_apply
    (chi : AddChar Gamma Complex) (x y : Gamma) :
    chi y * conj (chi x) = chi (y - x) := by
  rw [← AddChar.inv_apply_eq_conj, AddChar.map_sub_eq_div]
  rfl



theorem finiteTorusFourierCoeff_sum_mul_conj
    (G : Gamma → Real) (x : Gamma) :
    (∑ chi : AddChar Gamma Complex,
        finiteTorusFourierCoeff G chi * conj (chi x)) =
      Fintype.card Gamma * G x := by
  classical
  unfold finiteTorusFourierCoeff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y : Gamma, ∑ chi : AddChar Gamma Complex,
        ((G y : Complex) * chi y) * conj (chi x)) =
        ∑ y : Gamma, (G y : Complex) *
          ∑ chi : AddChar Gamma Complex, chi (y - x) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      rw [mul_assoc, addChar_apply_mul_conj_apply]
    _ = ∑ y : Gamma, (G y : Complex) *
          (if y = x then Fintype.card Gamma else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [AddChar.sum_apply_eq_ite]
      simp only [sub_eq_zero]
      split_ifs <;> simp
    _ = Fintype.card Gamma * G x := by
      simp
      ring


theorem finiteTorus_fourier_inversion
    (G : Gamma → Real) (x : Gamma) :
    (G x : Complex) =
      (1 / Fintype.card Gamma : Complex) *
        ∑ chi : AddChar Gamma Complex,
          finiteTorusFourierCoeff G chi * conj (chi x) := by
  rw [finiteTorusFourierCoeff_sum_mul_conj]
  have hcard : (Fintype.card Gamma : Complex) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp



theorem finiteTorus_fourier_difference
    (G : Gamma → Real) (x y : Gamma) :
    ((G x - G y : Real) : Complex) =
      (1 / Fintype.card Gamma : Complex) *
        ∑ chi : AddChar Gamma Complex,
          finiteTorusFourierCoeff G chi *
            (conj (chi x) - conj (chi y)) := by
  push_cast
  rw [finiteTorus_fourier_inversion G x,
    finiteTorus_fourier_inversion G y]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  ring

theorem finiteTorus_fourier_difference_trivial_term_zero
    (G : Gamma → Real) (x y : Gamma) :
    finiteTorusFourierCoeff G (0 : AddChar Gamma Complex) *
        (conj ((0 : AddChar Gamma Complex) x) -
          conj ((0 : AddChar Gamma Complex) y)) = 0 := by
  simp


theorem finiteTorus_fourier_difference_erase_zero
    (G : Gamma → Real) (x y : Gamma) :
    ((G x - G y : Real) : Complex) =
      (1 / Fintype.card Gamma : Complex) *
        ∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)),
          finiteTorusFourierCoeff G chi *
            (conj (chi x) - conj (chi y)) := by
  rw [finiteTorus_fourier_difference G x y]
  rw [← Finset.sum_erase (s := Finset.univ)
    (f := fun chi : AddChar Gamma Complex =>
      finiteTorusFourierCoeff G chi *
        (conj (chi x) - conj (chi y))) (a := 0)
    (finiteTorus_fourier_difference_trivial_term_zero G x y)]



theorem finiteTorus_fourier_difference_abs_le
    (G : Gamma → Real) (dispersion : AddChar Gamma Complex → Real)
    (C : Real) (x y : Gamma)
    (hbound : ∀ chi : AddChar Gamma Complex, chi ≠ 0 →
      ‖finiteTorusFourierCoeff G chi‖ ≤ C / dispersion chi) :
    |G x - G y| ≤
      (1 / Fintype.card Gamma : Real) *
        ∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)),
          (C / dispersion chi) * ‖conj (chi x) - conj (chi y)‖ := by
  classical
  have hcardNat : 0 < Fintype.card Gamma := Fintype.card_pos
  have hcardReal : (0 : Real) < Fintype.card Gamma := by exact_mod_cast hcardNat
  have hcardComplex : (Fintype.card Gamma : Complex) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hinvNorm : ‖(1 / Fintype.card Gamma : Complex)‖ =
      (1 / Fintype.card Gamma : Real) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  calc
    |G x - G y| = ‖((G x - G y : Real) : Complex)‖ := by
      rw [Complex.norm_real]
      rfl
    _ = ‖(1 / Fintype.card Gamma : Complex) *
        ∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)),
          finiteTorusFourierCoeff G chi *
            (conj (chi x) - conj (chi y))‖ := by
      rw [finiteTorus_fourier_difference_erase_zero G x y]
    _ = (1 / Fintype.card Gamma : Real) *
        ‖∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)),
          finiteTorusFourierCoeff G chi *
            (conj (chi x) - conj (chi y))‖ := by
      rw [norm_mul, hinvNorm]
    _ ≤ (1 / Fintype.card Gamma : Real) *
        ∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)),
          ‖finiteTorusFourierCoeff G chi *
            (conj (chi x) - conj (chi y))‖ := by
      apply mul_le_mul_of_nonneg_left
        (norm_sum_le _ _)
      exact (one_div_nonneg.mpr hcardReal.le)
    _ ≤ (1 / Fintype.card Gamma : Real) *
        ∑ chi ∈ (Finset.univ.erase (0 : AddChar Gamma Complex)),
          (C / dispersion chi) * ‖conj (chi x) - conj (chi y)‖ := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hcardReal.le)
      apply Finset.sum_le_sum
      intro chi hchi
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right
        (hbound chi (Finset.ne_of_mem_erase hchi)) (norm_nonneg _)



private theorem isingTorus_eq_sum_val_nsmul_step
    {d k : Nat} (x : IsingDyadicTorus d k) :
    x = ∑ i : Fin d, (x i).val • isingTorusStep i := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  calc
    x j = ((x j).val : ZMod (2 ^ (k + 2))) :=
      (ZMod.natCast_zmod_val (x j)).symm
    _ = ∑ i : Fin d, (x i).val • isingTorusStep i j := by
      rw [Finset.sum_eq_single j]
      · simp [isingTorusStep]
      · intro i _ hij
        simp [isingTorusStep, hij]
      · simp



theorem isingTorusCharacterDispersion_pos_of_ne_zero
    {d k : Nat} (chi : AddChar (IsingDyadicTorus d k) Complex)
    (hchi : chi ≠ 0) :
    0 < isingTorusCharacterDispersion chi := by
  have hexists : ∃ i : Fin d, chi (isingTorusStep i) ≠ 1 := by
    by_contra hnone
    push_neg at hnone
    apply hchi
    ext x
    rw [isingTorus_eq_sum_val_nsmul_step x]
    change chi (∑ i : Fin d, (x i).val • isingTorusStep i) = 1
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his, AddChar.map_add_eq_mul, ih,
          AddChar.map_nsmul_eq_pow, hnone, one_pow, one_mul]
  obtain ⟨i, hi⟩ := hexists
  have hterm : 0 < Complex.normSq (1 - chi (isingTorusStep i)) := by
    rw [Complex.normSq_pos]
    exact sub_ne_zero.mpr hi.symm
  unfold isingTorusCharacterDispersion
  have hle := Finset.single_le_sum
    (fun j _ => Complex.normSq_nonneg (1 - chi (isingTorusStep j)))
    (Finset.mem_univ i)
  exact hterm.trans_le hle

theorem isingTorusAveragedTwoPoint_fourierCoeff_norm_le
    {d k : Nat} (beta : Real) (hbeta : 0 < beta)
    (chi : AddChar (IsingDyadicTorus d k) Complex) (hchi : chi ≠ 0) :
    ‖finiteTorusFourierCoeff
        (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi‖ ≤
      (1 / beta) / isingTorusCharacterDispersion chi := by
  have hdisp := isingTorusCharacterDispersion_pos_of_ne_zero chi hchi
  have hb := isingTorusAveragedTwoPoint_fourier_bound beta hbeta
    (isingTorus_gaussianDominated beta hbeta.le) chi hdisp
  have hreal := finiteTorusFourierCoeff_isingTorusAveragedTwoPoint beta chi
  have hnorm :
      ‖finiteTorusFourierCoeff
          (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi‖ =
        |(finiteTorusFourierCoeff
          (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re| := by
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    rfl
  rw [hnorm, abs_of_nonneg hb.1]
  calc
    (finiteTorusFourierCoeff
        (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re ≤
        1 / (beta * isingTorusCharacterDispersion chi) := hb.2
    _ = (1 / beta) / isingTorusCharacterDispersion chi := by ring



theorem isingTorusAveragedTwoPoint_difference_abs_le
    {d k : Nat} (beta : Real) (hbeta : 0 < beta)
    (x y : IsingDyadicTorus d k) :
    |isingTorusAveragedTwoPoint beta x -
        isingTorusAveragedTwoPoint beta y| ≤
      (1 / Fintype.card (IsingDyadicTorus d k) : Real) *
        ∑ chi ∈ (Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex)),
          ((1 / beta) / isingTorusCharacterDispersion chi) *
            ‖conj (chi x) - conj (chi y)‖ := by
  exact finiteTorus_fourier_difference_abs_le
    (isingTorusAveragedTwoPoint (d := d) (k := k) beta)
    isingTorusCharacterDispersion (1 / beta) x y
    (isingTorusAveragedTwoPoint_fourierCoeff_norm_le beta hbeta)

end StatMech.FrontierA
