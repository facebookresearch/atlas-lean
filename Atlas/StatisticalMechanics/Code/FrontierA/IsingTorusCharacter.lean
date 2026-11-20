/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.IsingTorusGaussianDomination
import Code.FrontierA.IsingInfraredReduction
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

open Finset
open scoped BigOperators ComplexConjugate

namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusCharacterDispersion
    (chi : AddChar (IsingDyadicTorus d k) Complex) : Real :=
  ∑ i : Fin d, Complex.normSq (1 - chi (isingTorusStep i))

theorem isingTorusCharacterDispersion_nonneg
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    0 ≤ isingTorusCharacterDispersion chi := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem character_edge_normSq
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (x : IsingDyadicTorus d k) (i : Fin d) :
    Complex.normSq (chi x - chi (x + isingTorusStep i)) =
      Complex.normSq (1 - chi (isingTorusStep i)) := by
  rw [AddChar.map_add_eq_mul]
  rw [show chi x - chi x * chi (isingTorusStep i) =
      chi x * (1 - chi (isingTorusStep i)) by ring,
    Complex.normSq_mul]
  rw [Complex.normSq_eq_norm_sq, AddChar.norm_apply, one_pow, one_mul]



theorem isingTorusDirichlet_re_add_im_addChar
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichlet (fun x => (chi x).re) +
        isingTorusDirichlet (fun x => (chi x).im) =
      Fintype.card (IsingDyadicTorus d k) *
        isingTorusCharacterDispersion chi := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  rw [← Finset.sum_add_distrib]
  calc
    ∑ x : IsingDyadicTorus d k,
        ((∑ i : Fin d,
            ((chi x).re - (chi (x + isingTorusStep i)).re) *
              ((chi x).re - (chi (x + isingTorusStep i)).re)) +
          ∑ i : Fin d,
            ((chi x).im - (chi (x + isingTorusStep i)).im) *
              ((chi x).im - (chi (x + isingTorusStep i)).im)) =
        ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
          Complex.normSq (chi x - chi (x + isingTorusStep i)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    _ = ∑ _x : IsingDyadicTorus d k, ∑ i : Fin d,
          Complex.normSq (1 - chi (isingTorusStep i)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro i _
      exact character_edge_normSq chi x i
    _ = Fintype.card (IsingDyadicTorus d k) *
          isingTorusCharacterDispersion chi := by
      simp [isingTorusCharacterDispersion]


noncomputable def isingTorusDirichletBilinearComplex
    (u : IsingDyadicTorus d k → Real)
    (v : IsingDyadicTorus d k → Complex) : Complex :=
  ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
    (u x - u (x + isingTorusStep i)) *
      (v x - v (x + isingTorusStep i))

theorem isingTorusDirichletBilinearComplex_re
    (u : IsingDyadicTorus d k → Real)
    (v : IsingDyadicTorus d k → Complex) :
    (isingTorusDirichletBilinearComplex u v).re =
      isingTorusDirichletBilinear u (fun x => (v x).re) := by
  unfold isingTorusDirichletBilinearComplex isingTorusDirichletBilinear
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re]

theorem isingTorusDirichletBilinearComplex_im
    (u : IsingDyadicTorus d k → Real)
    (v : IsingDyadicTorus d k → Complex) :
    (isingTorusDirichletBilinearComplex u v).im =
      isingTorusDirichletBilinear u (fun x => (v x).im) := by
  unfold isingTorusDirichletBilinearComplex isingTorusDirichletBilinear
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_im]

private theorem character_laplacian
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (x : IsingDyadicTorus d k) (i : Fin d) :
    2 * chi x - chi (x + isingTorusStep i) -
        chi (x - isingTorusStep i) =
      (Complex.normSq (1 - chi (isingTorusStep i)) : Complex) * chi x := by
  rw [AddChar.map_add_eq_mul, AddChar.map_sub_eq_div]
  rw [Complex.normSq_eq_conj_mul_self, map_sub, map_one,
    ← AddChar.inv_apply_eq_conj]
  have hne : chi (isingTorusStep i) ≠ 0 := by
    intro hzero
    have hnorm := AddChar.norm_apply chi (isingTorusStep i)
    simp [hzero] at hnorm
  field_simp
  ring

private theorem sum_shift_character_edge
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) (i : Fin d) :
    (∑ x : IsingDyadicTorus d k,
        (u (x + isingTorusStep i) : Complex) *
          (chi x - chi (x + isingTorusStep i))) =
      ∑ x : IsingDyadicTorus d k, (u x : Complex) *
        (chi (x - isingTorusStep i) - chi x) := by
  let e : IsingDyadicTorus d k ≃ IsingDyadicTorus d k :=
    Equiv.addRight (-isingTorusStep i)
  calc
    (∑ x : IsingDyadicTorus d k,
        (u (x + isingTorusStep i) : Complex) *
          (chi x - chi (x + isingTorusStep i))) =
      ∑ x : IsingDyadicTorus d k,
        ((u ((e x) + isingTorusStep i) : Complex) *
          (chi (e x) - chi ((e x) + isingTorusStep i))) := by
        exact (e.sum_comp (fun x =>
          (u (x + isingTorusStep i) : Complex) *
            (chi x - chi (x + isingTorusStep i)))).symm
    _ = ∑ x : IsingDyadicTorus d k, (u x : Complex) *
        (chi (x - isingTorusStep i) - chi x) := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [e]
      simp [sub_eq_add_neg, add_assoc]



theorem isingTorusDirichletBilinearComplex_addChar
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichletBilinearComplex u chi =
      (isingTorusCharacterDispersion chi : Complex) *
        ∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x := by
  unfold isingTorusDirichletBilinearComplex
  rw [Finset.sum_comm]
  calc
    ∑ i : Fin d, ∑ x : IsingDyadicTorus d k,
        ((u x : Complex) - u (x + isingTorusStep i)) *
          (chi x - chi (x + isingTorusStep i)) =
      ∑ i : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x : Complex) *
          (2 * chi x - chi (x + isingTorusStep i) -
            chi (x - isingTorusStep i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, sum_shift_character_edge u chi i]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ i : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x : Complex) *
          ((Complex.normSq (1 - chi (isingTorusStep i)) : Complex) * chi x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      rw [character_laplacian chi x i]
    _ = (isingTorusCharacterDispersion chi : Complex) *
        ∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x := by
      simp only [isingTorusCharacterDispersion, Complex.ofReal_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem isingTorusDirichletBilinear_re_addChar
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichletBilinear u (fun x => (chi x).re) =
      isingTorusCharacterDispersion chi *
        (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x).re := by
  rw [← isingTorusDirichletBilinearComplex_re u chi,
    isingTorusDirichletBilinearComplex_addChar]
  simp

theorem isingTorusDirichletBilinear_im_addChar
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    isingTorusDirichletBilinear u (fun x => (chi x).im) =
      isingTorusCharacterDispersion chi *
        (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x).im := by
  rw [← isingTorusDirichletBilinearComplex_im u chi,
    isingTorusDirichletBilinearComplex_addChar]
  simp



theorem isingTorus_addChar_secondMoment_le
    (beta : Real) (hbeta : 0 < beta)
    (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (hdisp : 0 < isingTorusCharacterDispersion chi) :
    (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
        Complex.normSq (∑ x : IsingDyadicTorus d k,
          (isingTorusSpinField sigma x : Complex) * chi x)) ≤
      isingTorusShiftedPartition (d := d) (k := k) beta 0 *
        (Fintype.card (IsingDyadicTorus d k) /
          (beta * isingTorusCharacterDispersion chi)) := by
  let hr : IsingDyadicTorus d k → Real := fun x => (chi x).re
  let hi : IsingDyadicTorus d k → Real := fun x => (chi x).im
  let W : ConfigSpace (IsingDyadicTorus d k) → Real := fun sigma =>
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma))
  let A : ConfigSpace (IsingDyadicTorus d k) → Complex := fun sigma =>
    ∑ x : IsingDyadicTorus d k,
      (isingTorusSpinField sigma x : Complex) * chi x
  let delta := isingTorusCharacterDispersion chi
  let Z := isingTorusShiftedPartition (d := d) (k := k) beta 0
  have hre := isingTorus_bilinear_secondMoment_le_dirichlet
    (d := d) (k := k) beta hbeta hdom hr
  have him := isingTorus_bilinear_secondMoment_le_dirichlet
    (d := d) (k := k) beta hbeta hdom hi
  have hbre (sigma) :
      isingTorusDirichletBilinear (isingTorusSpinField sigma) hr =
        delta * (A sigma).re := by
    exact isingTorusDirichletBilinear_re_addChar
      (isingTorusSpinField sigma) chi
  have hbim (sigma) :
      isingTorusDirichletBilinear (isingTorusSpinField sigma) hi =
        delta * (A sigma).im := by
    exact isingTorusDirichletBilinear_im_addChar
      (isingTorusSpinField sigma) chi
  change (∑ sigma, W sigma *
      (isingTorusDirichletBilinear
        (isingTorusSpinField sigma) hr) ^ 2) ≤
      Z * (isingTorusDirichlet hr / beta) at hre
  change (∑ sigma, W sigma *
      (isingTorusDirichletBilinear
        (isingTorusSpinField sigma) hi) ^ 2) ≤
      Z * (isingTorusDirichlet hi / beta) at him
  simp_rw [hbre] at hre
  simp_rw [hbim] at him
  have hsum : delta ^ 2 * (∑ sigma, W sigma * Complex.normSq (A sigma)) ≤
      Z * ((isingTorusDirichlet hr + isingTorusDirichlet hi) / beta) := by
    rw [Finset.mul_sum]
    calc
      ∑ sigma, delta ^ 2 * (W sigma * Complex.normSq (A sigma)) =
          (∑ sigma, W sigma * (delta * (A sigma).re) ^ 2) +
            ∑ sigma, W sigma * (delta * (A sigma).im) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro sigma _
        simp only [Complex.normSq_apply]
        ring
      _ ≤ Z * (isingTorusDirichlet hr / beta) +
          Z * (isingTorusDirichlet hi / beta) := add_le_add hre him
      _ = Z * ((isingTorusDirichlet hr + isingTorusDirichlet hi) / beta) := by
        ring
  have henergy : isingTorusDirichlet hr + isingTorusDirichlet hi =
      Fintype.card (IsingDyadicTorus d k) * delta :=
    isingTorusDirichlet_re_add_im_addChar chi
  rw [henergy] at hsum
  change (∑ sigma, W sigma * Complex.normSq (A sigma)) ≤ _
  rw [div_mul_eq_div_mul_one_div, div_eq_mul_inv]
  have hdelta : 0 < delta := hdisp
  have hdelta0 : delta ≠ 0 := hdelta.ne'
  calc
    (∑ sigma, W sigma * Complex.normSq (A sigma)) =
        delta ^ 2 * (∑ sigma, W sigma * Complex.normSq (A sigma)) /
          delta ^ 2 := by field_simp
    _ ≤ (Z * (Fintype.card (IsingDyadicTorus d k) * delta / beta)) /
          delta ^ 2 := by gcongr
    _ = Z * (Fintype.card (IsingDyadicTorus d k) * beta⁻¹ *
          (1 / delta)) := by field_simp



noncomputable def isingTorusAveragedTwoPoint
    (beta : Real) (z : IsingDyadicTorus d k) : Real :=
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) *
      ∑ x : IsingDyadicTorus d k,
        isingTorusSpinField sigma x *
          isingTorusSpinField sigma (x + z)) /
    (isingTorusShiftedPartition (d := d) (k := k) beta 0 *
      Fintype.card (IsingDyadicTorus d k))

private theorem character_conj_mul_add
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (x z : IsingDyadicTorus d k) :
    conj (chi x) * chi (x + z) = chi z := by
  rw [AddChar.map_add_eq_mul, ← AddChar.inv_apply_eq_conj]
  have hne : chi x ≠ 0 := by
    intro hzero
    have hnorm := AddChar.norm_apply chi x
    simp [hzero] at hnorm
  field_simp

private theorem character_spin_sum_normSq
    (u : IsingDyadicTorus d k → Real)
    (chi : AddChar (IsingDyadicTorus d k) Complex) :
    (Complex.normSq (∑ x : IsingDyadicTorus d k, (u x : Complex) * chi x) :
        Complex) =
      ∑ x : IsingDyadicTorus d k, ∑ z : IsingDyadicTorus d k,
        ((u x * u (x + z) : Real) : Complex) * chi z := by
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul, Complex.conj_ofReal, Finset.mul_sum]
  calc
    ∑ y : IsingDyadicTorus d k,
        (u x : Complex) * conj (chi x) * ((u y : Complex) * chi y) =
      ∑ z : IsingDyadicTorus d k,
        (u x : Complex) * conj (chi x) *
          ((u (x + z) : Complex) * chi (x + z)) := by
      exact (Equiv.addLeft x).bijective.sum_comp
        (fun y : IsingDyadicTorus d k =>
          (u x : Complex) * conj (chi x) * ((u y : Complex) * chi y)) |>.symm
    _ = ∑ z : IsingDyadicTorus d k,
        ((u x * u (x + z) : Real) : Complex) * chi z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← character_conj_mul_add chi x z]
      push_cast
      ring



theorem finiteTorusFourierCoeff_isingTorusAveragedTwoPoint
    (beta : Real) (chi : AddChar (IsingDyadicTorus d k) Complex) :
    finiteTorusFourierCoeff
        (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi =
      ((∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) *
            isingTorusDirichlet (isingTorusSpinField sigma)) *
          Complex.normSq (∑ x : IsingDyadicTorus d k,
            (isingTorusSpinField sigma x : Complex) * chi x)) /
        (isingTorusShiftedPartition (d := d) (k := k) beta 0 *
          Fintype.card (IsingDyadicTorus d k)) : Real) := by
  unfold finiteTorusFourierCoeff isingTorusAveragedTwoPoint
  push_cast
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun t : Complex => t /
    (isingTorusShiftedPartition (d := d) (k := k) beta 0 *
      Fintype.card (IsingDyadicTorus d k)))
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [character_spin_sum_normSq]
  push_cast
  calc
    ∑ z : IsingDyadicTorus d k,
        (Complex.exp (-((beta : Complex) / 2) *
            (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
          ∑ x : IsingDyadicTorus d k,
            (isingTorusSpinField sigma x : Complex) *
              isingTorusSpinField sigma (x + z)) * chi z =
      Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
        ∑ z : IsingDyadicTorus d k, ∑ x : IsingDyadicTorus d k,
          ((isingTorusSpinField sigma x *
            isingTorusSpinField sigma (x + z) : Real) : Complex) * chi z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_assoc]
      rw [Finset.sum_mul]
      apply congrArg (fun t : Complex =>
        Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) * t)
      apply Finset.sum_congr rfl
      intro x _
      push_cast
      ring
    _ = Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
        ∑ x : IsingDyadicTorus d k, ∑ z : IsingDyadicTorus d k,
          ((isingTorusSpinField sigma x *
            isingTorusSpinField sigma (x + z) : Real) : Complex) * chi z := by
      rw [Finset.sum_comm]
    _ = Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) *
        ∑ x : IsingDyadicTorus d k, ∑ z : IsingDyadicTorus d k,
          (isingTorusSpinField sigma x : Complex) *
            isingTorusSpinField sigma (x + z) * chi z := by
      apply congrArg (fun t : Complex =>
        Complex.exp (-((beta : Complex) / 2) *
          (isingTorusDirichlet (isingTorusSpinField sigma) : Complex)) * t)
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      push_cast
      rfl



theorem isingTorusAveragedTwoPoint_fourier_bound
    (beta : Real) (hbeta : 0 < beta)
    (hdom : IsingTorusGaussianDominated (d := d) (k := k) beta)
    (chi : AddChar (IsingDyadicTorus d k) Complex)
    (hdisp : 0 < isingTorusCharacterDispersion chi) :
    0 ≤ (finiteTorusFourierCoeff
        (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re ∧
      (finiteTorusFourierCoeff
          (isingTorusAveragedTwoPoint (d := d) (k := k) beta) chi).re ≤
        1 / (beta * isingTorusCharacterDispersion chi) := by
  let N : Real := ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma)) *
    Complex.normSq (∑ x : IsingDyadicTorus d k,
      (isingTorusSpinField sigma x : Complex) * chi x)
  let Z : Real := isingTorusShiftedPartition (d := d) (k := k) beta 0
  let card : Real := Fintype.card (IsingDyadicTorus d k)
  have hmode := isingTorus_addChar_secondMoment_le
    (d := d) (k := k) beta hbeta hdom chi hdisp
  have hZ : 0 < Z := isingTorusShiftedPartition_zero_pos beta
  have hcard : 0 < card := by
    dsimp [card]
    positivity
  have hden : 0 < Z * card := mul_pos hZ hcard
  have hN : 0 ≤ N := by
    exact Finset.sum_nonneg fun sigma _ =>
      mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)
  rw [finiteTorusFourierCoeff_isingTorusAveragedTwoPoint]
  change 0 ≤ N / (Z * card) ∧
    N / (Z * card) ≤ 1 / (beta * isingTorusCharacterDispersion chi)
  refine ⟨div_nonneg hN hden.le, ?_⟩
  apply (div_le_iff₀ hden).2
  change N ≤ _
  change N ≤ Z *
    (Fintype.card (IsingDyadicTorus d k) /
      (beta * isingTorusCharacterDispersion chi)) at hmode
  calc
    N ≤ Z * (Fintype.card (IsingDyadicTorus d k) /
        (beta * isingTorusCharacterDispersion chi)) := hmode
    _ = 1 / (beta * isingTorusCharacterDispersion chi) * (Z * card) := by
      dsimp [card]
      ring

end StatMech.FrontierA
