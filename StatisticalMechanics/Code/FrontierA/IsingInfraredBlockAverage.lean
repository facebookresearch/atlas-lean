/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingDyadicGreenRiemann
import Code.FrontierA.IsingTorusStationarity

open Finset
open scoped BigOperators ComplexConjugate

namespace StatMech.FrontierA

variable {Gamma : Type*} [Fintype Gamma] [AddCommGroup Gamma]



noncomputable def finiteTorusBlockDifferenceAverage
    (G : Gamma → Real) (B : Finset Gamma) : Real :=
  (1 / (B.card : Real) ^ 2) *
    ∑ a ∈ B, ∑ b ∈ B, G (b - a)



noncomputable def finiteTorusBlockCharacterWeight
    (B : Finset Gamma) (chi : AddChar Gamma Complex) : Real :=
  Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2

theorem finiteTorusBlockCharacterWeight_nonneg
    (B : Finset Gamma) (chi : AddChar Gamma Complex) :
    0 ≤ finiteTorusBlockCharacterWeight B chi := by
  unfold finiteTorusBlockCharacterWeight
  exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

private theorem block_character_double_sum
    (B : Finset Gamma) (chi : AddChar Gamma Complex) :
    (∑ a ∈ B, ∑ b ∈ B, conj (chi (b - a))) =
      Complex.normSq (∑ a ∈ B, chi a) := by
  have hterm (a b : Gamma) :
      conj (chi (b - a)) = chi a * conj (chi b) := by
    rw [AddChar.map_sub_eq_div, map_div₀, div_eq_mul_inv]
    have hinv : (conj (chi a))⁻¹ = chi a := by
      rw [← AddChar.inv_apply_eq_conj]
      exact inv_inv (chi a)
    rw [hinv]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [← map_sum (starRingEnd Complex)]
  rw [Complex.mul_conj]



theorem finiteTorusBlockDifferenceAverage_fourier
    (G : Gamma → Real) (B : Finset Gamma) :
    finiteTorusBlockDifferenceAverage G B =
      (1 / Fintype.card Gamma : Real) *
        ∑ chi : AddChar Gamma Complex,
          (finiteTorusFourierCoeff G chi).re *
            finiteTorusBlockCharacterWeight B chi := by
  classical
  by_cases hB : B.card = 0
  · simp [finiteTorusBlockDifferenceAverage,
      finiteTorusBlockCharacterWeight, hB]
  have hBReal : (B.card : Real) ≠ 0 := by exact_mod_cast hB
  have hcard : (Fintype.card Gamma : Real) ≠ 0 := by positivity
  have hnum :
      (∑ a ∈ B, ∑ b ∈ B, (G (b - a) : Complex)) =
        (1 / Fintype.card Gamma : Complex) *
          ∑ chi : AddChar Gamma Complex,
            finiteTorusFourierCoeff G chi *
              Complex.normSq (∑ a ∈ B, chi a) := by
    calc
      (∑ a ∈ B, ∑ b ∈ B, (G (b - a) : Complex)) =
          ∑ a ∈ B, ∑ b ∈ B,
            (1 / Fintype.card Gamma : Complex) *
              ∑ chi : AddChar Gamma Complex,
                finiteTorusFourierCoeff G chi * conj (chi (b - a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact finiteTorus_fourier_inversion G (b - a)
      _ = (1 / Fintype.card Gamma : Complex) *
          ∑ chi : AddChar Gamma Complex,
            finiteTorusFourierCoeff G chi *
              (∑ a ∈ B, ∑ b ∈ B, conj (chi (b - a))) := by
        calc
          (∑ a ∈ B, ∑ b ∈ B,
              (1 / Fintype.card Gamma : Complex) *
                ∑ chi : AddChar Gamma Complex,
                  finiteTorusFourierCoeff G chi * conj (chi (b - a))) =
              ∑ a ∈ B, ∑ b ∈ B, ∑ chi : AddChar Gamma Complex,
              (1 / Fintype.card Gamma : Complex) *
                (finiteTorusFourierCoeff G chi * conj (chi (b - a))) := by
            simp_rw [Finset.mul_sum]
          _ =
              ∑ a ∈ B, ∑ chi : AddChar Gamma Complex, ∑ b ∈ B,
                (1 / Fintype.card Gamma : Complex) *
                  (finiteTorusFourierCoeff G chi * conj (chi (b - a))) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_comm]
          _ = ∑ chi : AddChar Gamma Complex, ∑ a ∈ B, ∑ b ∈ B,
                (1 / Fintype.card Gamma : Complex) *
                  (finiteTorusFourierCoeff G chi * conj (chi (b - a))) := by
            rw [Finset.sum_comm]
          _ = (1 / Fintype.card Gamma : Complex) *
              ∑ chi : AddChar Gamma Complex,
                finiteTorusFourierCoeff G chi *
                  (∑ a ∈ B, ∑ b ∈ B, conj (chi (b - a))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro chi _
            simp_rw [Finset.mul_sum]
      _ = (1 / Fintype.card Gamma : Complex) *
          ∑ chi : AddChar Gamma Complex,
            finiteTorusFourierCoeff G chi *
              Complex.normSq (∑ a ∈ B, chi a) := by
        apply congrArg ((1 / Fintype.card Gamma : Complex) * ·)
        apply Finset.sum_congr rfl
        intro chi _
        rw [block_character_double_sum]
  have hcomplex :
      ((finiteTorusBlockDifferenceAverage G B : Real) : Complex) =
        (1 / Fintype.card Gamma : Complex) *
          ∑ chi : AddChar Gamma Complex,
            finiteTorusFourierCoeff G chi *
              (Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2) := by
    unfold finiteTorusBlockDifferenceAverage
    push_cast
    rw [hnum]
    calc
      (1 / (B.card : Complex) ^ 2) *
          ((1 / Fintype.card Gamma : Complex) *
            ∑ chi : AddChar Gamma Complex,
              finiteTorusFourierCoeff G chi *
                Complex.normSq (∑ a ∈ B, chi a)) =
          (1 / Fintype.card Gamma : Complex) *
            ∑ chi : AddChar Gamma Complex,
              (1 / (B.card : Complex) ^ 2) *
                (finiteTorusFourierCoeff G chi *
                  Complex.normSq (∑ a ∈ B, chi a)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro chi _
        ring
      _ = (1 / Fintype.card Gamma : Complex) *
          ∑ chi : AddChar Gamma Complex,
            finiteTorusFourierCoeff G chi *
              (Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2) := by
        apply congrArg ((1 / Fintype.card Gamma : Complex) * ·)
        apply Finset.sum_congr rfl
        intro chi _
        push_cast
        field_simp [hBReal]
  calc
    finiteTorusBlockDifferenceAverage G B =
        (((finiteTorusBlockDifferenceAverage G B : Real) : Complex)).re := rfl
    _ = ((1 / Fintype.card Gamma : Complex) *
          ∑ chi : AddChar Gamma Complex,
            finiteTorusFourierCoeff G chi *
              (Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2)).re :=
      congrArg Complex.re hcomplex
    _ = (1 / Fintype.card Gamma : Real) *
        ∑ chi : AddChar Gamma Complex,
          (finiteTorusFourierCoeff G chi).re *
            finiteTorusBlockCharacterWeight B chi := by
      have hscalar : (1 / Fintype.card Gamma : Complex) =
          ((1 / Fintype.card Gamma : Real) : Complex) := by
        push_cast
        rfl
      rw [hscalar, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      congr 1
      change Complex.reCLM
          (∑ chi : AddChar Gamma Complex,
            finiteTorusFourierCoeff G chi *
              (Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro chi _
      unfold finiteTorusBlockCharacterWeight
      have hweightCast :
          (Complex.normSq (∑ a ∈ B, chi a) : Complex) /
              ((B.card : Real) : Complex) ^ 2 =
            ((Complex.normSq (∑ a ∈ B, chi a) /
              (B.card : Real) ^ 2 : Real) : Complex) := by
        push_cast
        rfl
      have hweightReal :
          ((Complex.normSq (∑ a ∈ B, chi a) : Complex) /
              ((B.card : Real) : Complex) ^ 2).re =
            Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2 := by
        rw [hweightCast]
        exact Complex.ofReal_re _
      have hweightImag :
          ((Complex.normSq (∑ a ∈ B, chi a) : Complex) /
              ((B.card : Real) : Complex) ^ 2).im = 0 := by
        rw [hweightCast]
        exact Complex.ofReal_im _
      change (finiteTorusFourierCoeff G chi *
        (Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2)).re = _
      rw [Complex.mul_re, hweightReal, hweightImag, mul_zero, sub_zero]

theorem finiteTorusBlockCharacterWeight_zero
    (B : Finset Gamma) :
    finiteTorusBlockCharacterWeight B (0 : AddChar Gamma Complex) =
      if B.card = 0 then 0 else 1 := by
  classical
  by_cases hB : B.card = 0
  · simp [finiteTorusBlockCharacterWeight, hB]
  · have hBReal : (B.card : Real) ≠ 0 := by exact_mod_cast hB
    simp [finiteTorusBlockCharacterWeight, hB]
    field_simp



theorem finiteTorusBlockDifferenceAverage_le
    (G : Gamma → Real) (B : Finset Gamma) (C : Real)
    (dispersion : AddChar Gamma Complex → Real)
    (hB : B.Nonempty)
    (hreal : ∀ chi, (finiteTorusFourierCoeff G chi).im = 0)
    (hbound : ∀ chi, chi ≠ 0 →
      0 ≤ (finiteTorusFourierCoeff G chi).re ∧
      (finiteTorusFourierCoeff G chi).re ≤ C / dispersion chi) :
    finiteTorusBlockDifferenceAverage G B ≤
      (finiteTorusFourierCoeff G 0).re / Fintype.card Gamma +
      (1 / Fintype.card Gamma : Real) *
        ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
          (C / dispersion chi) *
            finiteTorusBlockCharacterWeight B chi := by
  classical
  rw [finiteTorusBlockDifferenceAverage_fourier]
  let f : AddChar Gamma Complex → Real := fun chi =>
    (finiteTorusFourierCoeff G chi).re *
      finiteTorusBlockCharacterWeight B chi
  have hdecomp : (∑ chi : AddChar Gamma Complex, f chi) =
      (∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex), f chi) + f 0 :=
    (Finset.sum_erase_add Finset.univ f (Finset.mem_univ 0)).symm
  change (1 / Fintype.card Gamma : Real) * (∑ chi, f chi) ≤ _
  rw [hdecomp]
  have hweight0 := finiteTorusBlockCharacterWeight_zero
    (Gamma := Gamma) B
  rw [if_neg hB.card_ne_zero] at hweight0
  dsimp [f]
  rw [hweight0, mul_one]
  have hcard : (0 : Real) < Fintype.card Gamma := by positivity
  calc
    (1 / Fintype.card Gamma : Real) *
        (∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
            (finiteTorusFourierCoeff G chi).re *
              finiteTorusBlockCharacterWeight B chi +
          (finiteTorusFourierCoeff G 0).re) =
        (finiteTorusFourierCoeff G 0).re / Fintype.card Gamma +
          (1 / Fintype.card Gamma : Real) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (finiteTorusFourierCoeff G chi).re *
                finiteTorusBlockCharacterWeight B chi := by ring
    _ ≤ (finiteTorusFourierCoeff G 0).re / Fintype.card Gamma +
          (1 / Fintype.card Gamma : Real) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (C / dispersion chi) *
                finiteTorusBlockCharacterWeight B chi := by
      gcongr with chi hchi
      exact finiteTorusBlockCharacterWeight_nonneg B chi
      exact (hbound chi (Finset.ne_of_mem_erase hchi)).2

end StatMech.FrontierA
