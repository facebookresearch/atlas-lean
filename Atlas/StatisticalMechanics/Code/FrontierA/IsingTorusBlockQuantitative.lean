/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusAxisBlockAverage
import Code.FrontierA.IsingDyadicGreenLowMomentum

open Finset Set
open scoped BigOperators ComplexConjugate

namespace StatMech.FrontierA

variable {Gamma : Type*} [Fintype Gamma] [AddCommGroup Gamma]


theorem finiteTorusBlockCharacterWeight_le_one
    (B : Finset Gamma) (chi : AddChar Gamma Complex) :
    finiteTorusBlockCharacterWeight B chi <= 1 := by
  by_cases hB : B.card = 0
  · simp [finiteTorusBlockCharacterWeight, hB]
  have hnorm : ‖∑ a ∈ B, chi a‖ <= (B.card : Real) := by
    calc
      ‖∑ a ∈ B, chi a‖ <= ∑ a ∈ B, ‖chi a‖ := norm_sum_le _ _
      _ = (B.card : Real) := by simp
  have hcard : 0 <= (B.card : Real) := by positivity
  have hsq : Complex.normSq (∑ a ∈ B, chi a) <= (B.card : Real) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (∑ a ∈ B, chi a)]
  unfold finiteTorusBlockCharacterWeight
  exact (div_le_one (sq_pos_of_pos (by
    exact_mod_cast Nat.pos_of_ne_zero hB))).2 hsq


theorem sum_finiteTorusBlockCharacterWeight
    (B : Finset Gamma) (hB : B.Nonempty) :
    ∑ chi : AddChar Gamma Complex,
        finiteTorusBlockCharacterWeight B chi =
      Fintype.card Gamma / (B.card : Real) := by
  classical
  have hBReal : (B.card : Real) ≠ 0 := by
    exact_mod_cast hB.card_ne_zero
  have hnumComplex :
      (∑ chi : AddChar Gamma Complex,
          (Complex.normSq (∑ a ∈ B, chi a) : Complex)) =
        (Fintype.card Gamma : Complex) * B.card := by
    calc
      (∑ chi : AddChar Gamma Complex,
          (Complex.normSq (∑ a ∈ B, chi a) : Complex)) =
          ∑ chi : AddChar Gamma Complex,
            ∑ a ∈ B, ∑ b ∈ B, chi (b - a) := by
        apply Finset.sum_congr rfl
        intro chi _
        rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [← AddChar.inv_apply_eq_conj, AddChar.map_sub_eq_div]
        rw [div_eq_mul_inv, mul_comm]
      _ = ∑ a ∈ B, ∑ b ∈ B,
          ∑ chi : AddChar Gamma Complex, chi (b - a) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = ∑ a ∈ B, ∑ b ∈ B,
          if b = a then (Fintype.card Gamma : Complex) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [AddChar.sum_apply_eq_ite]
        simp only [sub_eq_zero]
      _ = (Fintype.card Gamma : Complex) * B.card := by
        simp
        ring
  have hnumReal :
      ∑ chi : AddChar Gamma Complex,
          Complex.normSq (∑ a ∈ B, chi a) =
        (Fintype.card Gamma : Real) * B.card := by
    exact_mod_cast congrArg Complex.re hnumComplex
  unfold finiteTorusBlockCharacterWeight
  rw [← Finset.sum_div, hnumReal]
  field_simp

section Dyadic

variable {d k M : Nat}

private theorem centered_natAbs_le_half
    (p : IsingDyadicTorus d k) (i : Fin d) :
    (p i).valMinAbs.natAbs <= isingDyadicSide k / 2 := by
  exact ZMod.natAbs_valMinAbs_le (p i)



theorem isingTorusCharacterDispersion_inverse_le_of_not_lowMomentum
    (p : IsingDyadicTorus d k) (hp0 : p ≠ 0)
    (hpHigh : p ∉ isingTorusLowMomentum d k M) :
    (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ <=
      (isingDyadicSide k : Real) ^ 2 /
        (16 * ((M + 1 : Nat) : Real) ^ 2) := by
  have hpAll : p ∈ isingTorusLowMomentum d k (isingDyadicSide k / 2) := by
    rw [isingTorusLowMomentum_mem_iff]
    exact ⟨hp0, centered_natAbs_le_half p⟩
  have hquad := isingTorusCharacterDispersion_centered_lower hpAll le_rfl
  rw [isingTorusLowMomentum_mem_iff] at hpHigh
  push Not at hpHigh
  obtain ⟨i, hi⟩ := hpHigh hp0
  have hcoord : (((M + 1 : Nat) : Real) ^ 2) <=
      (((p i).valMinAbs : Real) ^ 2) := by
    have habs : ((M + 1 : Nat) : Real) <= |((p i).valMinAbs : Real)| := by
      have : M + 1 <= (p i).valMinAbs.natAbs := by omega
      calc
        ((M + 1 : Nat) : Real) <= ((p i).valMinAbs.natAbs : Real) := by
          exact_mod_cast this
        _ = |((p i).valMinAbs : Real)| := by
          generalize (p i).valMinAbs = a
          cases a with
          | ofNat q => simp
          | negSucc q =>
              simp only [Int.cast_negSucc, Int.natAbs_negSucc,
                Nat.cast_add, Nat.cast_one]
              have hq : -((q : Real) + 1) <= 0 := neg_nonpos.mpr (by positivity)
              rw [abs_of_nonpos hq]
              norm_cast
    nlinarith [sq_abs ((p i).valMinAbs : Real)]
  have hnorm : (((p i).valMinAbs : Real) ^ 2) <=
      integerMomentumNormSq (isingTorusCenteredIntMomentum p) := by
    unfold integerMomentumNormSq isingTorusCenteredIntMomentum
    exact Finset.single_le_sum (fun j _ => sq_nonneg ((p j).valMinAbs : Real))
      (Finset.mem_univ i)
  have hL : 0 < (isingDyadicSide k : Real) := by
    exact_mod_cast isingDyadicSide_pos k
  have hlower :
      16 * (((M + 1 : Nat) : Real) ^ 2) /
          (isingDyadicSide k : Real) ^ 2 <=
        isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
    calc
      16 * (((M + 1 : Nat) : Real) ^ 2) /
          (isingDyadicSide k : Real) ^ 2 =
          (16 / (isingDyadicSide k : Real) ^ 2) *
            (((M + 1 : Nat) : Real) ^ 2) := by ring
      _ <= (16 / (isingDyadicSide k : Real) ^ 2) *
          integerMomentumNormSq (isingTorusCenteredIntMomentum p) := by
        gcongr
        exact hcoord.trans hnorm
      _ <= isingTorusCharacterDispersion (isingTorusMomentumChar p) := hquad
  have hleft : 0 < 16 * (((M + 1 : Nat) : Real) ^ 2) /
      (isingDyadicSide k : Real) ^ 2 := by positivity
  calc
    (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ <=
        (16 * (((M + 1 : Nat) : Real) ^ 2) /
          (isingDyadicSide k : Real) ^ 2)⁻¹ := inv_anti₀ hleft hlower
    _ = (isingDyadicSide k : Real) ^ 2 /
        (16 * ((M + 1 : Nat) : Real) ^ 2) := by field_simp


theorem finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power
    (hd : 2 < d) (B : Finset (IsingDyadicTorus d k)) (hB : B.Nonempty)
    (M : Nat) (hM : 1 <= M) (hMhalf : M <= isingDyadicSide k / 2)
    (C : Real)
    (hLow : (1 / (isingDyadicSide k : Real) ^ d) *
        ∑ p ∈ isingTorusLowMomentum d k M,
          (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ <=
        C * ((M : Real) / isingDyadicSide k) ^ (d - 2)) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k))) B <=
      C *
          ((M : Real) / isingDyadicSide k) ^ (d - 2) +
        (isingDyadicSide k : Real) ^ 2 /
          (16 * ((M + 1 : Nat) : Real) ^ 2 * B.card) := by
  let term : IsingDyadicTorus d k -> Real := fun p =>
    (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ *
      finiteTorusBlockCharacterWeight B (isingTorusMomentumChar p)
  have hgreen := finiteTorusBlockDifferenceAverage_zeroModeGreen
    (isingTorusCharacterDispersion (d := d) (k := k)) B
  have hsumChars :
      (∑ chi ∈ Finset.univ.erase
          (0 : AddChar (IsingDyadicTorus d k) Complex),
        (isingTorusCharacterDispersion chi)⁻¹ *
          finiteTorusBlockCharacterWeight B chi) =
        ∑ p : IsingDyadicTorus d k, term p := by
    have hzero :
        (isingTorusCharacterDispersion
            (0 : AddChar (IsingDyadicTorus d k) Complex))⁻¹ *
          finiteTorusBlockCharacterWeight B 0 = 0 := by
      simp [isingTorusCharacterDispersion]
    let f : AddChar (IsingDyadicTorus d k) Complex -> Real := fun chi =>
      (isingTorusCharacterDispersion chi)⁻¹ *
        finiteTorusBlockCharacterWeight B chi
    calc
      ∑ chi ∈ Finset.univ.erase
          (0 : AddChar (IsingDyadicTorus d k) Complex), f chi =
          ∑ chi : AddChar (IsingDyadicTorus d k) Complex, f chi := by
        rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ 0)]
        simp [f, isingTorusCharacterDispersion]
      _ = ∑ p : IsingDyadicTorus d k,
          f (isingTorusMomentumEquiv p) :=
        (Equiv.sum_comp isingTorusMomentumEquiv f).symm
      _ = ∑ p : IsingDyadicTorus d k, term p := by rfl
  rw [hgreen, hsumChars]
  let low := isingTorusLowMomentum d k M
  have hsplit : (∑ p : IsingDyadicTorus d k, term p) =
      (∑ p ∈ low, term p) + ∑ p ∈ Finset.univ.filter (fun p => p ∉ low), term p := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => p ∈ low)]
    simp
  rw [hsplit, mul_add]
  have hcard : (Fintype.card (IsingDyadicTorus d k) : Real) =
      (isingDyadicSide k : Real) ^ d := by
    rw [isingDyadicTorus_card]
    norm_cast
  rw [hcard]
  have hcoef : 0 <= 1 / (isingDyadicSide k : Real) ^ d := by positivity
  have hlow :
      (1 / (isingDyadicSide k : Real) ^ d) * (∑ p ∈ low, term p) <=
        C *
          ((M : Real) / isingDyadicSide k) ^ (d - 2) := by
    calc
      (1 / (isingDyadicSide k : Real) ^ d) * (∑ p ∈ low, term p) <=
          (1 / (isingDyadicSide k : Real) ^ d) *
            ∑ p ∈ low,
              (isingTorusCharacterDispersion
                (isingTorusMomentumChar p))⁻¹ := by
        gcongr with p hp
        dsimp [term]
        rw [isingTorusLowMomentum_mem_iff] at hp
        have hdisp := isingTorusCharacterDispersion_pos_of_ne_zero
          (isingTorusMomentumChar p)
          ((isingTorusMomentumChar_eq_zero_iff p).not.mpr
            hp.1)
        exact mul_le_of_le_one_right (inv_nonneg.mpr hdisp.le)
          (finiteTorusBlockCharacterWeight_le_one B _)
      _ <= C * ((M : Real) / isingDyadicSide k) ^ (d - 2) := by
        simpa [low] using hLow
  have hhighCoef : 0 <=
      (isingDyadicSide k : Real) ^ 2 /
        (16 * ((M + 1 : Nat) : Real) ^ 2) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))
  have hhighTerm (p : IsingDyadicTorus d k)
      (hp : p ∈ Finset.univ.filter (fun p => p ∉ low)) :
      term p <=
        ((isingDyadicSide k : Real) ^ 2 /
            (16 * ((M + 1 : Nat) : Real) ^ 2)) *
          finiteTorusBlockCharacterWeight B (isingTorusMomentumChar p) := by
    have hpHigh : p ∉ isingTorusLowMomentum d k M := by
      simpa [low] using hp
    by_cases hp0 : p = 0
    · subst p
      dsimp [term]
      rw [show (isingTorusCharacterDispersion
          (isingTorusMomentumChar (0 : IsingDyadicTorus d k)))⁻¹ = 0 by
        simp [isingTorusCharacterDispersion]]
      rw [zero_mul]
      exact mul_nonneg hhighCoef
        (finiteTorusBlockCharacterWeight_nonneg B _)
    · dsimp [term]
      exact mul_le_mul_of_nonneg_right
        (isingTorusCharacterDispersion_inverse_le_of_not_lowMomentum
          p hp0 hpHigh)
        (finiteTorusBlockCharacterWeight_nonneg B _)
  have hweights :
      ∑ p : IsingDyadicTorus d k,
          finiteTorusBlockCharacterWeight B (isingTorusMomentumChar p) =
        Fintype.card (IsingDyadicTorus d k) / (B.card : Real) := by
    calc
      ∑ p : IsingDyadicTorus d k,
          finiteTorusBlockCharacterWeight B (isingTorusMomentumChar p) =
          ∑ chi : AddChar (IsingDyadicTorus d k) Complex,
            finiteTorusBlockCharacterWeight B chi :=
        Equiv.sum_comp isingTorusMomentumEquiv
          (finiteTorusBlockCharacterWeight B)
      _ = _ := sum_finiteTorusBlockCharacterWeight B hB
  have hhigh :
      (1 / (isingDyadicSide k : Real) ^ d) *
          (∑ p ∈ Finset.univ.filter (fun p => p ∉ low), term p) <=
        (isingDyadicSide k : Real) ^ 2 /
          (16 * ((M + 1 : Nat) : Real) ^ 2 * B.card) := by
    calc
      (1 / (isingDyadicSide k : Real) ^ d) *
          (∑ p ∈ Finset.univ.filter (fun p => p ∉ low), term p) <=
          (1 / (isingDyadicSide k : Real) ^ d) *
            ∑ p ∈ Finset.univ.filter (fun p => p ∉ low),
              (((isingDyadicSide k : Real) ^ 2 /
                  (16 * ((M + 1 : Nat) : Real) ^ 2)) *
                finiteTorusBlockCharacterWeight B
                  (isingTorusMomentumChar p)) := by
        gcongr with p hp
        exact hhighTerm p hp
      _ <= (1 / (isingDyadicSide k : Real) ^ d) *
            (((isingDyadicSide k : Real) ^ 2 /
                (16 * ((M + 1 : Nat) : Real) ^ 2)) *
              ∑ p : IsingDyadicTorus d k,
                finiteTorusBlockCharacterWeight B
                  (isingTorusMomentumChar p)) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ hhighCoef
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun p _ _ => finiteTorusBlockCharacterWeight_nonneg B _)
      _ = (isingDyadicSide k : Real) ^ 2 /
          (16 * ((M + 1 : Nat) : Real) ^ 2 * B.card) := by
        rw [hweights, hcard]
        have hsidePos : (0 : Real) < isingDyadicSide k := by
          exact_mod_cast isingDyadicSide_pos k
        have hside : (isingDyadicSide k : Real) ≠ 0 := hsidePos.ne'
        have hBcard : (B.card : Real) ≠ 0 := by
          exact_mod_cast hB.card_ne_zero
        have hMone : (((M + 1 : Nat) : Real)) ≠ 0 := by positivity
        field_simp [hside, hBcard, hMone]
  exact add_le_add hlow hhigh



theorem exists_finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power
    (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ (k : Nat)
      (B : Finset (IsingDyadicTorus d k)), B.Nonempty ->
      ∀ M : Nat, 1 <= M -> M <= isingDyadicSide k / 2 ->
      finiteTorusBlockDifferenceAverage
          (finiteTorusZeroModeGreen
            (isingTorusCharacterDispersion (d := d) (k := k))) B <=
        C * ((M : Real) / isingDyadicSide k) ^ (d - 2) +
          (isingDyadicSide k : Real) ^ 2 /
            (16 * ((M + 1 : Nat) : Real) ^ 2 * B.card) := by
  obtain ⟨C, hC, hlow⟩ := isingTorusLowMomentum_inverseDispersion_le hd
  refine ⟨C, hC, ?_⟩
  intro k B hB M hM hMhalf
  exact finiteTorusBlockDifferenceAverage_zeroModeGreen_le_power
    hd B hB M hM hMhalf C (hlow k M hM hMhalf)



theorem isingTorusTwoPoint_blockDifferenceAverage_le_green
    (beta : Real) (hbeta : 0 < beta)
    (B : Finset (IsingDyadicTorus d k)) (hB : B.Nonempty) :
    finiteTorusBlockDifferenceAverage
        (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) B <=
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / beta) * finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k))) B := by
  let G : IsingDyadicTorus d k -> Real :=
    fun z => isingTorusTwoPoint beta 0 z
  have hkernel : G = isingTorusAveragedTwoPoint beta := by
    funext z
    exact (isingTorusAveragedTwoPoint_eq_twoPoint beta z).symm
  have hupper := finiteTorusBlockDifferenceAverage_le
    G B (1 / beta) isingTorusCharacterDispersion hB
      (fun chi => by
        rw [hkernel, finiteTorusFourierCoeff_isingTorusAveragedTwoPoint]
        rfl)
      (fun chi hchi => by
        rw [hkernel]
        have hdisp := isingTorusCharacterDispersion_pos_of_ne_zero chi hchi
        have hbound := isingTorusAveragedTwoPoint_fourier_bound beta hbeta
          (isingTorus_gaussianDominated beta hbeta.le) chi hdisp
        convert hbound using 1 <;> ring)
  have hgreen := finiteTorusBlockDifferenceAverage_zeroModeGreen
    (isingTorusCharacterDispersion (d := d) (k := k)) B
  rw [hgreen]
  refine hupper.trans_eq ?_
  simp only [G]
  congr 1
  have hsum :
      (∑ chi ∈ Finset.univ.erase
          (0 : AddChar (IsingDyadicTorus d k) Complex),
        ((1 / beta) / isingTorusCharacterDispersion chi) *
          finiteTorusBlockCharacterWeight B chi) =
        (1 / beta) *
          ∑ chi ∈ Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex),
          (isingTorusCharacterDispersion chi)⁻¹ *
            finiteTorusBlockCharacterWeight B chi := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi _
    ring
  rw [hsum]
  ring

end Dyadic

end StatMech.FrontierA
