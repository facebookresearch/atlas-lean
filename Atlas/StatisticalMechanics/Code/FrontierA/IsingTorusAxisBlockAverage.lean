/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusAxisMonotonicity
import Code.FrontierA.IsingInfraredBlockAverage

open Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

variable {Gamma : Type*} [AddCommGroup Gamma]




theorem le_finiteTorusBlockDifferenceAverage
    (G : Gamma → Real) (B : Finset Gamma) (m : Real)
    (hB : B.Nonempty) (hm : ∀ a ∈ B, ∀ b ∈ B, m ≤ G (b - a)) :
    m ≤ finiteTorusBlockDifferenceAverage G B := by
  have hcard : (0 : Real) < B.card := by
    exact_mod_cast hB.card_pos
  have hsum : (B.card : Real) ^ 2 * m ≤
      ∑ a ∈ B, ∑ b ∈ B, G (b - a) := by
    calc
      (B.card : Real) ^ 2 * m =
          ∑ a ∈ B, ∑ _b ∈ B, m := by
        simp
        ring
      _ ≤ ∑ a ∈ B, ∑ b ∈ B, G (b - a) := by
        gcongr with a ha b hb
        exact hm a ha b hb
  unfold finiteTorusBlockDifferenceAverage
  have hcardSq : (0 : Real) < (B.card : Real) ^ 2 := sq_pos_of_pos hcard
  calc
    m = (1 / (B.card : Real) ^ 2) * ((B.card : Real) ^ 2 * m) := by
      field_simp
    _ ≤ (1 / (B.card : Real) ^ 2) *
        ∑ a ∈ B, ∑ b ∈ B, G (b - a) := by
      gcongr

section FiniteGreen

variable [Fintype Gamma]



noncomputable def finiteTorusZeroModeGreen
    (dispersion : AddChar Gamma Complex → Real) (z : Gamma) : Real :=
  (1 / Fintype.card Gamma : Real) *
    ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
      (starRingEnd Complex (chi z)).re / dispersion chi

private theorem block_character_re_double_sum
    (B : Finset Gamma) (chi : AddChar Gamma Complex) :
    (∑ a ∈ B, ∑ b ∈ B,
        (starRingEnd Complex (chi (b - a))).re) =
      Complex.normSq (∑ a ∈ B, chi a) := by
  have hterm (a b : Gamma) :
      starRingEnd Complex (chi (b - a)) =
        chi a * starRingEnd Complex (chi b) := by
    rw [AddChar.map_sub_eq_div, map_div₀, div_eq_mul_inv]
    have hinv : (starRingEnd Complex (chi a))⁻¹ = chi a := by
      rw [← AddChar.inv_apply_eq_conj]
      exact inv_inv (chi a)
    rw [hinv]
    ring
  have hcomplex :
      (∑ a ∈ B, ∑ b ∈ B,
          starRingEnd Complex (chi (b - a))) =
        Complex.normSq (∑ a ∈ B, chi a) := by
    simp_rw [hterm, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ← map_sum (starRingEnd Complex),
      Complex.mul_conj]
  have hre := congrArg Complex.re hcomplex
  change Complex.reCLM
      (∑ a ∈ B, ∑ b ∈ B,
        starRingEnd Complex (chi (b - a))) = _ at hre
  simp only [map_sum] at hre
  exact hre



theorem finiteTorusBlockDifferenceAverage_zeroModeGreen
    (dispersion : AddChar Gamma Complex → Real) (B : Finset Gamma) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen dispersion) B =
      (1 / Fintype.card Gamma : Real) *
        ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
          (dispersion chi)⁻¹ * finiteTorusBlockCharacterWeight B chi := by
  classical
  by_cases hB : B.card = 0
  · simp [finiteTorusBlockDifferenceAverage,
      finiteTorusBlockCharacterWeight, hB]
  · have hBReal : (B.card : Real) ≠ 0 := by exact_mod_cast hB
    have hraw :
        (∑ a ∈ B, ∑ b ∈ B,
            finiteTorusZeroModeGreen dispersion (b - a)) =
          (1 / Fintype.card Gamma : Real) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (dispersion chi)⁻¹ *
                Complex.normSq (∑ a ∈ B, chi a) := by
      unfold finiteTorusZeroModeGreen
      calc
        (∑ a ∈ B, ∑ b ∈ B,
            (1 / Fintype.card Gamma : Real) *
              ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
                (starRingEnd Complex (chi (b - a))).re / dispersion chi) =
            (∑ a ∈ B, ∑ b ∈ B,
              ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
                (1 / Fintype.card Gamma : Real) *
                  ((starRingEnd Complex (chi (b - a))).re /
                    dispersion chi)) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              rw [Finset.mul_sum]
        _ = ∑ a ∈ B,
              ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
                ∑ b ∈ B, (1 / Fintype.card Gamma : Real) *
                  ((starRingEnd Complex (chi (b - a))).re /
                    dispersion chi) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.sum_comm]
        _ = ∑ chi ∈ Finset.univ.erase
              (0 : AddChar Gamma Complex),
              ∑ a ∈ B, ∑ b ∈ B,
                (1 / Fintype.card Gamma : Real) *
                  ((starRingEnd Complex (chi (b - a))).re /
                    dispersion chi) := by
              rw [Finset.sum_comm]
        _ = ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (1 / Fintype.card Gamma : Real) *
                ((dispersion chi)⁻¹ *
                  Complex.normSq (∑ a ∈ B, chi a)) := by
              apply Finset.sum_congr rfl
              intro chi hchi
              calc
                (∑ a ∈ B, ∑ b ∈ B,
                    (1 / Fintype.card Gamma : Real) *
                      ((starRingEnd Complex (chi (b - a))).re /
                        dispersion chi)) =
                    (1 / Fintype.card Gamma : Real) * (dispersion chi)⁻¹ *
                      (∑ a ∈ B, ∑ b ∈ B,
                        (starRingEnd Complex (chi (b - a))).re) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro b hb
                  ring
                _ = (1 / Fintype.card Gamma : Real) *
                    ((dispersion chi)⁻¹ *
                      Complex.normSq (∑ a ∈ B, chi a)) := by
                  rw [block_character_re_double_sum]
                  ring
        _ = (1 / Fintype.card Gamma : Real) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (dispersion chi)⁻¹ *
                Complex.normSq (∑ a ∈ B, chi a) := by
              exact (Finset.mul_sum
                (Finset.univ.erase (0 : AddChar Gamma Complex))
                (fun chi => (dispersion chi)⁻¹ *
                  Complex.normSq (∑ a ∈ B, chi a))
                (1 / Fintype.card Gamma : Real)).symm
    unfold finiteTorusBlockDifferenceAverage
    rw [hraw]
    unfold finiteTorusBlockCharacterWeight
    have hscaled :
        (∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
            (dispersion chi)⁻¹ *
              (Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2)) =
          (1 / (B.card : Real) ^ 2) *
            ∑ chi ∈ Finset.univ.erase (0 : AddChar Gamma Complex),
              (dispersion chi)⁻¹ *
                Complex.normSq (∑ a ∈ B, chi a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi hchi
      field_simp
    rw [hscaled]
    ring

end FiniteGreen

variable {d k : Nat}



theorem finiteTorusZeroModeGreen_isingSiteToDyadicTorus
    (x : StatMech.Lattice.Site d) :
    finiteTorusZeroModeGreen
        (isingTorusCharacterDispersion (d := d) (k := k))
        (isingSiteToDyadicTorus k x) =
      isingDyadicTorusGreen x k := by
  classical
  let f : AddChar (IsingDyadicTorus d k) Complex → Real := fun chi =>
    (starRingEnd Complex (chi (isingSiteToDyadicTorus k x))).re /
      isingTorusCharacterDispersion chi
  have hfzero : f 0 = 0 := by
    simp [f, isingTorusCharacterDispersion]
  have herase :
      (∑ chi ∈ Finset.univ.erase
          (0 : AddChar (IsingDyadicTorus d k) Complex), f chi) =
        ∑ chi : AddChar (IsingDyadicTorus d k) Complex, f chi := by
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ 0), hfzero,
      add_zero]
  have hreindex := (isingTorusMomentumEquiv (d := d) (k := k)).sum_comp f
  rw [finiteTorusZeroModeGreen, herase, ← hreindex,
    isingDyadicTorusGreen_eq_character_sum]
  apply congrArg ((1 / Fintype.card (IsingDyadicTorus d k) : Real) * ·)
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hp0 : p = 0
  · subst p
    simp [f, isingTorusCharacterDispersion]
  · simp only [if_neg hp0]
    rw [show f (isingTorusMomentumEquiv p) =
        (starRingEnd Complex
          (isingTorusMomentumChar p (isingSiteToDyadicTorus k x))).re /
            isingTorusCharacterDispersion (isingTorusMomentumChar p) by rfl]
    ring



theorem finiteTorusZeroModeGreen_axisDifference
    (i : Fin d) (a b : Nat) :
    finiteTorusZeroModeGreen
        (isingTorusCharacterDispersion (d := d) (k := k))
        (isingTorusCoordinateShift i b - isingTorusCoordinateShift i a) =
      isingDyadicTorusGreen
        (Pi.single i ((b : Int) - (a : Int))) k := by
  rw [← finiteTorusZeroModeGreen_isingSiteToDyadicTorus
    (k := k) (Pi.single i ((b : Int) - (a : Int)))]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Pi.sub_apply, isingTorusCoordinateShift_apply_same,
      isingSiteToDyadicTorus, Pi.single_eq_same]
    push_cast
    rfl
  · simp only [Pi.sub_apply,
      isingTorusCoordinateShift_apply_of_ne i j hji,
      isingSiteToDyadicTorus, Pi.single_eq_of_ne hji]
    change (0 : ZMod (2 ^ (k + 2))) - 0 = ((0 : Int) : ZMod (2 ^ (k + 2)))
    norm_num


noncomputable def isingTorusAxisSegment (i : Fin d) (r : Nat) :
    Finset (IsingDyadicTorus d k) :=
  (Finset.range (r + 1)).image (isingTorusCoordinateShift i)

theorem isingTorusCoordinateShift_injectiveOn_range
    (i : Fin d) (r : Nat) (hr : r < isingDyadicSide k) :
    Set.InjOn (isingTorusCoordinateShift (k := k) i)
      (Finset.range (r + 1) : Set Nat) := by
  intro a ha b hb hab
  have haR : a < r + 1 := by simpa using ha
  have hbR : b < r + 1 := by simpa using hb
  have haL : a < isingDyadicSide k := by omega
  have hbL : b < isingDyadicSide k := by omega
  have hcoord := congrFun hab i
  rw [isingTorusCoordinateShift_apply_same,
    isingTorusCoordinateShift_apply_same] at hcoord
  have hval := congrArg ZMod.val hcoord
  have haMod : a < 2 ^ (k + 2) := by
    simpa [isingDyadicSide] using haL
  have hbMod : b < 2 ^ (k + 2) := by
    simpa [isingDyadicSide] using hbL
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt haMod, Nat.mod_eq_of_lt hbMod] at hval
  exact hval

theorem isingTorusAxisSegment_card
    (i : Fin d) (r : Nat) (hr : r < isingDyadicSide k) :
    (isingTorusAxisSegment (k := k) i r).card = r + 1 := by
  unfold isingTorusAxisSegment
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    exact isingTorusCoordinateShift_injectiveOn_range i r hr
      (by simpa using ha) (by simpa using hb) hab


theorem finiteTorusBlockDifferenceAverage_zeroModeGreen_axisSegment
    (i : Fin d) (r : Nat) (hr : r < isingDyadicSide k) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusAxisSegment i r) =
      (1 / ((r + 1 : Nat) : Real) ^ 2) *
        ∑ a ∈ Finset.range (r + 1),
          ∑ b ∈ Finset.range (r + 1),
            isingDyadicTorusGreen
              (Pi.single i ((b : Int) - (a : Int))) k := by
  unfold finiteTorusBlockDifferenceAverage
  rw [isingTorusAxisSegment_card i r hr]
  apply congrArg ((1 / ((r + 1 : Nat) : Real) ^ 2) * ·)
  unfold isingTorusAxisSegment
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      exact finiteTorusZeroModeGreen_axisDifference i a b
    · intro b hb c hc hbc
      exact isingTorusCoordinateShift_injectiveOn_range i r hr
        (by simpa using hb) (by simpa using hc) hbc
  · intro a ha b hb hab
    exact isingTorusCoordinateShift_injectiveOn_range i r hr
      (by simpa using ha) (by simpa using hb) hab

theorem isingTorusAxisSegment_nonempty (i : Fin d) (r : Nat) :
    (isingTorusAxisSegment (k := k) i r).Nonempty := by
  refine ⟨isingTorusCoordinateShift i 0, ?_⟩
  rw [isingTorusAxisSegment, Finset.mem_image]
  exact ⟨0, by simp, rfl⟩


noncomputable def isingTorusSparseAxisBlock
    (i : Fin d) (spacing count : Nat) :
    Finset (IsingDyadicTorus d k) :=
  (Finset.range count).image fun j =>
    isingTorusCoordinateShift i (j * spacing)

theorem isingTorusSparseAxisBlock_nonempty
    (i : Fin d) (spacing count : Nat) (hcount : 0 < count) :
    (isingTorusSparseAxisBlock (k := k) i spacing count).Nonempty := by
  refine ⟨isingTorusCoordinateShift i 0, ?_⟩
  rw [isingTorusSparseAxisBlock, Finset.mem_image]
  refine ⟨0, by simp [hcount], ?_⟩
  simp

theorem isingTorusSparseAxisBlock_card
    (i : Fin d) (spacing count : Nat) (hspacing : 0 < spacing)
    (hr : (count - 1) * spacing < isingDyadicSide k) :
    (isingTorusSparseAxisBlock (k := k) i spacing count).card = count := by
  unfold isingTorusSparseAxisBlock
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have haCount : a < count := by simpa using ha
    have hbCount : b < count := by simpa using hb
    have haEnd : a * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hbEnd : b * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hmul := isingTorusCoordinateShift_injectiveOn_range
      (k := k) i ((count - 1) * spacing) hr
      (by simpa using haEnd) (by simpa using hbEnd) hab
    exact Nat.eq_of_mul_eq_mul_right hspacing hmul



theorem finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis
    (i : Fin d) (spacing count : Nat) (hspacing : 0 < spacing)
    (hr : (count - 1) * spacing < isingDyadicSide k) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusSparseAxisBlock i spacing count) =
      (1 / (count : Real) ^ 2) *
        ∑ a ∈ Finset.range count,
          ∑ b ∈ Finset.range count,
            isingDyadicTorusGreen
              (Pi.single i (((b * spacing : Nat) : Int) -
                ((a * spacing : Nat) : Int))) k := by
  unfold finiteTorusBlockDifferenceAverage
  rw [isingTorusSparseAxisBlock_card i spacing count hspacing hr]
  apply congrArg ((1 / (count : Real) ^ 2) * ·)
  unfold isingTorusSparseAxisBlock
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      exact finiteTorusZeroModeGreen_axisDifference
        i (a * spacing) (b * spacing)
    · intro b hb c hc hbc
      have hbCount : b < count := by simpa using hb
      have hcCount : c < count := by simpa using hc
      have hbEnd : b * spacing < (count - 1) * spacing + 1 := by
        apply Nat.lt_succ_of_le
        exact Nat.mul_le_mul_right spacing (by omega)
      have hcEnd : c * spacing < (count - 1) * spacing + 1 := by
        apply Nat.lt_succ_of_le
        exact Nat.mul_le_mul_right spacing (by omega)
      have hmul := isingTorusCoordinateShift_injectiveOn_range
        (k := k) i ((count - 1) * spacing) hr
        (by simpa using hbEnd) (by simpa using hcEnd) hbc
      exact Nat.eq_of_mul_eq_mul_right hspacing hmul
  · intro a ha b hb hab
    have haCount : a < count := by simpa using ha
    have hbCount : b < count := by simpa using hb
    have haEnd : a * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hbEnd : b * spacing < (count - 1) * spacing + 1 := by
      apply Nat.lt_succ_of_le
      exact Nat.mul_le_mul_right spacing (by omega)
    have hmul := isingTorusCoordinateShift_injectiveOn_range
      (k := k) i ((count - 1) * spacing) hr
      (by simpa using haEnd) (by simpa using hbEnd) hab
    exact Nat.eq_of_mul_eq_mul_right hspacing hmul



theorem finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis_le
    (i : Fin d) (spacing count : Nat) (hspacing : 0 < spacing)
    (hcount : 0 < count)
    (hr : (count - 1) * spacing < isingDyadicSide k)
    (M epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (hzero : |isingDyadicTorusGreen (0 : StatMech.Lattice.Site d) k| ≤ M)
    (hoff : ∀ a ∈ Finset.range count, ∀ b ∈ Finset.range count,
      a ≠ b →
        |isingDyadicTorusGreen
          (Pi.single i (((b * spacing : Nat) : Int) -
            ((a * spacing : Nat) : Int))) k| ≤ epsilon) :
    finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusSparseAxisBlock i spacing count) ≤
      M / count + epsilon := by
  rw [finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis
    i spacing count hspacing hr]
  let G : Nat → Nat → Real := fun a b =>
    isingDyadicTorusGreen
      (Pi.single i (((b * spacing : Nat) : Int) -
        ((a * spacing : Nat) : Int))) k
  have hinner (a : Nat) (ha : a ∈ Finset.range count) :
      ∑ b ∈ Finset.range count, G a b ≤
        M + (count : Real) * epsilon := by
    have hoff' : ∑ b ∈ (Finset.range count).erase a, |G a b| ≤
        ∑ _b ∈ (Finset.range count).erase a, epsilon := by
      apply Finset.sum_le_sum
      intro b hb
      exact hoff a ha b (Finset.mem_of_mem_erase hb)
        (Finset.ne_of_mem_erase hb).symm
    have hsumAbs : ∑ b ∈ Finset.range count, |G a b| ≤
        M + (count : Real) * epsilon := by
      have hdiag : |G a a| ≤ M := by
        simpa [G] using hzero
      rw [← Finset.sum_erase_add _ _ ha]
      calc
        (∑ b ∈ (Finset.range count).erase a, |G a b|) + |G a a| ≤
            (∑ _b ∈ (Finset.range count).erase a, epsilon) + M :=
          add_le_add hoff' hdiag
        _ ≤ M + (count : Real) * epsilon := by
          have hcard : ((Finset.range count).erase a).card ≤ count := by
            simpa using (Finset.card_erase_le :
              ((Finset.range count).erase a).card ≤
                (Finset.range count).card)
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hmul := mul_le_mul_of_nonneg_right
            (show (((Finset.range count).erase a).card : Real) ≤ count by
              exact_mod_cast hcard) hepsilon
          linarith
    exact (Finset.sum_le_sum fun b _ => le_abs_self (G a b)).trans hsumAbs
  have hsum :
      ∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b ≤
        (count : Real) * (M + (count : Real) * epsilon) := by
    calc
      ∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b ≤
          ∑ _a ∈ Finset.range count,
            (M + (count : Real) * epsilon) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hinner a ha
      _ = (count : Real) * (M + (count : Real) * epsilon) := by
        simp
        ring
  change (1 / (count : Real) ^ 2) *
      (∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b) ≤ _
  calc
    (1 / (count : Real) ^ 2) *
        (∑ a ∈ Finset.range count, ∑ b ∈ Finset.range count, G a b) ≤
      (1 / (count : Real) ^ 2) *
        ((count : Real) * (M + (count : Real) * epsilon)) := by
          gcongr
    _ = M / count + epsilon := by
      have hc : (count : Real) ≠ 0 := by exact_mod_cast hcount.ne'
      field_simp



theorem isingTorusTwoPoint_axis_antitone
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    {a b : Nat} (hab : a ≤ b) (hb : b ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i b) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i a) := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (isingTorusAxisCorrelation_succ_le
        (k := k) i beta hbeta b (by omega)).trans (ih (by omega))

private theorem isingTorusCoordinateShift_sub_of_le
    (i : Fin d) {a b : Nat} (hab : a ≤ b) :
    isingTorusCoordinateShift (k := k) i b -
        isingTorusCoordinateShift i a =
      isingTorusCoordinateShift i (b - a) := by
  have hadd := isingTorusCoordinateShift_add (k := k) i a (b - a)
  rw [Nat.add_sub_of_le hab] at hadd
  rw [hadd]
  abel



theorem isingTorusTwoPoint_axisEndpoint_le_difference
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1))
    {a b : Nat} (ha : a < r + 1) (hb : b < r + 1) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i b -
          isingTorusCoordinateShift i a) := by
  rcases le_total a b with hab | hba
  · rw [isingTorusCoordinateShift_sub_of_le i hab]
    exact isingTorusTwoPoint_axis_antitone i beta hbeta
      (Nat.sub_le b a |>.trans (by omega)) hr
  · have hsub := isingTorusCoordinateShift_sub_of_le
      (k := k) i hba
    have hneg : isingTorusCoordinateShift (k := k) i b -
          isingTorusCoordinateShift i a =
        -isingTorusCoordinateShift i (a - b) := by
      calc
        isingTorusCoordinateShift (k := k) i b -
            isingTorusCoordinateShift i a =
          -(isingTorusCoordinateShift i a -
            isingTorusCoordinateShift i b) := by abel
        _ = -isingTorusCoordinateShift i (a - b) :=
          congrArg Neg.neg hsub
    rw [hneg, isingTorusTwoPoint_origin_neg]
    exact isingTorusTwoPoint_axis_antitone i beta hbeta
      (Nat.sub_le a b |>.trans (by omega)) hr



theorem isingTorusTwoPoint_sparseAxisEndpoint_le_difference
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (spacing count : Nat) (hcount : 0 < count)
    (hr : (count - 1) * spacing ≤ 2 ^ (k + 1))
    {a b : Nat} (ha : a < count) (hb : b < count) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i ((count - 1) * spacing)) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i (b * spacing) -
          isingTorusCoordinateShift i (a * spacing)) := by
  apply isingTorusTwoPoint_axisEndpoint_le_difference
    i beta hbeta ((count - 1) * spacing) hr
  · apply Nat.lt_succ_of_le
    exact Nat.mul_le_mul_right spacing (by omega)
  · apply Nat.lt_succ_of_le
    exact Nat.mul_le_mul_right spacing (by omega)



theorem isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_of_block
    (i : Fin d) (beta : Real) (hbeta : 0 < beta) (r : Nat)
    (B : Finset (IsingDyadicTorus d k)) (hB : B.Nonempty)
    (hlower : ∀ a ∈ B, ∀ b ∈ B,
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i r) ≤
        isingTorusTwoPoint (k := k) beta 0 (b - a)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / beta) * finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k)
          (isingTorusCharacterDispersion (d := d) (k := k))) B := by
  let G : IsingDyadicTorus d k → Real :=
    fun z => isingTorusTwoPoint beta 0 z
  have hkernel : G = isingTorusAveragedTwoPoint beta := by
    funext z
    exact (isingTorusAveragedTwoPoint_eq_twoPoint beta z).symm
  have hblockLower :
      isingTorusTwoPoint beta 0 (isingTorusCoordinateShift i r) ≤
        finiteTorusBlockDifferenceAverage G B :=
    le_finiteTorusBlockDifferenceAverage G B _ hB hlower
  have hblockUpper := finiteTorusBlockDifferenceAverage_le
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
  refine hblockLower.trans (hblockUpper.trans_eq ?_)
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
    intro chi hchi
    ring
  rw [hsum]
  ring



theorem isingTorusTwoPoint_sparseAxisEndpoint_le_greenBlockAverage
    (i : Fin d) (beta : Real) (hbeta : 0 < beta)
    (spacing count : Nat) (hcount : 0 < count)
    (hr : (count - 1) * spacing ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i ((count - 1) * spacing)) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / beta) * finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k)
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusSparseAxisBlock (k := k) i spacing count) := by
  apply isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage_of_block
    i beta hbeta ((count - 1) * spacing)
    (isingTorusSparseAxisBlock i spacing count)
    (isingTorusSparseAxisBlock_nonempty i spacing count hcount)
  intro a ha b hb
  rw [isingTorusSparseAxisBlock, Finset.mem_image] at ha hb
  obtain ⟨aIndex, haIndex, rfl⟩ := ha
  obtain ⟨bIndex, hbIndex, rfl⟩ := hb
  exact isingTorusTwoPoint_sparseAxisEndpoint_le_difference
    i beta hbeta.le spacing count hcount hr
      (by simpa using haIndex) (by simpa using hbIndex)



theorem isingTorusTwoPoint_axisEndpoint_le_blockDifferenceAverage
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      finiteTorusBlockDifferenceAverage
        (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z)
        (isingTorusAxisSegment i r) := by
  apply le_finiteTorusBlockDifferenceAverage _ _ _
    (isingTorusAxisSegment_nonempty i r)
  intro a ha b hb
  rw [isingTorusAxisSegment, Finset.mem_image] at ha hb
  obtain ⟨aIndex, haIndex, rfl⟩ := ha
  obtain ⟨bIndex, hbIndex, rfl⟩ := hb
  exact isingTorusTwoPoint_axisEndpoint_le_difference
    i beta hbeta r hr (by simpa using haIndex) (by simpa using hbIndex)




theorem isingTorusTwoPoint_axisEndpoint_le_fourierBlockBound
    (i : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / Fintype.card (IsingDyadicTorus d k) : Real) *
        ∑ chi ∈ Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex),
          ((1 / beta) / isingTorusCharacterDispersion chi) *
            finiteTorusBlockCharacterWeight
              (isingTorusAxisSegment i r) chi := by
  let G : IsingDyadicTorus d k → Real :=
    fun z => isingTorusTwoPoint beta 0 z
  have hkernel : G = isingTorusAveragedTwoPoint beta := by
    funext z
    exact (isingTorusAveragedTwoPoint_eq_twoPoint beta z).symm
  have hlower :=
    isingTorusTwoPoint_axisEndpoint_le_blockDifferenceAverage
      (k := k) i beta hbeta.le r hr
  have hupper := finiteTorusBlockDifferenceAverage_le
    G (isingTorusAxisSegment i r) (1 / beta)
      isingTorusCharacterDispersion
      (isingTorusAxisSegment_nonempty i r)
      (fun chi => by
        rw [hkernel, finiteTorusFourierCoeff_isingTorusAveragedTwoPoint]
        rfl)
      (fun chi hchi => by
        rw [hkernel]
        have hdisp := isingTorusCharacterDispersion_pos_of_ne_zero chi hchi
        have hbound := isingTorusAveragedTwoPoint_fourier_bound beta hbeta
          (isingTorus_gaussianDominated beta hbeta.le) chi hdisp
        convert hbound using 1 <;> ring)
  exact hlower.trans (by simpa only [G] using hupper)




theorem isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage
    (i : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r : Nat) (hr : r ≤ 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) +
      (1 / beta) * finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen (Gamma := IsingDyadicTorus d k)
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusAxisSegment (k := k) i r) := by
  have hbound := isingTorusTwoPoint_axisEndpoint_le_fourierBlockBound
    (k := k) i beta hbeta r hr
  have hgreen := finiteTorusBlockDifferenceAverage_zeroModeGreen
    (isingTorusCharacterDispersion (d := d) (k := k))
    (isingTorusAxisSegment (k := k) i r)
  rw [hgreen]
  exact hbound.trans_eq (by
    congr 1
    have hsum :
        (∑ chi ∈ Finset.univ.erase
            (0 : AddChar (IsingDyadicTorus d k) Complex),
          ((1 / beta) / isingTorusCharacterDispersion chi) *
            finiteTorusBlockCharacterWeight
              (isingTorusAxisSegment i r) chi) =
          (1 / beta) *
            ∑ chi ∈ Finset.univ.erase
              (0 : AddChar (IsingDyadicTorus d k) Complex),
            (isingTorusCharacterDispersion chi)⁻¹ *
              finiteTorusBlockCharacterWeight
                (isingTorusAxisSegment i r) chi := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi hchi
      ring
    rw [hsum]
    ring)

end StatMech.FrontierA
