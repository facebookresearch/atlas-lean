/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingDyadicGreenGrid
import Code.FrontierA.IsingInfraredMomentumShell

open Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

open Lattice

variable {d k M : Nat}

theorem isingTorusLowMomentum_centeredInt_mem_box
    {p : IsingDyadicTorus d k} (hp : p ∈ isingTorusLowMomentum d k M) :
    isingTorusCenteredIntMomentum p ∈
      integerMomentumBoxWithoutZero d M := by
  rw [isingTorusLowMomentum_mem_iff] at hp
  rw [integerMomentumBoxWithoutZero, Finset.mem_sdiff,
    boxSV_mem_boxF, Finset.mem_singleton]
  constructor
  · intro i
    rw [Finset.mem_Icc]
    have hi := hp.2 i
    have habs : |(p i).valMinAbs| ≤ (M : Int) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hi
    exact abs_le.mp habs
  · intro hz
    apply hp.1
    apply isingTorusCenteredIntMomentum_injective
    have hzero : isingTorusCenteredIntMomentum
        (0 : IsingDyadicTorus d k) = 0 := by
      funext i
      simp [isingTorusCenteredIntMomentum]
    exact hz.trans hzero.symm



theorem isingTorusCharacterDispersion_centered_lower
    {p : IsingDyadicTorus d k}
    (hp : p ∈ isingTorusLowMomentum d k M)
    (hM : M ≤ isingDyadicSide k / 2) :
    (16 / (isingDyadicSide k : Real) ^ 2) *
        integerMomentumNormSq (isingTorusCenteredIntMomentum p) ≤
      isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
  rw [isingTorusLowMomentum_mem_iff] at hp
  rw [isingTorusCharacterDispersion_centered]
  unfold integerMomentumNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let z : Real := ((p i).valMinAbs : Real)
  let L : Real := isingDyadicSide k
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast isingDyadicSide_pos k
  have hzAbs : |z| ≤ (M : Real) := by
    dsimp [z]
    calc
      |((p i).valMinAbs : Real)| = ((p i).valMinAbs.natAbs : Real) := by
        generalize (p i).valMinAbs = a
        cases a with
        | ofNat n => simp
        | negSucc n =>
            simp only [Int.cast_negSucc, Int.natAbs_negSucc,
              Nat.cast_add, Nat.cast_one]
            have hn : -((n : Real) + 1) ≤ 0 := neg_nonpos.mpr (by positivity)
            rw [abs_of_nonpos hn]
            norm_cast
      _ ≤ (M : Real) := by exact_mod_cast hp.2 i
  have hML : (2 : Real) * M ≤ L := by
    dsimp [L]
    exact_mod_cast (show 2 * M ≤ isingDyadicSide k by omega)
  have harg : |2 * Real.pi * (z / L)| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]
    rw [abs_div, abs_of_pos hL]
    have hpi := Real.pi_pos.le
    calc
      (2 * Real.pi) * (|z| / L) ≤
          (2 * Real.pi) * ((M : Real) / L) := by gcongr
      _ ≤ Real.pi := by
        calc
          (2 * Real.pi) * ((M : Real) / L) =
              (2 * Real.pi * M) / L := by ring
          _ ≤ Real.pi := (div_le_iff₀ hL).2 (by
            nlinarith [Real.pi_pos])
  have hcos := Real.cos_le_one_sub_mul_cos_sq harg
  have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hquad :
      (4 / Real.pi ^ 2) * (2 * Real.pi * (z / L)) ^ 2 ≤
        2 - 2 * Real.cos (2 * Real.pi * (z / L)) := by
    calc
      (4 / Real.pi ^ 2) * (2 * Real.pi * (z / L)) ^ 2 =
          2 * ((2 / Real.pi ^ 2) *
            (2 * Real.pi * (z / L)) ^ 2) := by ring
      _ ≤ 2 * (1 - Real.cos (2 * Real.pi * (z / L))) := by
        gcongr
        linarith
      _ = 2 - 2 * Real.cos (2 * Real.pi * (z / L)) := by ring
  change (16 / L ^ 2) * z ^ 2 ≤
    2 - 2 * Real.cos (2 * Real.pi * (z / L))
  calc
    (16 / L ^ 2) * z ^ 2 =
        (4 / Real.pi ^ 2) * (2 * Real.pi * (z / L)) ^ 2 := by
      field_simp [hL.ne', Real.pi_ne_zero]
      ring
    _ ≤ 2 - 2 * Real.cos (2 * Real.pi * (z / L)) := hquad

theorem isingTorusLowMomentum_inverseDispersion_term_le
    {p : IsingDyadicTorus d k}
    (hp : p ∈ isingTorusLowMomentum d k M)
    (hM : M ≤ isingDyadicSide k / 2) :
    (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ ≤
      ((isingDyadicSide k : Real) ^ 2 / 16) *
        (integerMomentumNormSq (isingTorusCenteredIntMomentum p))⁻¹ := by
  have hpBox := isingTorusLowMomentum_centeredInt_mem_box hp
  have hp0 : isingTorusCenteredIntMomentum p ≠ 0 := by
    intro hp0
    exact (Finset.mem_sdiff.mp hpBox).2 (by simpa [hp0])
  have hnorm := integerMomentumNormSq_pos hp0
  have hcoef : 0 < 16 / (isingDyadicSide k : Real) ^ 2 := by
    have hside : (0 : Real) < isingDyadicSide k := by
      exact_mod_cast isingDyadicSide_pos k
    exact div_pos (by norm_num) (sq_pos_of_pos hside)
  have hlower := isingTorusCharacterDispersion_centered_lower hp hM
  calc
    (isingTorusCharacterDispersion (isingTorusMomentumChar p))⁻¹ ≤
        ((16 / (isingDyadicSide k : Real) ^ 2) *
          integerMomentumNormSq (isingTorusCenteredIntMomentum p))⁻¹ :=
      inv_anti₀ (mul_pos hcoef hnorm) hlower
    _ = ((isingDyadicSide k : Real) ^ 2 / 16) *
        (integerMomentumNormSq (isingTorusCenteredIntMomentum p))⁻¹ := by
      field_simp

theorem sum_inv_integerMomentumNormSq_lowMomentum_le_box
    (d k M : Nat) :
    ∑ p ∈ isingTorusLowMomentum d k M,
        (integerMomentumNormSq (isingTorusCenteredIntMomentum p))⁻¹ ≤
      ∑ m ∈ integerMomentumBoxWithoutZero d M,
        (integerMomentumNormSq m)⁻¹ := by
  classical
  let f : IsingDyadicTorus d k → Site d :=
    isingTorusCenteredIntMomentum
  have hinj : Set.InjOn f (isingTorusLowMomentum d k M : Set _) :=
    isingTorusCenteredIntMomentum_injective.injOn
  have hsubset : (isingTorusLowMomentum d k M).image f ⊆
      integerMomentumBoxWithoutZero d M := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    exact isingTorusLowMomentum_centeredInt_mem_box hp
  calc
    ∑ p ∈ isingTorusLowMomentum d k M,
        (integerMomentumNormSq (isingTorusCenteredIntMomentum p))⁻¹ =
        ∑ m ∈ (isingTorusLowMomentum d k M).image f,
          (integerMomentumNormSq m)⁻¹ := by
      symm
      simpa only [f] using
        (Finset.sum_image
          (f := fun m ↦ (integerMomentumNormSq m)⁻¹) hinj)
    _ ≤ ∑ m ∈ integerMomentumBoxWithoutZero d M,
        (integerMomentumNormSq m)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun m _ _ ↦ inv_nonneg.mpr (integerMomentumNormSq_nonneg m))



theorem isingTorusLowMomentum_inverseDispersion_le
    {d : Nat} (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ k M,
      1 ≤ M → M ≤ isingDyadicSide k / 2 →
      (1 / (isingDyadicSide k : Real) ^ d) *
          ∑ p ∈ isingTorusLowMomentum d k M,
            (isingTorusCharacterDispersion
              (isingTorusMomentumChar p))⁻¹ ≤
        C * ((M : Real) / isingDyadicSide k) ^ (d - 2) := by
  let C : Real := (2 * d * 3 ^ (d - 1)) / 16
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  intro k M hMpos hMhalf
  have hL : (0 : Real) < isingDyadicSide k := by
    exact_mod_cast isingDyadicSide_pos k
  have hsumTerm :
      ∑ p ∈ isingTorusLowMomentum d k M,
          (isingTorusCharacterDispersion
            (isingTorusMomentumChar p))⁻¹ ≤
        ((isingDyadicSide k : Real) ^ 2 / 16) *
          ∑ p ∈ isingTorusLowMomentum d k M,
            (integerMomentumNormSq
              (isingTorusCenteredIntMomentum p))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp ↦
      isingTorusLowMomentum_inverseDispersion_term_le hp hMhalf
  have hbox := sum_inv_integerMomentumNormSq_box_le_power d M hd
  have hlow := sum_inv_integerMomentumNormSq_lowMomentum_le_box d k M
  calc
    (1 / (isingDyadicSide k : Real) ^ d) *
        ∑ p ∈ isingTorusLowMomentum d k M,
          (isingTorusCharacterDispersion
            (isingTorusMomentumChar p))⁻¹ ≤
        (1 / (isingDyadicSide k : Real) ^ d) *
          (((isingDyadicSide k : Real) ^ 2 / 16) *
            ∑ p ∈ isingTorusLowMomentum d k M,
              (integerMomentumNormSq
                (isingTorusCenteredIntMomentum p))⁻¹) := by
      gcongr
    _ ≤ (1 / (isingDyadicSide k : Real) ^ d) *
          (((isingDyadicSide k : Real) ^ 2 / 16) *
            ∑ m ∈ integerMomentumBoxWithoutZero d M,
              (integerMomentumNormSq m)⁻¹) := by
      gcongr
    _ ≤ (1 / (isingDyadicSide k : Real) ^ d) *
          (((isingDyadicSide k : Real) ^ 2 / 16) *
            (2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2))) := by
      gcongr
    _ = C * ((M : Real) / isingDyadicSide k) ^ (d - 2) := by
      dsimp [C]
      rw [div_pow]
      field_simp [hL.ne']
      rw [← pow_add]
      congr 2
      omega

end StatMech.FrontierA
