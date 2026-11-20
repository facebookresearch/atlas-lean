/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusAxisBlockAverage
import Code.FrontierA.IsingTorusEmbedding

open Filter Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : Nat}

theorem sparseAxisDifference_not_mem_box
    (i : Fin d) (R spacing a b : Nat) (hspacing : R < spacing)
    (hab : a ≠ b) :
    Pi.single i (((b * spacing : Nat) : Int) -
      ((a * spacing : Nat) : Int)) ∉ box d R := by
  intro hbox
  have hi := hbox i
  simp only [Pi.single_eq_same] at hi
  have habOrder : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab
  rcases habOrder with habOrder | habOrder
  · have hba : a * spacing ≤ b * spacing :=
      Nat.mul_le_mul_right spacing habOrder.le
    have hdiff : 1 ≤ b - a := by omega
    have hlarge : spacing ≤ (b - a) * spacing := by
      simpa only [one_mul] using Nat.mul_le_mul_right spacing hdiff
    have heq :
        ((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int) =
          (((b - a) * spacing : Nat) : Int) := by
      exact (Int.ofNat_sub hba).symm.trans
        (congrArg (fun n : Nat => (n : Int)) (Nat.sub_mul b a spacing).symm)
    have hcast :
        (((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int)).natAbs =
          (b - a) * spacing := by
      rw [heq]
      rfl
    rw [hcast] at hi
    omega
  · have habMul : b * spacing ≤ a * spacing :=
      Nat.mul_le_mul_right spacing habOrder.le
    have hdiff : 1 ≤ a - b := by omega
    have hlarge : spacing ≤ (a - b) * spacing := by
      simpa only [one_mul] using Nat.mul_le_mul_right spacing hdiff
    have heq :
        ((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int) =
          -(((a - b) * spacing : Nat) : Int) := by
      calc
        ((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int) =
            -(((a * spacing : Nat) : Int) -
              ((b * spacing : Nat) : Int)) := by ring
        _ = -(((a * spacing - b * spacing : Nat) : Int)) := by
          rw [Int.ofNat_sub habMul]
        _ = -((((a - b) * spacing : Nat) : Int)) := by
          rw [Nat.sub_mul]
    have hcast :
        (((b * spacing : Nat) : Int) - ((a * spacing : Nat) : Int)).natAbs =
          (a - b) * spacing := by
      rw [heq, Int.natAbs_neg]
      rfl
    rw [hcast] at hi
    omega




theorem isingTorusSparseGreenAverage_eventually_le
    (hd : 2 < d) (delta : Real) (hdelta : 0 < delta) :
    ∃ M : Real, 0 ≤ M ∧ ∃ R : Nat,
      ∀ (i : Fin d) (spacing count : Nat), R < spacing → 0 < count →
        ∀ᶠ k : Nat in atTop,
          finiteTorusBlockDifferenceAverage
              (finiteTorusZeroModeGreen
                (isingTorusCharacterDispersion (d := d) (k := k)))
              (isingTorusSparseAxisBlock i spacing count) ≤
            M / count + delta := by
  obtain ⟨eta, heta, hclose⟩ :=
    isingDyadicTorusGreen_eventually_close_continuum hd 1 zero_lt_one
  let M : Real := |isingRegularizedContinuumGreen eta (0 : Site d)| + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨R, hfar⟩ :=
    isingDyadicTorusGreen_eventually_small_outside_box hd delta hdelta
  refine ⟨M, hM, R, ?_⟩
  intro i spacing count hspacing hcount
  have hside : ∀ᶠ k : Nat in atTop,
      (count - 1) * spacing < isingDyadicSide k := by
    have htendsto : Tendsto isingDyadicSide atTop atTop := by
      unfold isingDyadicSide
      rw [Filter.tendsto_add_atTop_iff_nat]
      exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
    exact htendsto.eventually_gt_atTop ((count - 1) * spacing)
  have hzero : ∀ᶠ k : Nat in atTop,
      |isingDyadicTorusGreen (0 : Site d) k| ≤ M := by
    filter_upwards [hclose (0 : Site d)] with k hk
    dsimp [M]
    calc
      |isingDyadicTorusGreen (0 : Site d) k| =
          |(isingDyadicTorusGreen (0 : Site d) k -
            isingRegularizedContinuumGreen eta 0) +
              isingRegularizedContinuumGreen eta 0| := by congr 1 <;> ring
      _ ≤
          |isingDyadicTorusGreen (0 : Site d) k -
            isingRegularizedContinuumGreen eta 0| +
              |isingRegularizedContinuumGreen eta 0| := by
        exact abs_add_le _ _
      _ ≤ 1 + |isingRegularizedContinuumGreen eta 0| := by
        gcongr
      _ = |isingRegularizedContinuumGreen eta 0| + 1 := by
        rw [add_comm]
  have hoff : ∀ᶠ k : Nat in atTop,
      ∀ a ∈ Finset.range count, ∀ b ∈ Finset.range count, a ≠ b →
        |isingDyadicTorusGreen
          (Pi.single i (((b * spacing : Nat) : Int) -
            ((a * spacing : Nat) : Int))) k| ≤ delta := by
    rw [Filter.eventually_all_finset (Finset.range count)]
    intro a ha
    rw [Filter.eventually_all_finset (Finset.range count)]
    intro b hb
    by_cases hab : a = b
    · filter_upwards with k
      exact fun hne => (hne hab).elim
    · filter_upwards [hfar _
          (sparseAxisDifference_not_mem_box i R spacing a b hspacing hab)] with k hk
      exact fun _ => hk.le
  filter_upwards [hside, hzero, hoff] with k hsideK hzeroK hoffK
  exact finiteTorusBlockDifferenceAverage_zeroModeGreen_sparseAxis_le
    i spacing count (by omega) hcount hsideK M delta hdelta.le hzeroK hoffK



theorem isingTorusZeroMode_eventually_small_subcritical
    (hd : 2 ≤ d) (beta : Real) (hbeta : 0 ≤ beta)
    (hlt : beta < IsingFK.betaC (StatMech.Ising.magnetization d))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
        Fintype.card (IsingDyadicTorus d k) < epsilon := by
  obtain ⟨C, hC, hsusc⟩ :=
    isingTorus_susceptibility_eventually_bounded_subcritical
      hd beta hbeta hlt
  have hsideNat : Tendsto isingDyadicSide atTop atTop := by
    unfold isingDyadicSide
    rw [Filter.tendsto_add_atTop_iff_nat]
    exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
  have hsideReal : Tendsto (fun k => (isingDyadicSide k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hsideNat
  have hlarge : ∀ᶠ k : Nat in atTop,
      C / epsilon < (isingDyadicSide k : Real) :=
    hsideReal.eventually_gt_atTop (C / epsilon)
  filter_upwards [hsusc, hlarge] with k hk hlargeK
  have hsideOne : (1 : Real) ≤ isingDyadicSide k := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (isingDyadicSide_pos k).ne')
  have hsideCard : (isingDyadicSide k : Real) ≤
      Fintype.card (IsingDyadicTorus d k) := by
    rw [isingDyadicTorus_card]
    push_cast
    simpa only [pow_one] using
      (pow_le_pow_right₀ hsideOne (by omega : 1 ≤ d) :
        (isingDyadicSide k : Real) ^ 1 ≤
          (isingDyadicSide k : Real) ^ d)
  have hcardPos : (0 : Real) < Fintype.card (IsingDyadicTorus d k) := by
    positivity
  have hCcard : C < epsilon * Fintype.card (IsingDyadicTorus d k) := by
    have hfirst : C < epsilon * isingDyadicSide k := by
      simpa [mul_comm] using (div_lt_iff₀ hepsilon).mp hlargeK
    exact hfirst.trans_le (mul_le_mul_of_nonneg_left hsideCard hepsilon.le)
  have hcoeff :
      (finiteTorusFourierCoeff
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re =
        ∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 z := by
    simp [finiteTorusFourierCoeff]
  rw [hcoeff, div_lt_iff₀ hcardPos]
  exact hk.trans_lt hCcard

end StatMech.FrontierA
