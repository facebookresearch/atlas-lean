/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Classical.MeioticDrive
public import Mathlib.Tactic.NormNum

/-!
# Tests for allele frequency under meiotic drive

The fair coin gives Mendel's law; a concrete coin and genotype law exercise the recursion from
the genotype model; the boundary values `k = 0`, `k = 1/2`, `k = 1` and the endpoints `p = 0`,
`p = 1` check the map and the three regimes; `k = 2` shows that the range clause needs
`k ≤ 1`.
-/

@[expose] public section

open Filter Set Topology
open MathlibExt.Biology.PopulationGenetics.HardyWeinberg
open MathlibExt.Biology.PopulationGenetics.Classical.MeioticDrive

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.MeioticDrive

-- With the fair coin, drive transmission is Mendelian segregation.
example : driveTransmit (PMF.uniformFintype Bool) = transmit := by
  funext g
  ext a
  obtain ⟨b, c⟩ := g
  rw [transmit_apply]
  cases b <;> cases c <;> cases a <;>
    simp [driveTransmit, PMF.uniformFintype_apply, ENNReal.inv_two_add_inv_two]

-- A coin transmitting `A` with probability `3/4`.
noncomputable def coin34 : PMF Bool :=
  PMF.ofFintype (fun b => cond b (3 / 4) (1 / 4)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, ENNReal.div_add_div_same]
    norm_num [ENNReal.div_self])

example : (coin34 true).toReal = 3 / 4 := by
  simp only [coin34, PMF.ofFintype_apply, Bool.cond_true]
  rw [ENNReal.toReal_div]
  norm_num

-- End to end: newborns of a population of heterozygous parents are in Hardy–Weinberg
-- proportions with `p = 1/2`; with `k = 3/4` the next newborns have `p' = 5/8`.
example :
    (gamete (driveOffspring coin34 (offspring (PMF.pure (true, false)))) true).toReal = 5 / 8 := by
  have hk : (coin34 true).toReal = 3 / 4 := by
    simp only [coin34, PMF.ofFintype_apply, Bool.cond_true]
    rw [ENNReal.toReal_div]
    norm_num
  have hp : (gamete (offspring (PMF.pure (true, false))) true).toReal = 1 / 2 := by
    rw [gamete_offspring, gamete_apply]
    simp [PMF.pure_apply, ENNReal.toReal_inv]
  obtain ⟨hmodel, -⟩ := allele_frequency_under_meiotic_drive (k := 3 / 4) (by norm_num)
  obtain ⟨-, hfreq, -⟩ := hmodel coin34 _ hk (offspring_offspring _)
  rw [hfreq, hp]
  norm_num [driveStep]

-- The map at `k = 3/4`, `p = 1/2`, and the change `pq(2k - 1) = 1/8`.
example : driveStep (3 / 4) (1 / 2) = 5 / 8 := by norm_num [driveStep]

example : driveStep (3 / 4) (1 / 2) - 1 / 2 = 1 / 8 := by
  obtain ⟨-, hsub, -⟩ := allele_frequency_under_meiotic_drive (k := 3 / 4) (by norm_num)
  rw [hsub]
  norm_num

-- Complete drive against `A` (`k = 0`) squares the frequency of `A`; complete drive for `A`
-- (`k = 1`) squares the frequency of `a`.
example (p : ℝ) : driveStep 0 p = p ^ 2 := by simp [driveStep]

example (p : ℝ) : 1 - driveStep 1 p = (1 - p) ^ 2 := by unfold driveStep; ring

-- Fixation and loss are fixed for every `k`.
example (k : ℝ) : driveStep k 0 = 0 ∧ driveStep k 1 = 1 := by
  constructor <;> norm_num [driveStep]

-- The three regimes at the extreme and Mendelian values of `k`.
example : StrictMono (fun t => (driveStep 1)^[t] (1 / 2)) ∧
    Tendsto (fun t => (driveStep 1)^[t] (1 / 2)) atTop (𝓝 1) := by
  obtain ⟨-, -, -, hreg⟩ := allele_frequency_under_meiotic_drive (k := 1) (by norm_num)
  exact (hreg (1 / 2) (by norm_num)).1 (by norm_num)

example : StrictAnti (fun t => (driveStep 0)^[t] (9 / 10)) ∧
    Tendsto (fun t => (driveStep 0)^[t] (9 / 10)) atTop (𝓝 0) := by
  obtain ⟨-, -, -, hreg⟩ := allele_frequency_under_meiotic_drive (k := 0) (by norm_num)
  exact (hreg (9 / 10) (by norm_num)).2.1 (by norm_num)

example (t : ℕ) : (driveStep (1 / 2))^[t] (1 / 3) = 1 / 3 := by
  obtain ⟨-, -, -, hreg⟩ := allele_frequency_under_meiotic_drive (k := 1 / 2) (by norm_num)
  exact (hreg (1 / 3) (by norm_num)).2.2 rfl t

-- Without `k ≤ 1` the map can leave `[0, 1]`.
example : driveStep 2 (1 / 2) = 5 / 4 := by norm_num [driveStep]

end MathlibExtTest.Biology.PopulationGenetics.Classical.MeioticDrive
