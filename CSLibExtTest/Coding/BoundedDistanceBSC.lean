/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.BoundedDistanceBSC
import Mathlib.Tactic.NormNum

@[expose] public section

open Cslib.CodingTheory.BoundedDistanceBSC ProbabilityTheory

namespace Cslib.CodingTheory.BoundedDistanceBSCTests

/-- The canonical binomial tail at concrete values:
`binomTail 7 2 (1/2) = (2^7 - 1 - 7) / 2^7 = 15/16`. -/
example : ProbabilityTheory.binomTail 7 2 (1 / 2 : ℝ) = 15 / 16 := by
  norm_num [ProbabilityTheory.binomTail, Finset.sum_Icc_succ_top, Nat.choose]

/-- The weight distribution identity at the same values, through
the public theorem: the probability that at least 2 of 7 symbols
flip at crossover `1/2` is `15/16`. -/
example : (bscMeasure 7 (1 / 2 : ℝ) (by norm_num) (by norm_num)).real
      {e : Fin 7 → ZMod 2 | 2 ≤ hammingNorm e} = 15 / 16 := by
  rw [bsc_real_weight_ge_eq_binomTail]
  norm_num [ProbabilityTheory.binomTail, Finset.sum_Icc_succ_top, Nat.choose]

/-- Hamming weights of concrete words. -/
example : hammingNorm ![1, 0, 1] = 2 := by decide
example : hammingNorm ![0, 0, 0] = 0 := by decide

/-- The length-1 identity code corrects the zero error, so the
headline bound applies to it with `t = 0`. -/
example (m : Fin 1 → ZMod 2) (delta : ℝ) (h0 : 0 ≤ delta) (h1 : delta ≤ 1) :
    (bscMeasure 1 delta h0 h1).real
        {e : Fin 1 → ZMod 2 | (fun w => w) ((fun w => w) m + e) ≠ (fun w => w) m}
      ≤ ProbabilityTheory.binomTail 1 1 delta :=
  boundedDistance_bsc_error_le_binomTail 1 1 0 (fun w => w) (fun w => w)
    (by
      intro msg e he
      have hz : e = 0 := by
        funext i
        by_contra h
        have hpos : 0 < hammingNorm e := by
          rw [hammingNorm, Finset.card_pos]
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
        omega
      simp [hz])
    m delta h0 h1

/-- The concrete Hamming (7,4) code of `Cslib.CodingTheory.Hamming74`
over the BSC at crossover `1/10`, through the public corollary. -/
example (m : Fin 4 → ZMod 2) :
    (bscMeasure 7 (1 / 10 : ℝ) (by norm_num) (by norm_num)).real
        {e : Fin 7 → ZMod 2 | Cslib.CodingTheory.Hamming74.decode
          (Cslib.CodingTheory.Hamming74.encode m + e)
          ≠ Cslib.CodingTheory.Hamming74.encode m}
      ≤ ProbabilityTheory.binomTail 7 2 (1 / 10 : ℝ) :=
  hamming74_bsc_error_le m (1 / 10 : ℝ) (by norm_num) (by norm_num)

end Cslib.CodingTheory.BoundedDistanceBSCTests
