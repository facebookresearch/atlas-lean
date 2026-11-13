/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddWallis
import Mathlib.Analysis.Real.Pi.Wallis





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddZeroPrefactorNormalized
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexZeroPhaseBethePrefactor c
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
      (sixVertexOddCentralIndex (s + k + 1)) /
    (sixVertexFourWidth (2 * s + 1) k : Real)

theorem tendsto_sixVertexCanonicalOddZeroPrefactorNormalized
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalOddZeroPrefactorNormalized hc s) atTop
      (nhds (c ^ 2 * (2 * Real.pi) *
        sixVertexFourierPhysicalDensity c hc 0)) := by
  have hdensity := tendsto_sixVertexCanonicalOddFiniteDensity_zero hc s
  have hmul := hdensity.const_mul (c ^ 2 * (2 * Real.pi))
  apply hmul.congr'
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  symm
  unfold sixVertexCanonicalOddZeroPrefactorNormalized
  rw [sixVertexCanonicalOddZeroPrefactor_eq_finiteDensity hc s k hk]
  have hN : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  field_simp [hN]

theorem sixVertexCanonicalOddZeroPrefactorNormalized_limit_pos
    {c : Real} (hc : 2 < c) :
    0 < c ^ 2 * (2 * Real.pi) *
      sixVertexFourierPhysicalDensity c hc 0 := by
  exact mul_pos (mul_pos (sq_pos_of_pos (by linarith))
    (mul_pos (by norm_num) Real.pi_pos))
    (sixVertexFourierPhysicalDensity_pos hc 0)

theorem tendsto_log_sixVertexCanonicalOddZeroPrefactorNormalized
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => Real.log
      (sixVertexCanonicalOddZeroPrefactorNormalized hc s k)) atTop
      (nhds (Real.log (c ^ 2 * (2 * Real.pi) *
        sixVertexFourierPhysicalDensity c hc 0))) := by
  exact (Real.continuousAt_log
    (sixVertexCanonicalOddZeroPrefactorNormalized_limit_pos hc).ne').tendsto.comp
      (tendsto_sixVertexCanonicalOddZeroPrefactorNormalized hc s)

def sixVertexIdealWallisLogCorrection (n : Nat) : Real :=
  -Real.log (Real.Wallis.W n)

theorem tendsto_sixVertexIdealWallisLogCorrection :
    Tendsto sixVertexIdealWallisLogCorrection atTop
      (nhds (-Real.log (Real.pi / 2))) := by
  unfold sixVertexIdealWallisLogCorrection
  exact ((Real.continuousAt_log (ne_of_gt Real.pi_div_two_pos)).tendsto.comp
    Real.Wallis.tendsto_W_nhds_pi_div_two).neg

theorem sixVertexIdealWallisLogCorrection_eq_sum (n : Nat) :
    sixVertexIdealWallisLogCorrection n =
      ∑ j ∈ Finset.range n,
        Real.log (((2 * (j : Real) + 1) * (2 * j + 3)) /
          (2 * j + 2) ^ 2) := by
  have hodd1 (j : Nat) : (2 * (j : Real) + 1) ≠ 0 := by positivity
  have hodd3 (j : Nat) : (2 * (j : Real) + 3) ≠ 0 := by positivity
  have heven (j : Nat) : (2 * (j : Real) + 2) ≠ 0 := by positivity
  have hfactor (j : Nat) :
      Real.log (((2 * (j : Real) + 1) * (2 * j + 3)) /
          (2 * j + 2) ^ 2) =
        -Real.log (((2 * (j : Real) + 2) / (2 * j + 1)) *
          ((2 * j + 2) / (2 * j + 3))) := by
    rw [Real.log_div (mul_ne_zero (hodd1 j) (hodd3 j))
      (pow_ne_zero 2 (heven j)), Real.log_mul (hodd1 j) (hodd3 j),
      Real.log_pow, Real.log_mul
        (div_ne_zero (heven j) (hodd1 j))
        (div_ne_zero (heven j) (hodd3 j)),
      Real.log_div (heven j) (hodd1 j),
      Real.log_div (heven j) (hodd3 j)]
    ring
  unfold sixVertexIdealWallisLogCorrection Real.Wallis.W
  rw [Real.log_prod (fun j hj => mul_ne_zero
    (div_ne_zero (heven j) (hodd1 j))
    (div_ne_zero (heven j) (hodd3 j)))]
  simp_rw [hfactor]
  rw [Finset.sum_neg_distrib]



theorem two_sum_midpoint_sub_eq_endpoint_add_secondDifference
    (n : Nat) (x : Nat -> Real) (f : Real -> Real) :
    2 * ∑ j ∈ Finset.range n,
        (f ((x j + x (j + 1)) / 2) - f (x j)) =
      f (x n) - f (x 0) +
        ∑ j ∈ Finset.range n,
          (2 * f ((x j + x (j + 1)) / 2) - f (x j) - f (x (j + 1))) := by
  rw [show f (x n) - f (x 0) =
    ∑ j ∈ Finset.range n, (f (x (j + 1)) - f (x j)) by
      rw [Finset.sum_sub_distrib]
      have h := Finset.sum_range_sub' (fun j => f (x j)) n
      rw [Finset.sum_sub_distrib] at h
      linarith]
  rw [<- Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end

end StatMech.FrontierD
