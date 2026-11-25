/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.TestFunctionPartitionOfUnity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Analysis.Distribution.TestFunctionPartitionOfUnity` -/

namespace MathlibExtTest.Analysis.Distribution.TestFunctionPartitionOfUnity

open Set TopologicalSpace
open scoped Distributions ContDiff
open MathlibExt.Analysis.Distribution.TestFunctionPartitionOfUnityWanted

-- The test functions `𝓓(⊤, ℝ)` of the statement are `C^∞` (order `∞`, not the analytic order `ω`)
-- and compactly supported.
example (f : 𝓓((⊤ : Opens ℝ), ℝ)) : ContDiff ℝ ∞ f ∧ HasCompactSupport f :=
  ⟨f.contDiff, f.hasCompactSupport⟩

-- A cover by one open set gives a smooth cutoff: a nonnegative test function equal to `1` on `K`
-- with closed support in `U`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (U : Opens E) (hKU : K ⊆ U) :
    ∃ φ : 𝓓((⊤ : Opens E), ℝ), (∀ x, 0 ≤ φ x) ∧ tsupport φ ⊆ U ∧ ∀ x ∈ K, φ x = 1 := by
  obtain ⟨φ, h0, hsupp, hsum⟩ :=
    testFunction_partitionOfUnity (ι := Unit) hK (U := fun _ => U) fun x hx =>
      mem_iUnion.2 ⟨(), hKU hx⟩
  exact ⟨φ (), h0 (), hsupp (), fun x hx => by simpa using hsum x hx⟩

-- On `K`, every function of the partition takes values in `[0, 1]`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] {K : Set E} (hK : IsCompact K) {U : ι → Opens E}
    (hKU : K ⊆ ⋃ i, ↑(U i)) :
    ∃ φ : ι → 𝓓((⊤ : Opens E), ℝ), ∀ i, ∀ x ∈ K, φ i x ∈ Icc 0 1 := by
  obtain ⟨φ, h0, -, hsum⟩ := testFunction_partitionOfUnity hK hKU
  refine ⟨φ, fun i x hx => ⟨h0 i x, ?_⟩⟩
  rw [← hsum x hx]
  exact Finset.single_le_sum (fun j _ => h0 j x) (Finset.mem_univ i)

-- Cover `[0, 2]` by `(-∞, 1)` and `(0, ∞)`. The closed support of each function lies in its open
-- set, so each function vanishes at the boundary point of its set: the partition is `(0, 1)` at `1`
-- and `(1, 0)` at `0`.
example : ∃ φ : Fin 2 → 𝓓((⊤ : Opens ℝ), ℝ), (∀ i x, 0 ≤ φ i x) ∧
    φ 0 1 = 0 ∧ φ 1 1 = 1 ∧ φ 0 0 = 1 ∧ φ 1 0 = 0 := by
  obtain ⟨φ, h0, hsupp, hsum⟩ := testFunction_partitionOfUnity
    (isCompact_Icc (a := (0 : ℝ)) (b := 2)) (U := ![⟨Iio 1, isOpen_Iio⟩, ⟨Ioi 0, isOpen_Ioi⟩])
    fun x hx => by
      rcases lt_or_ge x 1 with h | h
      · exact mem_iUnion.2 ⟨0, by simpa using h⟩
      · exact mem_iUnion.2 ⟨1, by simp; linarith⟩
  have h01 : φ 0 1 = 0 := image_eq_zero_of_notMem_tsupport fun h => by
    have h' : (1 : ℝ) ∈ Iio 1 := hsupp 0 h
    exact lt_irrefl 1 h'
  have h10 : φ 1 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => by
    have h' : (0 : ℝ) ∈ Ioi 0 := hsupp 1 h
    exact lt_irrefl 0 h'
  have h1 := hsum 1 ⟨by norm_num, by norm_num⟩
  have h0' := hsum 0 ⟨le_rfl, by norm_num⟩
  rw [Fin.sum_univ_two] at h1 h0'
  exact ⟨φ, h0, h01, by linarith, by linarith, h10⟩

-- In the Euclidean plane: a smooth cutoff equal to `1` on the closed unit disc, with closed
-- support in the open disc of radius `2`.
example : ∃ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin 2))), ℝ), (∀ x, 0 ≤ φ x) ∧
    tsupport φ ⊆ Metric.ball 0 2 ∧ ∀ x ∈ Metric.closedBall 0 1, φ x = 1 := by
  obtain ⟨φ, h0, hsupp, hsum⟩ := testFunction_partitionOfUnity (ι := Unit)
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (U := fun _ => (⟨Metric.ball 0 2, Metric.isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin 2))))
    fun x hx => mem_iUnion.2 ⟨(), Metric.closedBall_subset_ball (by norm_num) hx⟩
  exact ⟨φ (), h0 (), hsupp (), fun x hx => by simpa using hsum x hx⟩

end MathlibExtTest.Analysis.Distribution.TestFunctionPartitionOfUnity
