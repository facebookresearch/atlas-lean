/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt
import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

open MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt
open scoped lp ENNReal

namespace MathlibExtTest.Analysis.InnerProductSpace.HilbertSchmidtCanonicalTests

-- Each finite identity block has squared entry sum N, including N=0.
example (N : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ‖hsDiagonal (fun _ : ℕ => (1 : ℝ)) i j‖ ^ 2) = (N : ℝ) := by
  have hf : (Finset.range N).filter (fun x => x < N) = Finset.range N :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_range.mp hx)
  simp [hsDiagonal, hf]

-- The infinite identity cannot supply a witness for the finite real norm.
example : ¬ IsHilbertSchmidt (hsDiagonal (fun _ : ℕ => (1 : ℝ))) := by
  intro ha
  have hd : Summable ((fun p : ℕ × ℕ => ‖hsDiagonal (fun _ : ℕ => (1 : ℝ)) p.1 p.2‖ ^ 2)
      ∘ fun n : ℕ => (n, n)) :=
    ha.comp_injective (fun i j h => congrArg Prod.fst h)
  have h1 : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [hsDiagonal, Function.comp_def] using hd
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp h1)

-- The actual bounded identity in the standard ℓ² basis has extended value top.
example : MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq
    (ContinuousLinearMap.id ℝ ℓ²(ℕ, ℝ)) (fun j => lp.single 2 j (1 : ℝ)) = ⊤ := by
  simp only [MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq,
    ContinuousLinearMap.id_apply, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    norm_one, one_pow, ENNReal.ofReal_one]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

example : hsMatrix (ContinuousLinearMap.id ℝ ℓ²(ℕ, ℝ)) =
    hsDiagonal (fun _ : ℕ => (1 : ℝ)) := by
  funext i j
  simp [hsMatrix, hsDiagonal, lp.single_apply, Pi.single_apply]

-- Use the standard Mathlib single-coordinate vectors, with no new basis object.
example : Orthonormal ℝ (fun j : ℕ => lp.single 2 j (1 : ℝ)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply]

private def d : ℕ → ℝ := fun n => if n = 0 then 2 else if n = 1 then 3 else 0

private theorem d_summable : Summable fun n => ‖d n‖ ^ 2 := by
  apply summable_of_ne_finset_zero (s := Finset.range 2)
  intro n hn
  have hn0 : n ≠ 0 := by simp only [Finset.mem_range] at hn; omega
  have hn1 : n ≠ 1 := by simp only [Finset.mem_range] at hn; omega
  simp [d, hn0, hn1]

private noncomputable abbrev u : ℓ²(ℕ, ℝ) := lp.single 2 0 (2 : ℝ)
private noncomputable abbrev v : ℓ²(ℕ, ℝ) := lp.single 2 1 (3 : ℝ)

example : IsHilbertSchmidt (hsDiagonal d) := isHilbertSchmidt_hsDiagonal d_summable
example : IsHilbertSchmidt (hsRankOne u v) := isHilbertSchmidt_hsRankOne

-- The real norm requires its finite-domain witness explicitly.
example {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → ℕ → 𝕜) (ha : IsHilbertSchmidt a) :
    hsNormSq a ha = ∑' p : ℕ × ℕ, ‖a p.1 p.2‖ ^ 2 := rfl

example (T : ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ)) (hT : IsHilbertSchmidt (hsMatrix T)) :
    MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq T
      (fun j => lp.single 2 j (1 : ℝ)) = ENNReal.ofReal (hsNormSq (hsMatrix T) hT) :=
  canonical_hsNormSq_eq_ofReal_matrix T hT

example (a : ℕ → ℕ → ℝ) (ha : IsHilbertSchmidt a) :
    MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq (hsOperator a ha)
      (fun j => lp.single 2 j (1 : ℝ)) = ENNReal.ofReal (hsNormSq a ha) :=
  canonical_hsNormSq_hsOperator a ha

example : MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq
    (hsOperator (0 : ℕ → ℕ → ℝ) isHilbertSchmidt_zero)
    (fun j => lp.single 2 j (1 : ℝ)) = 0 := by
  rw [canonical_hsNormSq_hsOperator]
  simp [hsNormSq]

-- A genuine two-entry diagonal has canonical squared norm 2²+3²=13.
example : MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq
    (hsOperator (hsDiagonal d) (isHilbertSchmidt_hsDiagonal d_summable))
    (fun j => lp.single 2 j (1 : ℝ)) = 13 := by
  rw [canonical_hsNormSq_hsOperator, hsNormSq_hsDiagonal d_summable]
  have hz : ∀ n ∉ Finset.range 2, ‖d n‖ ^ 2 = 0 := by
    intro n hn
    have hn0 : n ≠ 0 := by simp only [Finset.mem_range] at hn; omega
    have hn1 : n ≠ 1 := by simp only [Finset.mem_range] at hn; omega
    simp [d, hn0, hn1]
  rw [(hasSum_sum_of_ne_finset_zero hz).tsum_eq]
  norm_num [d, Finset.sum_range_succ]

-- A nonzero off-diagonal rank-one matrix has squared norm ‖u‖²‖v‖²=36.
example : MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq
    (hsOperator (hsRankOne u v) isHilbertSchmidt_hsRankOne)
    (fun j => lp.single 2 j (1 : ℝ)) = 36 := by
  rw [canonical_hsNormSq_hsOperator, hsNormSq_hsRankOne]
  norm_num [u, v, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

end MathlibExtTest.Analysis.InnerProductSpace.HilbertSchmidtCanonicalTests
