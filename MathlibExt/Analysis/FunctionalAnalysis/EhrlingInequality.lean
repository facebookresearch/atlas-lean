/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_36.lean` (openbmb/ma-proofbench, revision 31bab4c):
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al.

This attribution applies to the theorem statement.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Ehrling's inequality

On the compact closure of the image of the unit ball, the ratio of the intermediate norm
to the final norm is bounded wherever the intermediate norm is at least a fixed positive
threshold. Rescaling gives the estimate for arbitrary vectors.
-/

public section

namespace MathlibExt.Analysis.FunctionalAnalysis.EhrlingInequalityWanted

open Metric Set

/-- **Ehrling's inequality.** Let $X$, $Y$, $Z$ be real Banach spaces, let $i \colon X \to Y$ be an
injective compact bounded linear operator, and let $j \colon Y \to Z$ be an injective bounded
linear operator. Then for every $\varepsilon > 0$ there is $C_\varepsilon > 0$ such that
$\|i(u)\|_Y \le \varepsilon \|u\|_X + C_\varepsilon \|j(i(u))\|_Z$ for all $u \in X$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_36.lean`
at openbmb/ma-proofbench@31bab4c.
-/
theorem ehrling_inequality
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (iXY : X →L[ℝ] Y) (iYZ : Y →L[ℝ] Z)
    (hXY_compact : IsCompactOperator (iXY : X → Y))
    (hXY_inj : Function.Injective iXY)
    (hYZ_inj : Function.Injective iYZ) :
    ∀ ε > 0, ∃ Cε > 0, ∀ u : X,
      ‖iXY u‖ ≤ ε * ‖u‖ + Cε * ‖iYZ (iXY u)‖ := by
  intro ε hε
  obtain ⟨K, hK, himage⟩ := hXY_compact.image_closedBall_subset_compact (f := iXY.toLinearMap) 1
  let S := K ∩ {y : Y | ε ≤ ‖y‖}
  have hS : IsCompact S := hK.inter_right (isClosed_le continuous_const continuous_norm)
  have hpos (y : Y) (hy : y ∈ S) : 0 < ‖iYZ y‖ :=
    norm_pos_iff.mpr <| (map_ne_zero_iff iYZ hYZ_inj).mpr (norm_pos_iff.mp (hε.trans_le hy.2))
  obtain ⟨M, hM⟩ := hS.bddAbove_image (f := fun y ↦ ‖y‖ / ‖iYZ y‖)
    (continuous_norm.continuousOn.div iYZ.continuous.norm.continuousOn fun y hy ↦ (hpos y hy).ne')
  let C := max M 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨C, hC, fun u ↦ ?_⟩
  by_cases hu : u = 0
  · simp [hu]
  by_cases hsmall : ‖iXY u‖ ≤ ε * ‖u‖
  · exact hsmall.trans (le_add_of_nonneg_right (mul_nonneg hC.le (norm_nonneg _)))
  -- Normalizing the input puts its image in the compact set on which the ratio is bounded.
  have hu_pos := norm_pos_iff.mpr hu
  let v := ‖u‖⁻¹ • u
  have hv : iXY v ∈ S := by
    refine ⟨himage ⟨v, inv_norm_smul_mem_unitClosedBall u, rfl⟩, ?_⟩
    change ε ≤ ‖iXY (‖u‖⁻¹ • u)‖
    rw [map_smul, norm_smul_of_nonneg (inv_nonneg.mpr hu_pos.le), le_inv_mul_iff₀ hu_pos,
      mul_comm]
    exact (lt_of_not_ge hsmall).le
  have hratio : ‖iXY v‖ / ‖iYZ (iXY v)‖ ≤ C :=
    (hM (mem_image_of_mem _ hv)).trans (le_max_left _ _)
  simp only [v, map_smul, norm_smul_of_nonneg (inv_nonneg.mpr hu_pos.le),
    mul_div_mul_left _ _ (inv_ne_zero hu_pos.ne')] at hratio
  have hne := (map_ne_zero_iff iYZ hYZ_inj).mpr ((map_ne_zero_iff iXY hXY_inj).mpr hu)
  exact ((div_le_iff₀ (norm_pos_iff.mpr hne)).mp hratio).trans
    (le_add_of_nonneg_left (mul_nonneg hε.le (norm_nonneg _)))

end MathlibExt.Analysis.FunctionalAnalysis.EhrlingInequalityWanted
