/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/LinearAlgebra/Lidskii.lean` (leanprover/lean-eval), commit
38361be884302c7edce1908c4aef8296eb2cb27e, manifest `manifests/problems/lidskii_last.toml`
(revision 1, submitted by Kim Morrison, archived).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use the adapted
portion except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the
License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the License for the specific language governing permissions
and limitations under the License. lean-eval ships no `NOTICE` file.

The adapted portion is the statement of `lidskii_last`. ATLAS placed it in the
`MathlibExt.LinearAlgebra.LidskiiWanted.LinearAlgebra` namespace as a wanted declaration
and subsequently moved it here with a proof.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic.Module
import MathlibExt.Analysis.InnerProductSpace.CourantFischer

/-!
# Lidskii–Last eigenvalue perturbation theorem

`lidskii_last` bounds the total displacement of the ordered eigenvalues of two Hermitian
matrices by the sum of the norms of their entrywise differences.
-/

namespace MathlibExt.LinearAlgebra.LidskiiWanted.LinearAlgebra

open Matrix
open scoped ComplexOrder
open MathlibExt.Analysis.InnerProductSpace.CourantFischer

section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive semidefinite difference increases each ordered eigenvalue. -/
private theorem eigenvalues₀_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  obtain ⟨W, hW, htail, -⟩ := exists_tail_submodule (isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace k.isLt
  obtain ⟨x, hx, hx₁, hhead⟩ := exists_unit_ge_of_submodule
    (isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace k.isLt W hW
  refine hhead.trans (le_trans ?_ (htail x hx hx₁))
  have hpos := (isPositive_toEuclideanLin_iff.mpr h).re_inner_nonneg_left x
  simpa only [map_sub, LinearMap.sub_apply, inner_sub_left, sub_nonneg, rayleighForm]
    using hpos

/-- Each Gershgorin disk lies in the closed right half-plane after adding the absolute row sums
to the diagonal. Hence the shifted Hermitian matrix is positive semidefinite. -/
private theorem diagonal_add_posSemidef {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (diagonal (fun i => ((∑ j, ‖M i j‖ : ℝ) : ℂ)) + M).PosSemidef := by
  let D : Matrix n n ℂ := diagonal fun i => ((∑ j, ‖M i j‖ : ℝ) : ℂ)
  have hD : D.IsHermitian := isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  let h := hD.add hM
  apply h.posSemidef_iff_eigenvalues_nonneg.mpr
  intro k
  have heig : Module.End.HasEigenvalue (D + M).toLin' (h.eigenvalues k : ℂ) := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, spectrum_toLin']
    exact spectrum.algebraMap_mem ℂ (h.eigenvalues_mem_spectrum_real k)
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball heig
  have hbound := (Complex.re_le_norm _).trans (mem_closedBall_iff_norm'.mp hi)
  have hoff (j : n) (hj : j ∈ Finset.univ.erase i) : (D + M) i j = M i j := by
    simp [D, (Finset.ne_of_mem_erase hj).symm]
  rw [Finset.sum_congr rfl fun j hj => congrArg norm (hoff j hj)] at hbound
  simp only [D, Matrix.add_apply, diagonal_apply_eq, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re, Finset.sum_erase_eq_sub (Finset.mem_univ i)] at hbound
  change 0 ≤ h.eigenvalues k
  have hdiag := Complex.abs_re_le_norm (M i i)
  linarith [(abs_le.mp hdiag).1]

private theorem sum_eigenvalues₀ {M : Matrix n n ℂ} (h : M.IsHermitian) :
    ∑ j, h.eigenvalues₀ j = M.trace.re := by
  change _ = RCLike.re M.trace
  rw [h.trace_eq_sum_eigenvalues, map_sum]
  simp only [RCLike.ofReal_re]
  exact ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm.sum_comp h.eigenvalues₀).symm

end

set_option linter.dupNamespace false in
/-- **Lidskii–Last theorem.** Let $A$ and $B$ be Hermitian complex square matrices indexed by a
finite set with $N$ elements, and list the eigenvalues of $A$ and of $B$, each with multiplicity
and in decreasing order, as $\alpha_1 \ge \dots \ge \alpha_N$ and $\beta_1 \ge \dots \ge \beta_N$.
Then
$$\sum_{j=1}^N |\alpha_j - \beta_j| \le \sum_{i,j} |A_{ij} - B_{ij}|.$$

Source: V. B. Lidskii (1950); the entrywise ℓ¹ form is due to Y. Last (around 1993). Listed as §99
in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `lidskii_last`. -/
public theorem lidskii_last {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
      ∑ i, ∑ j, ‖A i j - B i j‖ := by
  let D : Matrix n n ℂ := diagonal fun i => ((∑ j, ‖A i j - B i j‖ : ℝ) : ℂ)
  -- This common upper bound satisfies `2 • C - A - B = D`.
  let C := (1 / 2 : ℝ) • (A + B + D)
  have hCA : (C - A).PosSemidef := by
    have heq : C - A = (1 / 2 : ℝ) • (D + (B - A)) := by dsimp [C]; module
    rw [heq]
    apply PosSemidef.smul _ (by norm_num)
    simpa only [D, Matrix.sub_apply, norm_sub_rev (B _ _) (A _ _)] using
      diagonal_add_posSemidef (hB.sub hA)
  have hCB : (C - B).PosSemidef := by
    have heq : C - B = (1 / 2 : ℝ) • (D + (A - B)) := by dsimp [C]; module
    rw [heq]
    exact (diagonal_add_posSemidef (hA.sub hB)).smul (by norm_num)
  have hC : C.IsHermitian := by simpa using hCA.isHermitian.add hA
  calc
    _ ≤ ∑ j, (2 * hC.eigenvalues₀ j - hA.eigenvalues₀ j - hB.eigenvalues₀ j) := by
      apply Finset.sum_le_sum
      intro j _
      have ha := eigenvalues₀_le hA hC hCA j
      have hb := eigenvalues₀_le hB hC hCB j
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sum_eigenvalues₀ hA, sum_eigenvalues₀ hB, sum_eigenvalues₀ hC]
      simp [C, D, trace_add, trace_smul, Complex.re_sum]
      ring

end MathlibExt.LinearAlgebra.LidskiiWanted.LinearAlgebra
