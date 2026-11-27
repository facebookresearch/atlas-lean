/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`openai/math` at revision `3344da59991ed94f9ba711217b29c1d760badfa6`.

* `lean/ComparatorChallenges/DirectCrouzeix.lean`: the statement of `uniform_sharpness`
  and the definitions inlined in its hypothesis.
* `lean/OAI/Analysis/DirectCrouzeix/Sharpness.lean`: the matrix-entry estimate,
  two-dimensional shift witness, and sharpness proof.

Licensed under the Apache License, Version 2.0; see `lean/LICENSE` at that revision.
Authors: OpenAI (project attribution in lean/formalization.yaml).
The cited files and accompanying notices name no copyright holder or individual authors.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorff

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix.Norms.L2Operator Kronecker
open MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted

namespace Matrix

private def twoStepShift : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

private theorem norm_ge_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (i j : ι) : ‖M i j‖ ≤ ‖M‖ := by
  let v := EuclideanSpace.single j (1 : ℂ)
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M
  have hTv : (T v) i = M i j := by
    change (M *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    rfl
  rw [← hTv]
  calc
    ‖(T v) i‖ ≤ ‖T v‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖v‖ := T.le_opNorm _
    _ = ‖M‖ := by simp [v, T, Matrix.l2_opNorm_toEuclideanCLM]

private theorem norm_le_one_of_mem_shift_range {z : ℂ}
    (hz : z ∈ numericalRange (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
      twoStepShift)) : ‖z‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  have hs : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    simpa [hx, Fin.sum_univ_two] using (EuclideanSpace.norm_sq_eq x).symm
  have hv : inner ℂ (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) twoStepShift x) x =
      (2 : ℂ) * star (x 1) * x 0 := by
    simp [twoStepShift, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM,
      dotProduct, Fin.sum_univ_two, map_ofNat, mul_comm, mul_left_comm]
  rw [hv]
  simp only [norm_mul, norm_star]
  norm_num
  nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖)]


/-- **No uniform complete numerical-range bound has constant below two.** Suppose $c$ is real
and for every pair of positive matrix sizes $n,m$, degree $d\ge 0$, complex matrix $A$ of size
$n$, and complex matrix coefficients $B_0,\ldots,B_d$ of size $m$, the Euclidean operator norm
of $\sum_{k=0}^d A^k\otimes B_k$ is at most $c$ times the supremum of the Euclidean operator
norm of $\sum_{k=0}^d z^k B_k$ on the numerical range of $A$. The numerical range here uses
$\langle x,Ax\rangle$ for unit vectors $x$, with the inner product linear in its second
argument. Then $2\le c$. The bound from below is independent of the upper-bound theorem.

Source: OpenAI, *A direct proof of the complete Crouzeix inequality*, [sharpness
statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DirectCrouzeix.lean#L27-L39). -/
theorem two_le_of_uniform_complete_numericalRange_bound (c : ℝ)
    (hc : ∀ (n m d : ℕ), 0 < n → 0 < m →
      ∀ (A : Matrix (Fin n) (Fin n) ℂ) (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ),
        ‖∑ k : Fin (d + 1), (A ^ (k : ℕ)) ⊗ₖ B k‖ ≤ c * sSup
          ((fun z : ℂ => ‖∑ k : Fin (d + 1), (z ^ (k : ℕ)) • B k‖) ''
            (star '' MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted.numericalRange
              (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) A)))) :
    2 ≤ c := by
  let B : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := ![0, 1]
  let E := star '' numericalRange (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) twoStepShift)
  have h := hc 2 1 1 (by decide) (by decide) twoStepShift B
  change ‖∑ k : Fin 2, (twoStepShift ^ (k : ℕ)) ⊗ₖ B k‖ ≤ c * sSup
    ((fun z : ℂ => ‖∑ k : Fin 2, (z ^ (k : ℕ)) • B k‖) '' E) at h
  have hleft : (∑ k : Fin 2, (twoStepShift ^ (k : ℕ)) ⊗ₖ B k) =
      twoStepShift ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    simp [B, Fin.sum_univ_two]
  have hright (z : ℂ) : ‖∑ k : Fin 2, (z ^ (k : ℕ)) • B k‖ = ‖z‖ := by
    simp [B, Fin.sum_univ_two, norm_smul]
  simp_rw [hleft, hright] at h
  have hge : 2 ≤ ‖twoStepShift ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ := by
    simpa [twoStepShift, Matrix.kroneckerMap_apply] using
      (norm_ge_entry (twoStepShift ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (0, 0) (1, 0))
  have hE : E.Nonempty := by
    let x := EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
    have hx : ‖x‖ = 1 := by simp [x]
    exact Set.Nonempty.image _ ⟨_, inner_mem_numericalRange _ hx⟩
  have hle : sSup ((fun z : ℂ => ‖z‖) '' E) ≤ 1 := by
    apply csSup_le (hE.image _)
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [norm_star] using norm_le_one_of_mem_shift_range hz
  have hnonneg : 0 ≤ sSup ((fun z : ℂ => ‖z‖) '' E) := by
    obtain ⟨z, hz⟩ := hE
    have hbd : BddAbove ((fun z : ℂ => ‖z‖) '' E) := by
      use 1
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [norm_star] using norm_le_one_of_mem_shift_range hw
    exact (norm_nonneg z).trans (le_csSup hbd ⟨z, hz, rfl⟩)
  have hc₀ : 0 ≤ c := by
    by_contra! hn
    have hbad := mul_nonpos_of_nonpos_of_nonneg hn.le hnonneg
    linarith
  exact hge.trans (h.trans (by simpa using mul_le_mul_of_nonneg_left hle hc₀))

end Matrix
