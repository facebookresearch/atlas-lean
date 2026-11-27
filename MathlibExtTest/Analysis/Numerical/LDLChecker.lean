/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.LDLChecker
public meta import MathlibExt.Analysis.Numerical.LDLChecker
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Tactic.NormNum

/-
Tests for exact rational LDLᵀ certificates (`SOSCertificate.LDL`).

A concrete 2×2 acceptance case with `PosSemidef` derived through the verified
checker (and directly through the main soundness theorem), rejection cases (a
negative diagonal entry; a forged certificate for the non-PSD matrix
`diagonal ![1, -1]`), a direct proof that `diagonal ![1, -1]` is not positive
semidefinite as a sanity anchor, and axiom probes. See Horn and Johnson,
"Matrix Analysis" (Cambridge University Press), Chapter 7, for the background
on positive semidefinite matrices.
-/

namespace SOSCertificate.LDL

/-- The 2×2 factorization equation `Q = L * diagonal d * Lᵀ` for
`Q = !![3, 6; 6, 17]`, `L = !![1, 0; 2, 1]`, `d = ![3, 5]`, shared by the
acceptance test and the direct soundness test. -/
theorem factor_2x2 : (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ)
    = (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ)
      * Matrix.diagonal (![3, 5] : Fin 2 → ℚ)
      * (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ).transpose := by
  have q00 : (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = 3 := by decide
  have q01 : (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 6 := by decide
  have q10 : (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 6 := by decide
  have q11 : (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 17 := by decide
  have l00 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = 1 := by decide
  have l01 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 0 := by decide
  have l10 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 2 := by decide
  have l11 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1 := by decide
  have d00 : (Matrix.diagonal (![3, 5] : Fin 2 → ℚ)) 0 0 = 3 := by decide
  have d01 : (Matrix.diagonal (![3, 5] : Fin 2 → ℚ)) 0 1 = 0 := by decide
  have d10 : (Matrix.diagonal (![3, 5] : Fin 2 → ℚ)) 1 0 = 0 := by decide
  have d11 : (Matrix.diagonal (![3, 5] : Fin 2 → ℚ)) 1 1 = 5 := by decide
  have t00 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ).transpose 0 0 = 1 := by
    decide
  have t01 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ).transpose 0 1 = 2 := by
    decide
  have t10 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ).transpose 1 0 = 0 := by
    decide
  have t11 : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ).transpose 1 1 = 1 := by
    decide
  apply Matrix.ext
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, q00, q01, q10, q11,
      l00, l01, l10, l11, d00, d01, d10, d11, t00, t01, t10, t11] <;>
    norm_num

/-- Acceptance: `Q = !![3, 6; 6, 17]` factors as `L * diagonal d * Lᵀ` with
`L = !![1, 0; 2, 1]` unit lower-triangular and `d = ![3, 5]` nonnegative. -/
theorem accept_2x2 : checkLDL (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ)
    (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) (![3, 5] : Fin 2 → ℚ) = true := by
  have eTri : decide ((!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ).IsLowerTriangular ∧
      ∀ i : Fin 2, (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) i i = 1) = true := by
    decide
  have e3 : decide (∀ i : Fin 2, (0 : ℚ) ≤ (![3, 5] : Fin 2 → ℚ) i) = true := by
    decide
  have hEntry : ∀ i j : Fin 2,
      (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ∑ k, (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) i k *
        (![3, 5] : Fin 2 → ℚ) k *
        (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) j k := by
    intro i j
    have hQij := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℚ => M i j) factor_2x2
    rw [hQij]
    exact ldl_entry _ _ i j
  have eEntry : decide (∀ i j : Fin 2,
      (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ∑ k, (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) i k *
        (![3, 5] : Fin 2 → ℚ) k *
        (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) j k) = true := by
    cases h : decide (∀ i j : Fin 2,
      (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ∑ k, (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) i k *
        (![3, 5] : Fin 2 → ℚ) k *
        (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) j k) with
    | true => rfl
    | false => exact absurd hEntry (of_decide_eq_false h)
  have hEq : checkLDL (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ)
      (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) (![3, 5] : Fin 2 → ℚ)
      = (true && (true && true)) := by
    simp only [checkLDL, eTri, e3, eEntry]
  exact hEq.trans (by decide)

/-- `PosSemidef` for the acceptance case, through the verified checker. -/
theorem psd_2x2 : (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef :=
  checkLDL_sound accept_2x2

/-- The same matrix is positive semidefinite through the main soundness
theorem directly. -/
theorem psd_2x2_via_main :
    (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ).PosSemidef := by
  have hLower : (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ).IsLowerTriangular := by
    decide
  have hDiag : ∀ i : Fin 2,
      (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) i i = 1 := by decide
  have hL : IsUnitLowerTriangular (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) :=
    ⟨hLower, hDiag⟩
  have hd : ∀ i : Fin 2, (0 : ℚ) ≤ (![3, 5] : Fin 2 → ℚ) i := by decide
  exact ldl_posSemidef _ _ hL hd _ factor_2x2

/-- Rejection: the same `Q` and `L` but with a negative entry in `d`. -/
theorem reject_neg_d : checkLDL (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ)
    (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℚ) (![3, -5] : Fin 2 → ℚ)
    = false := by
  decide

/-- Rejection: a forged certificate (`L = 1`, `d = ![1, 1]`) for the non-PSD
matrix `diagonal ![1, -1]`; triangularity and nonnegativity pass but the
factorization equation fails. -/
theorem reject_nonpsd : checkLDL (Matrix.diagonal (![1, -1] : Fin 2 → ℚ))
    (1 : Matrix (Fin 2) (Fin 2) ℚ) (![1, 1] : Fin 2 → ℚ) = false := by
  have hne : ¬ (∀ i j : Fin 2, (Matrix.diagonal (![1, -1] : Fin 2 → ℚ)) i j =
      ∑ k, (1 : Matrix (Fin 2) (Fin 2) ℚ) i k * (![1, 1] : Fin 2 → ℚ) k *
        (1 : Matrix (Fin 2) (Fin 2) ℚ) j k) := by
    intro hcon
    have h11 := hcon 1 1
    have b11 : (Matrix.diagonal (![1, -1] : Fin 2 → ℚ)) 1 1 = -1 := by decide
    have o10 : (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by decide
    have o11 : (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1 := by decide
    have d0 : ((![1, 1] : Fin 2 → ℚ) 0) = 1 := by decide
    have d1 : ((![1, 1] : Fin 2 → ℚ) 1) = 1 := by decide
    simp only [Fin.sum_univ_two, b11, o10, o11, d0, d1] at h11
    norm_num at h11
  have eTri : decide ((1 : Matrix (Fin 2) (Fin 2) ℚ).IsLowerTriangular ∧
      ∀ i : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℚ) i i = 1) = true := by decide
  have e3 : decide (∀ i : Fin 2, (0 : ℚ) ≤ (![1, 1] : Fin 2 → ℚ) i) = true := by
    decide
  have eEntry : decide (∀ i j : Fin 2,
      (Matrix.diagonal (![1, -1] : Fin 2 → ℚ)) i j =
      ∑ k, (1 : Matrix (Fin 2) (Fin 2) ℚ) i k * (![1, 1] : Fin 2 → ℚ) k *
        (1 : Matrix (Fin 2) (Fin 2) ℚ) j k) = false := by
    cases h : decide (∀ i j : Fin 2,
      (Matrix.diagonal (![1, -1] : Fin 2 → ℚ)) i j =
      ∑ k, (1 : Matrix (Fin 2) (Fin 2) ℚ) i k * (![1, 1] : Fin 2 → ℚ) k *
        (1 : Matrix (Fin 2) (Fin 2) ℚ) j k) with
    | true => exact absurd (of_decide_eq_true h) hne
    | false => rfl
  have hEq : checkLDL (Matrix.diagonal (![1, -1] : Fin 2 → ℚ))
      (1 : Matrix (Fin 2) (Fin 2) ℚ) (![1, 1] : Fin 2 → ℚ)
      = (true && (true && false)) := by
    simp only [checkLDL, eTri, e3, eEntry]
  exact hEq.trans (by decide)

/-- Sanity anchor: `diagonal ![1, -1]` is not positive semidefinite. -/
theorem not_psd_diag : ¬ (Matrix.diagonal (![1, -1] : Fin 2 → ℚ)).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  intro h
  have h1 := h 1
  have e : ((![1, -1] : Fin 2 → ℚ) 1) = -1 := by decide
  rw [e] at h1
  exact absurd h1 (by decide)

/-- Acceptance case evaluated directly in the kernel: the 2x2 LDL certificate. -/
example : checkLDL (!![3, 6; 6, 17] : Matrix (Fin 2) (Fin 2) ℚ)
    !![1, 0; 2, 1] ![3, 5] = true := by decide +kernel

/-- Rejection case evaluated directly in the kernel: negative diagonal entry. -/
example : checkLDL (Matrix.diagonal (![1, -1] : Fin 2 → ℚ))
    (1 : Matrix (Fin 2) (Fin 2) ℚ) ![1, -1] = false := by decide +kernel
#print axioms factor_2x2
#print axioms accept_2x2
#print axioms psd_2x2
#print axioms psd_2x2_via_main
#print axioms reject_neg_d
#print axioms reject_nonpsd
#print axioms not_psd_diag
#print axioms checkLDL_sound
#print axioms ldl_posSemidef

end SOSCertificate.LDL
