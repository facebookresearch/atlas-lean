/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Finite structure factors

The finite structure factor with the negative-exponent kernel.

## i. Overview

The finite structure factor sums amplitudes with Mathlib's standard additive character and the
same negative-exponent kernel as `ZMod.dft` (`ZMod.dft_apply`), `exp (-2πi j k / N)`. The
positive-exponent character is not used; the sign is the convention this module fixes.

Only the finite periodic case is treated: no continuous Fourier transform is claimed. Reciprocal
bases are not formalized here; they belong to the diffraction modules.

Provenance: atlas roadmap R09 and R11; task MF15, target MF15.3.

## ii. Key results

- `PhyslibExt.CondensedMatter.Crystallography.StructureFactor.structureFactor` :
  finite structure factor with the negative-exponent kernel.
- `PhyslibExt.CondensedMatter.Crystallography.StructureFactor.structureFactor_eq_sum_amp_of_zero`
  : at zero wavevector the structure factor is the sum of amplitudes.
- `PhyslibExt.CondensedMatter.Crystallography.StructureFactor.structureFactor_twoSite_cancel` :
  two equal amplitudes at `0` and `1` of `ZMod 2` cancel at `k = 1`.

## iii. Table of contents

- A. Finite structure factor
- B. Two-site cancellation

## iv. References

* C. Kittel, *Introduction to Solid State Physics*, 8th ed., Wiley (2005), Chapter 2,
  "Structure factor of the basis", which uses the negative-exponent kernel
  `S_G = Σ_j f_j exp(-i G·r_j)` matching `structureFactor`.
* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Holt, Rinehart and Winston (1976),
  Chapter 6, whose geometrical structure factor uses the opposite (positive) exponent sign.

-/

@[expose] public section

noncomputable section

namespace PhyslibExt.CondensedMatter.Crystallography.StructureFactor

/-! ## A. Finite structure factor -/

/-- Finite structure factor: amplitudes `amp i` at positions `pos i`, evaluated at
wavevector index `k`, with Mathlib's standard additive character and the same
negative-exponent kernel as `ZMod.dft`. -/
noncomputable def structureFactor {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (amp : ι → ℂ) (pos : ι → ZMod N) (k : ZMod N) : ℂ :=
  ∑ i, amp i * ZMod.stdAddChar (-(k * pos i))

/-- At zero wavevector the structure factor is the plain sum of amplitudes. -/
lemma structureFactor_eq_sum_amp_of_zero {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (amp : ι → ℂ) (pos : ι → ZMod N) :
    structureFactor amp pos 0 = ∑ i, amp i := by
  simp only [structureFactor, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]

/-! ## B. Two-site cancellation -/

/-- Two-site motif cancellation: two equal amplitudes at positions `0` and `1` of
`ZMod 2`, evaluated at `k = 1`, interfere destructively to `0`. -/
lemma structureFactor_twoSite_cancel (a : ℂ) :
    structureFactor (fun _ : Fin 2 => a) ![0, 1] (1 : ZMod 2) = 0 := by
  -- `simp` normalizes `-(1 : ZMod 2)` to `1`, so prove the value at `1`.
  have h1 : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
    have h := ZMod.stdAddChar_coe (N := 2) 1
    rw [Int.cast_one] at h
    rw [h, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  simp [structureFactor, Fin.sum_univ_two, h1]

end PhyslibExt.CondensedMatter.Crystallography.StructureFactor
