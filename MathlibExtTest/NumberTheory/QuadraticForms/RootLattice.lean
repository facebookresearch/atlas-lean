/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.RootLattice

/-!
# Tests for roots of binary quadratic forms and their lattices

The form $x^2 + y^2$, with root $i$: the endomorphism ring of $\mathbb{Z} + \mathbb{Z}i$ is
$\mathbb{Z} + \mathbb{Z}i$ of discriminant $-4$, the form is Gauss reduced and $i$ lies in both
fundamental domains, and $S$ fixes the form. The lattices of $\tau$ and $\tau + 1$ are homothetic.
-/

namespace BinaryQuadraticForm.RootLatticeTest

open UpperHalfPlane ModularGroup

open scoped MatrixGroups

theorem root_I : ((1 : ℤ) : ℂ) * (I : ℂ) ^ 2 + ((0 : ℤ) : ℂ) * (I : ℂ) + ((1 : ℤ) : ℂ) = 0 := by
  simp

theorem gcd_one_zero_one : Int.gcd (Int.gcd 1 0 : ℤ) 1 = 1 := by decide

theorem discrim_one_zero_one : discrim (1 : ℤ) 0 1 = -4 := by norm_num [discrim]

-- The endomorphism ring of `ℤ + ℤi` is `ℤ + ℤi`, an order of discriminant `-4`.
example :
    ((PeriodPair.ofTau (I : ℂ) (im_ne_zero_of_root (by norm_num [discrim]) root_I)).endomorphismRing :
        Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((1 : ℤ) * (I : ℂ))} :=
  (endomorphismRing_ofTau gcd_one_zero_one (by norm_num [discrim]) root_I).1

example : (((1 : ℤ) : ℂ) * (I : ℂ) - (starRingEnd ℂ) (((1 : ℤ) : ℂ) * (I : ℂ))) ^ 2 = -4 := by
  have h := (endomorphismRing_ofTau gcd_one_zero_one (by norm_num [discrim]) root_I).2.2
  rw [h, discrim_one_zero_one]
  norm_num

-- `x² + y²` is Gauss reduced, so `i` lies in the half-open fundamental domain.
example : (I : ℍ).re ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2) ∧ 1 ≤ ‖((I : ℍ) : ℂ)‖ ∧
    (0 < (I : ℍ).re → 1 < ‖((I : ℍ) : ℂ)‖) :=
  (isGaussReduced_iff_root_mem (by norm_num) (by norm_num [discrim]) root_I).mp
    ⟨by norm_num, by norm_num [discrim], by norm_num, le_rfl, fun _ ↦ le_rfl⟩

-- `x² - xy + y²` is not Gauss reduced: its root `(1 + i√3)/2` has real part `1/2`.
example : ¬ IsGaussReduced 1 (-1) 1 := fun h ↦ by
  have := h.boundary (Or.inr rfl)
  norm_num at this

-- `i` lies in Mathlib's closed fundamental domain.
example : (I : ℍ) ∈ fd :=
  (root_mem_fd_iff (by norm_num) root_I).mpr ⟨by norm_num, le_rfl⟩

-- The substitution `S = [[0, -1], [1, 0]]` fixes `x² + y²`.
example : substitute (1, 0, 1) S = (1, 0, 1) := by
  simp [substitute, coe_S]

example : ProperlyEquivalent (1, 0, 1) (1, 0, 1) := ⟨S, by simp [substitute, coe_S]⟩

-- The lattices of `τ` and `τ + 1 = T τ` are homothetic.
example (τ : ℍ) :
    (PeriodPair.ofTau τ τ.im_pos.ne').IsHomothetic
      (PeriodPair.ofTau ((T • τ : ℍ) : ℂ) (T • τ).im_pos.ne') :=
  (PeriodPair.isHomothetic_ofTau_iff τ (T • τ)).mpr ⟨T, rfl⟩

-- The orbit criterion, applied to `x² + y²` and the identity matrix.
example : ProperlyEquivalent (1, 0, 1) (1, 0, 1) :=
  (properlyEquivalent_iff_exists_smul gcd_one_zero_one gcd_one_zero_one (by norm_num)
    (by norm_num) (by norm_num [discrim]) root_I root_I).mpr ⟨1, (one_smul _ _).symm⟩

end BinaryQuadraticForm.RootLatticeTest
