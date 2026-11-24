/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.AcyclicResolutionNormalizationSign

/-!
# The triangular comparison sign across original cup degrees
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory.ProjectiveResolution

/-- The recursively proved normalization exponent has the original cross-degree contribution p*q. -/
theorem acyclicResolutionNormalizationExponent_add (p q : ℕ) :
    acyclicResolutionNormalizationExponent (p + q) =
      acyclicResolutionNormalizationExponent p + acyclicResolutionNormalizationExponent q + p * q := by
  induction q with
  | zero => simp only [Nat.add_zero, acyclicResolutionNormalizationExponent, Nat.mul_zero]
  | succ q ih =>
      rw [show p + (q + 1) = (p + q) + 1 from by omega,
        acyclicResolutionNormalizationExponent, ih, acyclicResolutionNormalizationExponent]
      rw [Nat.mul_add, Nat.mul_one]
      omega

/--
The retained comparison sign contributes precisely the original (-1)^(p*q) factor across cup
degrees.
-/
theorem acyclicResolutionNormalizationSign_add (p q : ℕ) :
    acyclicResolutionNormalizationSign (p + q) =
      (-1 : ℤ) ^ (p * q) *
        acyclicResolutionNormalizationSign p * acyclicResolutionNormalizationSign q := by
  have hclosed : ∀ n, acyclicResolutionNormalizationSign n =
      (-1 : ℤ) ^ acyclicResolutionNormalizationExponent n := by
    intro n
    rw [acyclicResolutionNormalizationSign_closed, acyclicResolutionNormalizationExponent_eq]
  rw [hclosed, hclosed, hclosed, acyclicResolutionNormalizationExponent_add]
  simp only [pow_add]
  ac_rfl

end CategoryTheory.ProjectiveResolution
