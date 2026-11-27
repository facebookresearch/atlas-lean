/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.AcyclicResolutionNormalizationSign

/- Proof implementation note.
# The triangular comparison sign across original cup degrees
-/

/-!
# Triangular normalization across cup degrees

The exponent `a_n = n(n+1)/2` satisfies
`a_(p+q) = a_p + a_q + pq`. Consequently its integer sign
`σ_n = (-1)^a_n` contributes exactly `(-1)^(pq)` to a pairing
in degrees `p`, `q`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory.ProjectiveResolution

/- Proof implementation note.
The recursively proved normalization exponent has the original cross-degree contribution p*q.
-/

/-- For natural numbers `p`, `q`, the triangular normalization
exponents satisfy `a_(p+q) = a_p + a_q + pq`, where
`a_n` is the sum of the integers `1,…,n`. -/
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

/- Proof implementation note.
The retained comparison sign contributes precisely the original (-1)^(p*q) factor across cup
degrees.
-/

/-- For natural numbers `p`, `q`, the integer normalization
scalars satisfy `σ_(p+q) = (-1)^(pq) σ_p σ_q`,
where `σ_n = (-1)^(n(n+1)/2)`. -/
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
