/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Coefficients in a subfield of the real numbers

A subfield `A` of `ℝ` embeds into `ℂ`; this is the coefficient embedding used
for real-coefficient perverse sheaves and Hodge structures. The embedding is
real, hence fixed by complex conjugation.
-/

@[expose] public noncomputable section

namespace MathlibExt.Algebra.RealSubfieldCoefficients

variable (A : Subfield ℝ)

/-- The embedding of a subfield of `ℝ` into `ℂ`. -/
def complexEmbedding : A →+* ℂ := Complex.ofRealHom.comp A.subtype

@[simp] theorem complexEmbedding_apply (a : A) : complexEmbedding A a = (a : ℝ) := rfl

@[simp] theorem complexEmbedding_star (a : A) : star (complexEmbedding A a) =
    complexEmbedding A a := by simp

/-- `ℂ` as an algebra over the coefficient subfield, through `complexEmbedding`. -/
abbrev complexAlgebra : Algebra A ℂ := (complexEmbedding A).toAlgebra

end MathlibExt.Algebra.RealSubfieldCoefficients
