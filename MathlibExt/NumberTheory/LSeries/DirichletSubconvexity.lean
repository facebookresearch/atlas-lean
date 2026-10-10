/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conductor-aspect Dirichlet subconvexity exponent
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import MathlibExt.NumberTheory.PowerFree

@[expose] public section

namespace MathlibExt.NumberTheory.DirichletSubconvexity

/-- Uniform conductor-aspect central-value exponent on a selected set of levels.
The constants may depend on `ε`, but not on the level or primitive character. -/
def IsCentralValueExponentOn (levels : Set ℕ) (θ : ℝ) : Prop :=
  0 ≤ θ ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ hq : 0 < q, q ∈ levels →
        letI : NeZero q := ⟨hq.ne'⟩
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
          ‖χ.LFunction (1 / 2 : ℂ)‖ ≤ C * Real.rpow (q : ℝ) (θ + ε)

/-- An exponent admissible for all primitive Dirichlet characters. -/
def IsDirichletSubconvexityExponent (θ : ℝ) : Prop :=
  IsCentralValueExponentOn Set.univ θ

/-- The pointwise conductor-aspect Dirichlet subconvexity exponent. -/
noncomputable def dirichletSubconvexityExponent : EReal :=
  sInf ((fun θ : ℝ => (θ : EReal)) '' {θ | IsDirichletSubconvexityExponent θ})

/-- The exponent is nonnegative by construction, including if the admitted set is empty. -/
theorem dirichletSubconvexityExponent_nonneg :
    (0 : EReal) ≤ dirichletSubconvexityExponent := by
  apply le_sInf
  rintro _ ⟨θ, hθ, rfl⟩
  exact EReal.coe_nonneg.mpr hθ.1

/-- Every admitted real exponent bounds the infimal exponent from above. -/
theorem dirichletSubconvexityExponent_le_of_admissible {θ : ℝ}
    (hθ : IsDirichletSubconvexityExponent θ) :
    dirichletSubconvexityExponent ≤ (θ : EReal) := by
  exact sInf_le ⟨θ, hθ, rfl⟩

end MathlibExt.NumberTheory.DirichletSubconvexity
