/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.FiveArrowSequence
public import Mathlib.Tactic.IntervalCases

/-!
# Exact five-arrow windows of δ-functors

Each pair of adjacent degrees gives an exact five-arrow window of the
associated long exact sequence.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- All five-arrow delta windows are exact from the genuine
exactLeft, exactMiddle, and exactRight coefficient conditions. -/
theorem fiveArrowSequence_exact (T : CohomologicalDeltaFunctor A B)
    (S : ShortComplex.ShortExactSequences A) (n : ℕ) : (fiveArrowSequence T S n).Exact := by
  obtain ⟨w₀,h₀⟩ := T.exactMiddle n S
  obtain ⟨w₁,h₁⟩ := T.exactRight n S
  obtain ⟨w₂,h₂⟩ := T.exactLeft n S
  obtain ⟨w₃,h₃⟩ := T.exactMiddle (n + 1) S
  refine { zero := ?_, exact := ?_ }
  · intro i hi
    have hle : i ≤ 3 := by omega
    interval_cases i
    · exact w₀
    · exact w₁
    · exact w₂
    · exact w₃
  · intro i hi
    have hle : i ≤ 3 := by omega
    interval_cases i
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃

end CategoryTheory.CohomologicalDeltaFunctor
