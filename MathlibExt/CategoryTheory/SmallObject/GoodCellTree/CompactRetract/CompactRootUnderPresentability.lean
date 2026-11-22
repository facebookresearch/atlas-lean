/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Presentable.IsDiscrete
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Actual fixed-rank compact-root under categories

A genuinely compact original root and coefficient LP at chi prove LP of
its under category at the same chi. The original forgetful functor
preserves chi-presentable objects, giving compact coefficient right ends.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.CompactRootUnderPresentability

open Limits

variable {C : Type u} [Category.{v} C] (D : C)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalPresentable D chi]

/-- The actual original one-object root functor preserves the same compactness rank. -/
theorem rootFunctorPresentable : (Functor.fromPUnit.{0} D).PreservesCardinalPresentable chi where
  le_inverseImage_isCardinalPresentable _ _ := by
    change IsCardinalPresentable D chi
    infer_instance

variable [IsCardinalLocallyPresentable C chi]

/-- The actual original under category is accessible at the unchanged original rank. -/
theorem cardinalAccessible : IsCardinalAccessibleCategory (Under D) chi := by
  let : (Functor.fromPUnit.{0} D).PreservesCardinalPresentable chi :=
    rootFunctorPresentable D chi
  exact inferInstanceAs
    (IsCardinalAccessibleCategory (Comma (Functor.fromPUnit.{0} D) (𝟭 C)) chi)

/-- Coefficient colimits and actual fixed-rank accessibility prove the under category LP. -/
theorem cardinalLocallyPresentable : IsCardinalLocallyPresentable (Under D) chi := by
  let : IsCardinalAccessibleCategory (Under D) chi := cardinalAccessible D chi
  exact { }

/-- The same original forgetful functor preserves the actual original compactness rank. -/
theorem forgetPresentable : (Under.forget D).PreservesCardinalPresentable chi := by
  let : (Functor.fromPUnit.{0} D).PreservesCardinalPresentable chi :=
    rootFunctorPresentable D chi
  exact inferInstanceAs
    ((Comma.snd (Functor.fromPUnit.{0} D) (𝟭 C)).PreservesCardinalPresentable chi)

/-- An actual compact under-root piece has its actual right end compact in the coefficient. -/
theorem rightPresentable (U : Under D) [IsCardinalPresentable U chi] :
    IsCardinalPresentable U.right chi := by
  let : (Under.forget D).PreservesCardinalPresentable chi := forgetPresentable D chi
  exact inferInstanceAs (IsCardinalPresentable ((Under.forget D).obj U) chi)

end CategoryTheory.SmallObject.CompactRootUnderPresentability
