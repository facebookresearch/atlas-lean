/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidNormalAdmissibleValues

/-!
# Every native original groupoid path is recovered from its whole normal word

The actual original groupoid path gives its complete admissible native
reduced label word. Full original normal-word injection proves that the
native value of this same word is the original path, retaining each
individual endpoint and all original generators.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The native value of the SAME full original reduced-word path is exactly the original
groupoid path. -/
lemma normalWord_value_recovery {x y : V}
    (f : (Quiver.FreeGroupoid.of V).obj x ⟶ (Quiver.FreeGroupoid.of V).obj y) :
    (normalWord_admissible V x y f).value = f := by
  apply normalWord_injective V _ _
  exact (Admissible.normalWord_value V (normalWord_admissible V x y f)).trans
    (normalWord_reduced V f)

/-- Every SAME full original normal word is reduced under the native free-group criterion. -/
lemma normalWord_isReduced {x y : Quiver.FreeGroupoid V} (f : x ⟶ y) : FreeGroup.IsReduced
  (normalWord V f) := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  exact FreeGroup.IsReduced.of_reduce_eq (normalWord_reduced V f)

end Quiver.FreeGroupoid.OriginalWords
