/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidOriginalNormalWords

/-!
# The actual original covering-graph edge on native reduced words

Appending the SAME original generator to a full native groupoid path
changes its original reduced label word by the exact native free-group
rule: either the last inverse label cancels, or the whole original
label is appended. Every original endpoint and arrow coefficient stays
in the word; no covering-tree or weak outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The SAME actual native original generator append has its complete original
cancellation/append formula. -/
theorem normalWord_comp_generator {z x y : V}
    (f : (Quiver.FreeGroupoid.of V).obj z ⟶ (Quiver.FreeGroupoid.of V).obj x) (a : x ⟶ y) :
    letI : DecidableEq (Labels V) := Classical.decEq _
    normalWord V (f ≫ (Quiver.FreeGroupoid.of V).map a) =
      if (normalWord V f).getLast? = some (⟨x, y, a⟩, false) then
        (normalWord V f).dropLast else (normalWord V f).concat (⟨x, y, a⟩, true) := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  have h := (labelledFunctor V).map_comp f ((Quiver.FreeGroupoid.of V).map a)
  have hg := labelledFunctor_generator V a
  have hm : MulOpposite.unop ((labelledFunctor V).map (f ≫ (Quiver.FreeGroupoid.of V).map a)) =
      MulOpposite.unop ((labelledFunctor V).map f) * FreeGroup.of ⟨x, y, a⟩ := by
    exact (congrArg MulOpposite.unop h).trans
      (congrArg (fun b => MulOpposite.unop ((labelledFunctor V).map f) * MulOpposite.unop b) hg)
  exact (congrArg (@FreeGroup.toWord (Labels V) (Classical.decEq _)) hm).trans
    (FreeGroup.toWord_mul_mk_eq (⟨x, y, a⟩ : Labels V) true _)

end Quiver.FreeGroupoid.OriginalWords
