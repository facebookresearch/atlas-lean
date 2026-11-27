/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidNativeNormalForm

/-!
# The full original native reduced-word recognition API

The native quiver free-groupoid morphism retains its entire original
signed-label reduced word. Actual full faithfulness of the original
label functor proves reduced-word injection at the same original
endpoints. Every reduced word is admissible and has an actual native
original signed-path representative with the same full value.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The SAME original full native groupoid morphism is detected by its actual reduced-label word. -/
theorem normalWord_injective (x y : Quiver.FreeGroupoid V) : Function.Injective (normalWord
  V (x := x) (y := y)) := by
  intro f g h
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  apply (labelledFunctor V).map_injective
  apply MulOpposite.unop_injective
  exact FreeGroup.toWord_injective h

/-- Every actual full original reduced word retains native reduction idempotence. -/
lemma normalWord_reduced {x y : Quiver.FreeGroupoid V} (f : x ⟶ y) :
    @FreeGroup.reduce (Labels V) (Classical.decEq _) (normalWord V f) = normalWord V f := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  exact @FreeGroup.reduce_toWord (Labels V) (Classical.decEq _)
    (MulOpposite.unop ((labelledFunctor V).map f))

/-- The actual native quotient gives full original signed-path representatives,
retaining individual original endpoints and every coefficient. -/
theorem normalWord_admissible (x y : V)
    (f : (Quiver.FreeGroupoid.of V).obj x ⟶ (Quiver.FreeGroupoid.of V).obj y) :
    Admissible V x (normalWord V f) y := by
  classical
  let _ : (signedPathFunctor V).Full := CategoryTheory.Quotient.full_functor
    (@Quiver.FreeGroupoid.redStep V inferInstance)
  obtain ⟨p, rfl⟩ := (signedPathFunctor V).map_surjective f
  have h := signedPathLabels_admissible V p
  have hn : normalWord V (signedPathValue V p) =
      @FreeGroup.reduce (Labels V) (Classical.decEq _) (signedPathLabels V p) := by
    unfold normalWord
    have he := labelled_signedPathValue V p
    rw [he]
    rfl
  exact hn ▸ reducedWord_admissible V h

end Quiver.FreeGroupoid.OriginalWords
