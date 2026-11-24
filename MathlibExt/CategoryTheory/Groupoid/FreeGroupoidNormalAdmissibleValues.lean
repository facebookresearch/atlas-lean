/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidOriginalNormalWords

/-!
# Exact native reduced-word value recovery

Every complete original admissible word gives its actual native
signed-path value. Its original reduced label word is precisely the
native reduction of that SAME entire original label sequence. For
native reduced words this is the original sequence, with individual
endpoints and all arrow coefficients retained.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The SAME full native original signed-path value has exactly its native reduced original
labels. -/
lemma normalWord_signedPathValue {x y : Quiver.Symmetrify V} (p : Quiver.Path x y) :
    normalWord V (signedPathValue V p) =
      @FreeGroup.reduce (Labels V) (Classical.decEq _) (signedPathLabels V p) := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  unfold normalWord
  exact (congrArg (@FreeGroup.toWord (Labels V) (Classical.decEq _))
    (congrArg MulOpposite.unop (labelled_signedPathValue V p))).trans FreeGroup.toWord_mk

/-- The actual native value of EVERY full original admissible word retains its SAME native
label reduction. -/
lemma Admissible.normalWord_value {x y : V} {L : List (Labels V × Bool)} (h : Admissible V x L y) :
    normalWord V h.value = @FreeGroup.reduce (Labels V) (Classical.decEq _) L := by
  exact (normalWord_signedPathValue V h.toPath).trans
    (congrArg (@FreeGroup.reduce (Labels V) (Classical.decEq _)) h.toPath_labels)

/-- A native reduced original word is read back exactly by its SAME actual signed-path value. -/
lemma Admissible.normalWord_value_of_reduced {x y : V} {L : List (Labels V × Bool)}
    (h : Admissible V x L y) (hL : FreeGroup.IsReduced L) : normalWord V h.value = L := by
  classical
  let _ : DecidableEq (Labels V) := Classical.decEq _
  exact (Admissible.normalWord_value V h).trans hL.reduce_eq

end Quiver.FreeGroupoid.OriginalWords
