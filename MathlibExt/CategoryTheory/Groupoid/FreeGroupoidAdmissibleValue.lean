/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidSignedPathValue
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidAdmissibleReduction

/-!
# The actual native value of each complete original admissible word

Every original admissible label word reconstructs a full native signed
path. Its actual original free-groupoid value is independent of the
reconstruction because the entire original label sequence is injective
on paths. Native path concatenation gives the SAME original value
composition; no quotient faithfulness or weak conclusion is assumed.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The SAME actual native original groupoid value of a full admissible word. -/
def Admissible.value {x y : V} {L : List (Labels V × Bool)} (h : Admissible V x L y) :
    (signedPathFunctor V).obj x ⟶ (signedPathFunctor V).obj y := signedPathValue V h.toPath

/-- Every full native original path recovers the SAME actual value from its whole original
label word. -/
lemma Admissible.value_path {x y : V} {L : List (Labels V × Bool)}
    (h : Admissible V x L y) (p : @Quiver.Path (Quiver.Symmetrify V)
      (Quiver.symmetrifyQuiver V) x y)
    (hp : signedPathLabels V p = L) : h.value = signedPathValue V p := by
  have he : h.toPath = p := signedPathLabels_injective V x y (h.toPath_labels.trans hp.symm)
  exact congrArg (signedPathValue V) he

/-- Original admissible-word composition is exactly the actual native original groupoid
composition. -/
lemma Admissible.value_append {x y z : V} {L M : List (Labels V × Bool)}
    (hL : Admissible V x L y) (hM : Admissible V y M z) :
    (Admissible.append V hL hM).value = hL.value ≫ hM.value := by
  have h := Admissible.value_path V (Admissible.append V hL hM) (hL.toPath.comp hM.toPath)
    ((signedPathLabels_comp V hL.toPath hM.toPath).trans
      (congrArg₂ List.append hL.toPath_labels hM.toPath_labels))
  exact h.trans ((signedPathFunctor V).map_comp hL.toPath hM.toPath)

/-- The original empty admissible word has the SAME native original identity value. -/
lemma Admissible.value_nil (x : V) : (@Admissible.nil V inferInstance x).value =
  𝟙 ((signedPathFunctor V).obj x) :=
  (Admissible.value_path V (@Admissible.nil V inferInstance x) Quiver.Path.nil rfl).trans
    ((signedPathFunctor V).map_id x)

/-- Every original singleton label has exactly the native full original signed-arrow value. -/
lemma Admissible.value_singleton (a : Labels V × Bool) :
    (@Admissible.cons V inferInstance a [] (labelTarget V a)
      (@Admissible.nil V inferInstance (labelTarget V a))).value =
        signedPathValue V (labelArrow V a).toPath := by
  apply Admissible.value_path V
  exact (signedPathLabels_toPath V (labelArrow V a)).trans (by
    rcases a with ⟨⟨x, y, a⟩, b⟩
    cases b <;> rfl)

end Quiver.FreeGroupoid.OriginalWords
