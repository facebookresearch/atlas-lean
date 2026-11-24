/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidOriginalWordLabels

/-!
# Complete original signed paths and native reduced labels

The whole original signed path retains every actual original arrow,
its orientation and both individual original endpoints. Native path
concatenation appends those SAME full labels. The actual quiver free
groupoid label functor reads this original complete word exactly.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The SAME signed original generator with its actual original endpoints and orientation. -/
def arrowLabel {x y : Quiver.Symmetrify V} (a : x ⟶ y) : Labels V × Bool :=
  match a with
  | .inl f => (⟨x, y, f⟩, true)
  | .inr f => (⟨y, x, f⟩, false)

/-- The complete original label word of a full native signed path. -/
def signedPathLabels {x : Quiver.Symmetrify V} :
    {y : Quiver.Symmetrify V} → Quiver.Path x y → List (Labels V × Bool)
  | _, .nil => []
  | _, .cons p a => signedPathLabels p ++ [arrowLabel V a]

/-- The full original signed-path concatenation retains every original label in actual order. -/
lemma signedPathLabels_comp {x y z : Quiver.Symmetrify V} (p : Quiver.Path x y) (q :
  Quiver.Path y z) :
    signedPathLabels V (p.comp q) = signedPathLabels V p ++ signedPathLabels V q := by
  induction q with
  | nil => exact (List.append_nil _).symm
  | cons q a ih =>
    exact (congrArg (fun w => w ++ [arrowLabel V a]) ih).trans
      (List.append_assoc _ _ _)

/-- Each original signed generator's actual reverse retains the SAME full original label
with inverted orientation. -/
lemma arrowLabel_reverse {x y : Quiver.Symmetrify V} (a : x ⟶ y) :
    arrowLabel V (Quiver.reverse a) = ((arrowLabel V a).1, !(arrowLabel V a).2) := by
  change Sum (@Quiver.Hom V inferInstance x y) (@Quiver.Hom V inferInstance y x) at a
  cases a <;> rfl

/-- Each full native singleton signed path retains its SAME original arrow label. -/
lemma signedPathLabels_toPath {x y : Quiver.Symmetrify V} (a : x ⟶ y) :
    signedPathLabels V a.toPath = [arrowLabel V a] := rfl

/-- The full original reversed signed path has the SAME native original reversed/inverted
label word. -/
lemma signedPathLabels_reverse {x y : Quiver.Symmetrify V} (p : Quiver.Path x y) :
    signedPathLabels V p.reverse = FreeGroup.invRev (signedPathLabels V p) := by
  induction p with
  | nil => rfl
  | cons p a ih =>
    rw [Quiver.Path.reverse, signedPathLabels_comp, ih]
    rw [signedPathLabels_toPath, arrowLabel_reverse]
    simp only [signedPathLabels, FreeGroup.invRev, List.map_append,
      List.map_singleton, List.reverse_append, List.reverse_singleton]

end Quiver.FreeGroupoid.OriginalWords
