/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidSignedPathLabels

/-!
# Actual endpoint admissibility of full original signed label words

A signed label retains its individual original source/target/arrow.
Admissibility records only the literal endpoint matching of all
original labels. Complete native signed paths give those words,
and every admissible word reconstructs an actual original signed path.
No groupoid faithfulness, tree or weak outcome is a premise.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The actual source of the SAME original signed label. -/
def labelSource (a : Labels V × Bool) : V := if a.2 then a.1.1 else a.1.2.1

/-- The actual target of the SAME original signed label. -/
def labelTarget (a : Labels V × Bool) : V := if a.2 then a.1.2.1 else a.1.1

/-- The SAME entire original signed arrow at its exact signed label endpoints. -/
def labelArrow (a : Labels V × Bool) :
    @Quiver.Hom (Quiver.Symmetrify V) (Quiver.symmetrifyQuiver V) (labelSource V a)
      (labelTarget V a) := by
  rcases a with ⟨⟨x, y, a⟩, b⟩
  cases b
  · exact .inr a
  · exact .inl a

/-- Full original endpoint matching of every actual label in the word. -/
inductive Admissible : V → List (Labels V × Bool) → V → Prop
  | nil (x : V) : Admissible x [] x
  | cons (a : Labels V × Bool) (L : List (Labels V × Bool)) (z : V)
      (h : Admissible (labelTarget V a) L z) : Admissible (labelSource V a) (a :: L) z

/-- Concatenating complete admissible original words keeps the SAME intermediate endpoint. -/
lemma Admissible.append {x y z : V} {L M : List (Labels V × Bool)}
    (hL : Admissible V x L y) (hM : Admissible V y M z) : Admissible V x (L ++ M) z := by
  induction hL with
  | nil => exact hM
  | cons a L y h ih => exact Admissible.cons a (L ++ M) z (ih hM)

/-- The entire one-letter original signed arrow is admissible at its SAME actual endpoints. -/
lemma arrowLabel_admissible {x y : Quiver.Symmetrify V} (a : x ⟶ y) :
    Admissible V x [arrowLabel V a] y := by
  change Sum (@Quiver.Hom V inferInstance x y) (@Quiver.Hom V inferInstance y x) at a
  cases a with
  | inl a =>
    exact @Admissible.cons V inferInstance (⟨x, y, a⟩,
    true) [] y (@Admissible.nil V inferInstance y)
  | inr a =>
    exact @Admissible.cons V inferInstance (⟨y, x, a⟩,
    false) [] y (@Admissible.nil V inferInstance y)

/-- Every actual full native original signed path has an admissible original label sequence. -/
lemma signedPathLabels_admissible {x y : Quiver.Symmetrify V} (p : Quiver.Path x y) :
    Admissible V x (signedPathLabels V p) y := by
  induction p with
  | nil => exact Admissible.nil _
  | cons p a ih =>
    exact Admissible.append V ih (arrowLabel_admissible V a)

/-- Every complete endpoint-admissible original word has an actual native signed path with
the SAME full labels. -/
theorem Admissible.exists_path {x y : V} {L : List (Labels V × Bool)} (h : Admissible V x L y) :
    ∃ p : @Quiver.Path (Quiver.Symmetrify V) (Quiver.symmetrifyQuiver V) x y,
      signedPathLabels V p = L := by
  induction h with
  | nil x => exact ⟨Quiver.Path.nil, rfl⟩
  | cons a L z h ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨(labelArrow V a).toPath.comp p, ?_⟩
    have he : arrowLabel V (labelArrow V a) = a := by
      rcases a with ⟨⟨x, y, a⟩, b⟩
      cases b <;> rfl
    exact (signedPathLabels_comp V (labelArrow V a).toPath p).trans
      ((congrArg₂ List.append (signedPathLabels_toPath V (labelArrow V a)) hp).trans
        (congrArg (fun z => [z] ++ L) he))

/-- The actual original signed path supplied by full endpoint admissibility. -/
def Admissible.toPath {x y : V} {L : List (Labels V × Bool)} (h : Admissible V x L y) :
    @Quiver.Path (Quiver.Symmetrify V) (Quiver.symmetrifyQuiver V) x y :=
  Classical.choose h.exists_path

/-- Every reconstructed original signed path retains the SAME entire original label word. -/
lemma Admissible.toPath_labels {x y : V} {L : List (Labels V × Bool)} (h : Admissible V x L y) :
    signedPathLabels V h.toPath = L := Classical.choose_spec h.exists_path

end Quiver.FreeGroupoid.OriginalWords
