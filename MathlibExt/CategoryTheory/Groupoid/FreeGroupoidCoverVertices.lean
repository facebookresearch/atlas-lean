/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidNormalWordEdges

/-!
# The actual original free-groupoid covering vertices

A cover vertex is an individual original target object and an actual
full native groupoid path from the fixed original base object.
Every native reduced label word remains admissible at those SAME
original endpoints. Original generator edges append the SAME actual
full arrow to that native path. No tree or weak conclusion is assumed.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)

/-- An original target vertex and full native original groupoid path from the SAME base vertex. -/
structure CoverVertex where
  /-- The SAME individual original target vertex. -/
  target : V
  /-- The actual full native groupoid path. -/
  path : (Quiver.FreeGroupoid.of V).obj z ⟶ (Quiver.FreeGroupoid.of V).obj target

/-- The original identity path at the SAME fixed base vertex. -/
def coverRoot : CoverVertex V z := ⟨z, 𝟙 _⟩

/-- The actual full reduced original label word of the SAME native cover vertex. -/
def CoverVertex.word (a : CoverVertex V z) : List (Labels V × Bool) := normalWord V a.path

/-- Every original full cover word is admissible at the SAME individual source and target. -/
lemma CoverVertex.word_admissible (a : CoverVertex V z) : Admissible V z a.word a.target :=
  normalWord_admissible V z a.target a.path

/-- Append the SAME full original generating arrow to an actual original covering vertex. -/
def CoverVertex.append (a : CoverVertex V z) {y : V} (e : a.target ⟶ y) : CoverVertex V z :=
  ⟨y, a.path ≫ (Quiver.FreeGroupoid.of V).map e⟩

/-- The entire original cover edge has the exact SAME native reduced-word append/cancel readback. -/
lemma CoverVertex.append_word (a : CoverVertex V z) {y : V} (e : a.target ⟶ y) :
    letI : DecidableEq (Labels V) := Classical.decEq _
    (CoverVertex.append V z a e).word = if a.word.getLast? = some (⟨a.target, y, e⟩, false) then
      a.word.dropLast else a.word.concat (⟨a.target, y, e⟩, true) :=
  normalWord_comp_generator V a.path e

/-- Each actual original admissible label sequence determines its SAME individual target vertex. -/
lemma Admissible.target_unique {x y y' : V} {L : List (Labels V × Bool)}
    (h : Admissible V x L y) (h' : Admissible V x L y') : y = y' := by
  induction h generalizing y' with
  | nil =>
    cases h'
    rfl
  | cons a L y h ih =>
    have ht := (Admissible.cons_iff V a L).mp h'
    exact ih ht.2

/-- Full original reduced-word equality determines BOTH the target object and SAME entire
native path. -/
theorem CoverVertex.word_injective : Function.Injective (CoverVertex.word (V := V) (z := z)) := by
  intro a b h
  have ht : a.target = b.target := Admissible.target_unique V a.word_admissible
    (h.symm ▸ b.word_admissible)
  cases a with
  | mk x f =>
    cases b with
    | mk y g =>
      change x = y at ht
      subst y
      have hp : f = g := normalWord_injective V _ _ h
      subst g
      rfl

end Quiver.FreeGroupoid.OriginalWords
