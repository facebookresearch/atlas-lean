/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidAdmissibleValue

/-!
# Actual native original values survive word reduction

The original adjacent inverse-label pair is the SAME original arrow
followed by its native reverse. The native quiver free-groupoid
quotient relates that full backtrack to the original identity.
Complete original prefix and suffix words retain the actual value
through every native reduction step.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- Native original signed-arrow backtracking is precisely the original quotient relation. -/
lemma signedPathValue_backtrack {x y : Quiver.Symmetrify V} (a : x ⟶ y) :
    signedPathValue V (a.toPath.comp (Quiver.reverse a).toPath) = 𝟙 ((signedPathFunctor V).obj x) :=
  (CategoryTheory.Quotient.sound (@Quiver.FreeGroupoid.redStep V inferInstance)
    (Quiver.FreeGroupoid.redStep.step x y a)).symm

/-- The SAME native original labelled inverse pair is an actual full original backtrack. -/
lemma labelArrow_inverse_pair (a : Labels V) (b : Bool) :
    HEq (labelArrow V (a, !b)) (Quiver.reverse (labelArrow V (a, b))) := by
  rcases a with ⟨x, y, a⟩
  cases b <;> rfl

/-- The actual original value of a full adjacent inverse-label pair is the SAME native
original identity. -/
lemma Admissible.value_inverse_pair (a : Labels V) (b : Bool)
    (h : Admissible V (labelSource V (a, b)) [(a, b), (a, !b)] (labelSource V (a, b))) :
    h.value = 𝟙 ((signedPathFunctor V).obj (labelSource V (a, b))) := by
  let e := labelArrow V (a, b)
  have he : arrowLabel V e = (a, b) := by
    rcases a with ⟨x, y, a⟩
    cases b <;> rfl
  have hl : signedPathLabels V (e.toPath.comp (Quiver.reverse e).toPath) = [(a, b), (a, !b)] :=
    (signedPathLabels_comp V _ _).trans
      ((congrArg₂ List.append (signedPathLabels_toPath V e)
        (signedPathLabels_toPath V (Quiver.reverse e))).trans
        (congrArg₂ List.append (congrArg List.singleton he)
          (congrArg List.singleton ((arrowLabel_reverse V e).trans
            (congrArg (fun c => (c.1, !c.2)) he)))))
  exact (Admissible.value_path V h (e.toPath.comp (Quiver.reverse e).toPath) hl).trans
    (signedPathValue_backtrack V e)

/-- EVERY native original reduction step preserves the SAME actual full free-groupoid word value. -/
lemma value_eq_of_redStep {x y : V} {L M : List (Labels V × Bool)}
    (hL : Admissible V x L y) (hM : Admissible V x M y) (h : FreeGroup.Red.Step L M) :
    hL.value = hM.value := by
  cases h with
  | @not A B a b =>
    obtain ⟨s, hs, ht⟩ := (Admissible.append_iff V A ((a, b) :: (a, !b) :: B)).mp hL
    obtain ⟨t, hst, hty⟩ := (Admissible.append_iff V [(a, b), (a, !b)] B).mp ht
    have he := admissible_inverse_pair_endpoint V a b hst
    subst t
    have hsource := (Admissible.cons_iff V (a, b) [(a, !b)]).mp hst
    have hsEq : s = labelSource V (a, b) := hsource.1
    subst s
    have hp := Admissible.value_inverse_pair V a b hst
    calc
      hL.value = hs.value ≫ ((Admissible.append V hst hty).value) :=
        Admissible.value_append V hs (Admissible.append V hst hty)
      _ = hs.value ≫ (hst.value ≫ hty.value) := congrArg (fun f => hs.value ≫ f)
        (Admissible.value_append V hst hty)
      _ = hs.value ≫ hty.value := by rw [hp, Category.id_comp]
      _ = hM.value := (Admissible.value_append V hs hty).symm

/-- The full original native reduction relation preserves the SAME actual complete original
word value. -/
lemma value_eq_of_red {x y : V} {L M : List (Labels V × Bool)}
    (hL : Admissible V x L y) (hM : Admissible V x M y) (h : FreeGroup.Red L M) : hL.value =
      hM.value := by
  induction h with
  | refl => rfl
  | tail h hs ih =>
    have hN := admissible_of_red V hL h
    exact (ih hN).trans (value_eq_of_redStep V hN hM hs)

end Quiver.FreeGroupoid.OriginalWords
