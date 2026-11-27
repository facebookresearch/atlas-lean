/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidSignedPathRecovery

/-!
# The SAME original completed signed-path value and full native label word

The native quotient functor maps the entire original signed path to
its actual free-groupoid morphism. The actual original labelled functor
reads its whole signed label word in the native free group. All
original generators, inverse generators and concatenations remain.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The native full signed-path quotient map into the SAME original quiver free groupoid. -/
def signedPathFunctor : Paths (Quiver.Symmetrify V) ⥤ Quiver.FreeGroupoid V :=
  CategoryTheory.Quotient.functor (@Quiver.FreeGroupoid.redStep V inferInstance)

/-- The SAME entire original signed path gives its actual full native completed word value. -/
def signedPathValue {x y : Quiver.Symmetrify V} (p : Quiver.Path x y) :
    (signedPathFunctor V).obj x ⟶ (signedPathFunctor V).obj y :=
  (signedPathFunctor V).map p

/-- Every original positive singleton path is the SAME full native original groupoid generator. -/
lemma signedPathValue_positive {x y : V} (a : x ⟶ y) :
    signedPathValue V a.toPosPath = (Quiver.FreeGroupoid.of V).map a := rfl

/-- Every original negative singleton path is the SAME actual inverse native original
groupoid generator. -/
lemma signedPathValue_negative {x y : V} (a : x ⟶ y) :
    signedPathValue V a.toNegPath = inv ((Quiver.FreeGroupoid.of V).map a) := by
  exact (rfl : signedPathValue V a.toNegPath = Groupoid.inv ((Quiver.FreeGroupoid.of V).map
    a)).trans
    (Groupoid.inv_eq_inv ((Quiver.FreeGroupoid.of V).map a))

/-- Every full native signed word keeps its SAME actual full original label word under the
native completed functor. -/
theorem labelled_signedPathValue {x y : Quiver.Symmetrify V} (p : Quiver.Path x y) :
    (labelledFunctor V).map (signedPathValue V p) = MulOpposite.op (FreeGroup.mk
      (signedPathLabels V p)) := by
  induction p with
  | nil =>
    exact (labelledFunctor V).map_id _
  | cons p a ih =>
    have hc : signedPathValue V (p.cons a) = signedPathValue V p ≫ signedPathValue V a.toPath :=
      (signedPathFunctor V).map_comp p a.toPath
    have ha : (labelledFunctor V).map (signedPathValue V a.toPath) =
        MulOpposite.op (FreeGroup.mk [arrowLabel V a]) := by
      change Sum (@Quiver.Hom V inferInstance _ _) (@Quiver.Hom V inferInstance _ _) at a
      cases a with
      | inl a => exact labelledFunctor_generator V a
      | inr a =>
        exact (congrArg (labelledFunctor V).map (signedPathValue_negative V a)).trans
          (labelledFunctor_inverse_generator V a)
    exact (congrArg (labelledFunctor V).map hc).trans
      (((labelledFunctor V).map_comp _ _).trans (congrArg₂ (fun f g => f ≫ g) ih ha))

end Quiver.FreeGroupoid.OriginalWords
