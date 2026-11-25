/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidAdmissibleWords

/-!
# Lossless complete original signed-path labels

Each full original signed label retains source, target and arrow.
Every full native signed path is recovered from its complete original
label list, including all intermediate vertices and orientations.
No groupoid quotient faithfulness or weak theorem is assumed here.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- The SAME full original signed arrow label reads its actual original source vertex. -/
lemma arrowLabel_source {x y : Quiver.Symmetrify V} (a : x ⟶ y) : labelSource V
  (arrowLabel V a) = x := by
  change Sum (@Quiver.Hom V inferInstance x y) (@Quiver.Hom V inferInstance y x) at a
  cases a <;> rfl

/-- The SAME full original signed arrow label reads its actual original target vertex. -/
lemma arrowLabel_target {x y : Quiver.Symmetrify V} (a : x ⟶ y) : labelTarget V
  (arrowLabel V a) = y := by
  change Sum (@Quiver.Hom V inferInstance x y) (@Quiver.Hom V inferInstance y x) at a
  cases a <;> rfl

/-- The actual original signed label reconstructs the SAME full signed arrow coefficient. -/
lemma labelArrow_arrowLabel_heq {x y : Quiver.Symmetrify V} (a : x ⟶ y) :
    HEq (labelArrow V (arrowLabel V a)) a := by
  change Sum (@Quiver.Hom V inferInstance x y) (@Quiver.Hom V inferInstance y x) at a
  cases a <;> rfl

/-- The whole original signed-label list retains the SAME native path length. -/
lemma signedPathLabels_length {x y : Quiver.Symmetrify V} (p : Quiver.Path x y) :
    (signedPathLabels V p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p a ih => simpa only [signedPathLabels, List.length_append, List.length_singleton,
      Quiver.Path.length_cons] using congrArg Nat.succ ih

/-- Full original label equality retains both actual signed-arrow endpoints. -/
lemma arrowLabel_endpoints {x y x' y' : Quiver.Symmetrify V} (a : x ⟶ y) (b : x' ⟶ y')
    (h : arrowLabel V a = arrowLabel V b) : x = x' ∧ y = y' :=
  ⟨(arrowLabel_source V a).symm.trans ((congrArg (labelSource V) h).trans (arrowLabel_source V b)),
    (arrowLabel_target V a).symm.trans ((congrArg (labelTarget V) h).trans (arrowLabel_target V b))⟩

/-- Equal whole original signed labels retain the SAME complete dependent signed-arrow
coefficient. -/
lemma labelArrow_heq_of_eq {a b : Labels V × Bool} (h : a =
  b) : HEq (labelArrow V a) (labelArrow V b) := by
  cases h
  rfl

/-- Equal full original signed labels retain EVERY actual signed-arrow coefficient. -/
lemma arrowLabel_arrow_heq {x y x' y' : Quiver.Symmetrify V} (a : x ⟶ y) (b : x' ⟶ y')
    (h : arrowLabel V a = arrowLabel V b) : HEq a b :=
  (labelArrow_arrowLabel_heq V a).symm.trans
    ((labelArrow_heq_of_eq V h).trans (labelArrow_arrowLabel_heq V b))

/-- The SAME original complete native signed path is recovered injectively from all original
labels. -/
theorem signedPathLabels_injective (x y : Quiver.Symmetrify V) :
    Function.Injective (signedPathLabels V (x := x) (y := y)) := by
  intro p
  induction p with
  | nil =>
    intro q h
    have hl : q.length = 0 := by
      have he := congrArg List.length h
      exact (signedPathLabels_length V q).symm.trans he.symm
    exact (Quiver.Path.eq_nil_of_length_zero q hl).symm
  | @cons z t p a ih =>
    intro q h
    cases q with
    | nil =>
      have he := congrArg List.length h
      simp only [signedPathLabels, List.length_append, List.length_singleton, List.length_nil] at he
      omega
    | @cons z' t q b =>
      have he := congrArg List.reverse h
      have hpair : arrowLabel V a = arrowLabel V b ∧ signedPathLabels V p =
        signedPathLabels V q := by
        simp only [signedPathLabels, List.reverse_append, List.reverse_singleton,
          List.singleton_append,
          List.cons.injEq] at he
        exact ⟨he.1, List.reverse_injective he.2⟩
      have hz := (arrowLabel_endpoints V a b hpair.1).1
      subst z'
      have hp := ih hpair.2
      subst q
      have hab := eq_of_heq (arrowLabel_arrow_heq V a b hpair.1)
      subst b
      rfl

end Quiver.FreeGroupoid.OriginalWords
