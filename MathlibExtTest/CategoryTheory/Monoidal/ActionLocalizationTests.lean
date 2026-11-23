/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization
public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Tactic.NormNum

/-!
# Consumers of the general action localization

The acting symmetric monoidal groupoid is the discrete additive monoid of
natural numbers. The acted-on category may be the preorder of natural numbers
or a one-object category with distinct noninvertible endomorphisms. These
examples check that arbitrary original arrows survive, and that the quotient
does not identify unequal stabilizer labels or unequal original arrows.

The final example supplies a trivial numerator action on the acting category
itself; the denominator coordinate must still use the canonical tensor action.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalActionCategory
open scoped MonoidalCategory MonoidalLeftAction

namespace MonoidalActionCategoryTests

universe uS vS uX vX

-- Independent object and morphism universes are accepted by the public category.
example (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] :
    Category.{max uS vX} (MonoidalActionCategory S X) := inferInstance

section PublicObjects

variable (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
  (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X]

-- Basic object access works before any product or diagonal action registrations.
example (x : X) : ((SInverse.inclusion S X).obj x).toProd = (x, 𝟙_ S) :=
  SInverse.inclusion_obj S X x

example (a : SInverse S X) :
    ((SInverse.sourceEquivalence S X).functor.obj a).toProd =
      (a.toProd.2, a.toProd.1) :=
  SInverse.sourceEquivalence_obj S X a

example (a : SourceSInverse S X) :
    ((SInverse.sourceEquivalence S X).inverse.obj a).toProd =
      (a.toProd.2, a.toProd.1) := rfl

end PublicObjects

-- The explicit constructor type retains the selected action dictionary.
#check @CategoryTheory.MonoidalActionCategory
#check @CategoryTheory.MonoidalActionCategory.mk

/-- A concrete coherent action used by the consumers below. -/
@[instance_reducible]
private def trivialAction (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] : MonoidalLeftAction S X where
  actionObj _ x := x
  actionHomLeft _ x := 𝟙 x
  actionHomRight _ _ _ f := f
  actionHom _ f := f
  actionAssocIso _ _ x := Iso.refl x
  actionUnitIso x := Iso.refl x
  actionHom_def _ _ := by simp
  actionHomRight_id _ _ := rfl
  id_actionHomLeft _ _ := rfl
  actionHom_comp _ _ _ _ := rfl
  actionAssocIso_hom_naturality _ _ _ := by simp
  actionUnitIso_hom_naturality _ := by simp
  whiskerLeft_actionHomLeft _ _ _ _ _ := by simp
  whiskerRight_actionHomLeft _ _ _ := by simp
  associator_actionHom _ _ _ _ := by simp
  leftUnitor_actionHom _ _ := by simp
  rightUnitor_actionHom _ _ := by simp

private abbrev Stabilizers := Discrete (Multiplicative ℕ)

private instance : SymmetricCategory Stabilizers where
  toBraidedCategory := inferInstance
  symmetry _ _ := Subsingleton.elim _ _

example : IsGroupoid Stabilizers := inferInstance

private instance natAction : MonoidalLeftAction Stabilizers ℕ :=
  trivialAction Stabilizers ℕ

private def rising : (0 : ℕ) ⟶ 1 := homOfLE (Nat.zero_le 1)

private def rawNat (s n m : ℕ) (h : n ≤ m) :
    RawHom (⟨n⟩ : MonoidalActionCategory Stabilizers ℕ) ⟨m⟩ where
  stabilizer := Discrete.mk (Multiplicative.ofAdd s)
  hom := homOfLE h

-- Equal original maps with nonisomorphic stabilizers remain different classes.
example : Hom.mk (rawNat 0 0 1 (Nat.zero_le 1)) ≠
    Hom.mk (rawNat 1 0 1 (Nat.zero_le 1)) := by
  intro h
  obtain ⟨e, _⟩ := (Hom.mk_eq_mk_iff _ _).mp h
  have he : (0 : ℕ) = 1 :=
    congrArg Multiplicative.toAdd (Discrete.eq_of_hom e.hom)
  exact Nat.zero_ne_one he

-- Stabilizers accumulate along two genuinely noninvertible arrows.
example :
    CategoryStruct.comp (obj := MonoidalActionCategory Stabilizers ℕ)
      (X := ⟨0⟩) (Y := ⟨1⟩) (Z := ⟨2⟩)
      (Hom.mk (rawNat 2 0 1 (Nat.zero_le 1)))
      (Hom.mk (rawNat 3 1 2 (by decide))) =
    Hom.mk (rawNat 5 0 2 (Nat.zero_le 2)) := by
  rw [Hom.mk_comp]
  apply (Hom.mk_eq_mk_iff _ _).mpr
  exact ⟨Discrete.eqToIso (by rfl), Subsingleton.elim _ _⟩

section OrderedArrows

attribute [local instance] MonoidalActionCategory.diagonalAction

-- The actual localization receives every original arrow, including 0 → 1.
example : Nonempty ((SInverse.inclusion Stabilizers ℕ).obj 0 ⟶
    (SInverse.inclusion Stabilizers ℕ).obj 1) :=
  ⟨(SInverse.inclusion Stabilizers ℕ).map rising⟩

private theorem noReverse :
    ¬ Nonempty ((SInverse.inclusion Stabilizers ℕ).obj 1 ⟶
      (SInverse.inclusion Stabilizers ℕ).obj 0) := by
  rintro ⟨f⟩
  obtain ⟨r, _⟩ := Hom.exists_rep f
  have h : (1 : ℕ) ≤ 0 := leOfHom r.hom.1
  exact Nat.not_succ_le_zero 0 h

-- The localization is an ordinary category: the inclusion of 0 → 1 is not an iso.
example : ¬ IsIso ((SInverse.inclusion Stabilizers ℕ).map rising) := by
  intro h
  let := h
  exact noReverse ⟨inv ((SInverse.inclusion Stabilizers ℕ).map rising)⟩

-- The inclusion has the specified positive-first object coordinates.
example (n : ℕ) : ((SInverse.inclusion Stabilizers ℕ).obj n).toProd =
    (n, Discrete.mk (Multiplicative.ofAdd 0)) := rfl

attribute [local instance] MonoidalActionCategory.sourceDiagonalAction

-- The source-order equivalence also carries the noninvertible original arrow.
example :
    (SInverse.sourceEquivalence Stabilizers ℕ).functor.map
      ((SInverse.inclusion Stabilizers ℕ).map rising) =
    Hom.mk (RawHom.ofMap (S := Stabilizers)
      (𝟙 (𝟙_ Stabilizers), rising)) := rfl

example (n : ℕ) :
    ((SInverse.sourceEquivalence Stabilizers ℕ).functor.obj
      ((SInverse.inclusion Stabilizers ℕ).obj n)).toProd =
    (Discrete.mk (Multiplicative.ofAdd 0), n) := rfl

end OrderedArrows

section ParallelArrows

private instance : MonoidalLeftAction Stabilizers (SingleObj ℕ) :=
  trivialAction Stabilizers (SingleObj ℕ)

-- The stabilizer quotient preserves distinct original parallel arrows.
example :
    (MonoidalActionCategory.inclusion Stabilizers (SingleObj ℕ)).map
      (((SingleObj.toEnd ℕ) 2).asHom) ≠
    (MonoidalActionCategory.inclusion Stabilizers (SingleObj ℕ)).map
      (((SingleObj.toEnd ℕ) 3).asHom) := by
  intro h
  obtain ⟨_, he⟩ := (Hom.mk_eq_mk_iff _ _).mp h
  change ((3 : ℕ) * 1) * 1 = 2 * 1 at he
  norm_num at he

end ParallelArrows

section CanonicalDenominator

private instance numeratorAction : MonoidalLeftAction Stabilizers Stabilizers :=
  trivialAction Stabilizers Stabilizers

private instance diagonalAction : MonoidalLeftAction Stabilizers (Stabilizers × Stabilizers) :=
  MonoidalActionCategory.diagonalAction Stabilizers Stabilizers

-- A different numerator action cannot replace the denominator's tensor action.
example (s x t : Stabilizers) : s ⊙ₗ (x, t) = (x, s ⊗ t) := rfl

end CanonicalDenominator

#print axioms CategoryTheory.MonoidalActionCategory.category
#print axioms CategoryTheory.MonoidalActionCategory.Hom.mk_eq_mk_iff
#print axioms CategoryTheory.MonoidalActionCategory.Hom.exists_rep
#print axioms CategoryTheory.MonoidalActionCategory.Hom.mk_comp
#print axioms CategoryTheory.MonoidalActionCategory.Hom.mk_id
#print axioms CategoryTheory.MonoidalActionCategory.inclusion
#print axioms CategoryTheory.MonoidalActionCategory.productAction
#print axioms CategoryTheory.MonoidalActionCategory.diagonalAction
#print axioms CategoryTheory.MonoidalActionCategory.SInverse.toProd
#print axioms CategoryTheory.MonoidalActionCategory.SourceSInverse.toProd
#print axioms CategoryTheory.MonoidalActionCategory.SInverse.inclusion
#print axioms CategoryTheory.MonoidalActionCategory.SInverse.inclusion_obj
#print axioms CategoryTheory.MonoidalActionCategory.productSwapEquivalence
#print axioms CategoryTheory.MonoidalActionCategory.SInverse.sourceEquivalence
#print axioms CategoryTheory.MonoidalActionCategory.SInverse.sourceEquivalence_obj

end MonoidalActionCategoryTests

end
