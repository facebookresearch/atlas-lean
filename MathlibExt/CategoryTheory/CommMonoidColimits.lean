/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
copied from `Mathlib/Algebra/Category/MonCat/Colimits.lean` in
leanprover-community/mathlib4 at revision 56a005855ea17e0b0958f73ec801ae140b0a1679;
the free-expression colimit construction is kept, the commutativity relation and
its case of the universal property are added, and the result is specialized to
`CommMonCat` (pinned Mathlib provides colimits in `MonCat` only).
-/

module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Complete colimits of commutative monoids

The native CommMonCat colimit is a quotient of finite monoid expressions on
the diagram's elements. Diagram, multiplication, unit and commutativity
relations are imposed explicitly; the desc map and colimit universal property
are proved. This completed provider supports actual monoid stalks and sheaf
pushouts in logarithmic geometry.
-/

@[expose] public section

universe v u

open CategoryTheory Limits CommMonCat

namespace MathlibExt.CategoryTheory.CommMonoidColimits

/-!
We build the colimit of a diagram in `CommMonCat` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [Category.{u} J] (F : J ⥤ CommMonCat.{v})

/-- An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | one : Prequotient
  | mul : Prequotient → Prequotient → Prequotient

instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.one⟩

open Prequotient

/-- The relation on `Prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z),
      Relation x z -- There's always a `map` relation
  | map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      -- Then one relation per operation, describing the interaction with `of`
      Relation (Prequotient.of j' ((F.map f) x)) (Prequotient.of j x)
  | mul : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x * y))
      (mul (Prequotient.of j x) (Prequotient.of j y))
  | one : ∀ j, Relation (Prequotient.of j 1) one -- Then one relation per argument of each operation
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    -- And one relation per monoid law
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | mul_comm : ∀ x y, Relation (mul x y) (mul y x)
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x

/-- The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
instance colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

/-- The underlying type of the colimit of a diagram in `CommMonCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
deriving Inhabited

instance commMonoidColimitType : CommMonoid (ColimitType F) where
  one := Quotient.mk _ one
  mul := Quotient.map₂ mul fun _ x' rx y _ ry =>
    Setoid.trans (Relation.mul_1 _ _ y rx) (Relation.mul_2 x' _ _ ry)
  one_mul := Quotient.ind fun _ => Quotient.sound <| Relation.one_mul _
  mul_one := Quotient.ind fun _ => Quotient.sound <| Relation.mul_one _
  mul_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
    Quotient.sound <| Relation.mul_assoc _ _ _
  mul_comm := Quotient.ind₂ fun _ _ => Quotient.sound <| Relation.mul_comm _ _

@[simp]
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
theorem quot_mul (x y : Prequotient F) : Quot.mk Setoid.r (mul x y) =
    @HMul.hMul (ColimitType F) (ColimitType F) (ColimitType F) _
      (Quot.mk Setoid.r x) (Quot.mk Setoid.r y) :=
  rfl

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : CommMonCat :=
  of (ColimitType F)

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
  { toFun := coconeFun F j
    map_one' := Quot.sound (Relation.one _)
    map_mul' _ _ := Quot.sound (Relation.mul _ _ _) }

@[simp]
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The cocone over the proposed colimit monoid. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp]
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | one => 1
  | mul x y => descFunLift _ x * descFunLift _ y

/-- The function from the colimit monoid to the cone point of any other cocone. -/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl x => rfl
    | symm x y _ h => exact h.symm
    | trans x y z _ _ h₁ h₂ => exact h₁.trans h₂
    | map j j' f x => exact s.w_apply f x
    | mul j x y => exact map_mul (s.ι.app j).hom x y
    | one j => exact map_one (s.ι.app j).hom
    | mul_1 x x' y _ h => congrm $h * _
    | mul_2 x y y' _ h => congrm _ * $h
    | mul_assoc x y z => exact mul_assoc _ _ _
    | mul_comm x y => exact mul_comm _ _
    | one_mul x => exact one_mul _
    | mul_one x => exact mul_one _

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt :=
  ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_mul' x y := by
      induction x using Quot.inductionOn
      induction y using Quot.inductionOn
      solve_by_elim }

set_option backward.isDefEq.respectTransparency false in
/-- Evidence that the proposed colimit is the colimit. -/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := by
    ext x
    induction x using Quot.inductionOn with | h x => ?_
    induction x with
    | of j =>
      change _ = s.ι.app j _
      rw [← w j]
      rfl
    | one =>
      rw [quot_one, map_one]
      rfl
    | mul x y hx hy =>
      rw [quot_mul, map_mul, hx, hy]
      solve_by_elim

instance hasColimitsCommMonCat : HasColimits CommMonCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end MathlibExt.CategoryTheory.CommMonoidColimits
