/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Integer graded exact group sequences with three positions

The index has a source, target and cofiber position at each integer degree.
After the cofiber position its successor is the source in the preceding
degree. A sequence retains every group, every differential, its trivial
two-step composites and its image/kernel equalities. Morphisms retain every
group homomorphism and every differential square.

The trivial group homomorphism is denoted by `1`, as in `GrpCat`; its value
on every element is the group unit.
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory

namespace GrpCat.IntegerSequence

/-- The three consecutive positions in each integer row. -/
inductive Position where
  | source
  | target
  | cofiber
  deriving DecidableEq

/-- Every integer degree retains all three distinct group positions. -/
abbrev Index := ℤ × Position

/-- The next differential lowers the degree exactly when it leaves the cofiber. -/
def next : Index → Index
  | (q, .source) => (q, .target)
  | (q, .target) => (q, .cofiber)
  | (q, .cofiber) => (q - 1, .source)

/-- The preceding differential raises the degree exactly before the source position. -/
def prev : Index → Index
  | (q, .source) => (q + 1, .cofiber)
  | (q, .target) => (q, .source)
  | (q, .cofiber) => (q, .target)

/-- Three differentials return to the same position in the preceding integer degree. -/
theorem next_three (q : ℤ) (p : Position) :
    next (next (next (q, p))) = (q - 1, p) := by
  cases p <;> rfl

@[simp]
theorem prev_next (i : Index) : prev (next i) = i := by
  rcases i with ⟨q, p⟩
  cases p <;> simp [next, prev]

@[simp]
theorem next_prev (i : Index) : next (prev i) = i := by
  rcases i with ⟨q, p⟩
  cases p <;> simp [next, prev]

end GrpCat.IntegerSequence

namespace GrpCat

/-- A full integer graded group sequence, exact after every original differential. -/
structure IntegerExactSequence where
  /-- The complete original group at every integer degree and position. -/
  term : IntegerSequence.Index → GrpCat.{v}
  /-- The entire group homomorphism to the next position. -/
  differential : ∀ i, term i ⟶ term (IntegerSequence.next i)
  differential_comp : ∀ i,
    differential i ≫ differential (IntegerSequence.next i) = 1
  exact : ∀ i,
    Function.MulExact (differential i).hom
      (differential (IntegerSequence.next i)).hom

namespace IntegerExactSequence

open IntegerSequence

/-- A map of full integer sequences, with a square for every differential. -/
structure Hom (S T : IntegerExactSequence.{v}) where
  /-- Every complete group component of the original sequence morphism. -/
  app : ∀ i, S.term i ⟶ T.term i
  comm : ∀ i, app i ≫ T.differential i = S.differential i ≫ app (next i)

namespace Hom

@[ext]
theorem ext {S T : IntegerExactSequence.{v}} {f g : Hom S T}
    (h : ∀ i, f.app i = g.app i) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      cases hfg
      rfl

/-- The identity keeps the identity homomorphism of every original integer group. -/
def id (S : IntegerExactSequence.{v}) : Hom S S where
  app i := 𝟙 (S.term i)
  comm i := by rw [Category.id_comp, Category.comp_id]

/-- Composition uses the entire original group homomorphisms in their given order. -/
def comp {S T U : IntegerExactSequence.{v}} (f : Hom S T) (g : Hom T U) : Hom S U where
  app i := f.app i ≫ g.app i
  comm i := by
    rw [Category.assoc, g.comm i, ← Category.assoc, f.comm i, Category.assoc]

end Hom

instance : Category IntegerExactSequence.{v} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext fun i => Category.id_comp (f.app i)
  comp_id f := Hom.ext fun i => Category.comp_id (f.app i)
  assoc f g h := Hom.ext fun i => Category.assoc (f.app i) (g.app i) (h.app i)

@[simp]
theorem id_app (S : IntegerExactSequence.{v}) (i : Index) :
    (𝟙 S : S ⟶ S).app i = 𝟙 (S.term i) := rfl

@[simp]
theorem comp_app {S T U : IntegerExactSequence.{v}} (f : S ⟶ T) (g : T ⟶ U)
    (i : Index) : (f ≫ g).app i = f.app i ≫ g.app i := rfl

/-- Evaluation is an actual functor at every integer and every position. -/
def evaluation (i : Index) : IntegerExactSequence.{v} ⥤ GrpCat.{v} where
  obj S := S.term i
  map f := f.app i

/-- All original differentials form natural transformations between the evaluation functors. -/
def differentialNatTrans (i : Index) : evaluation i ⟶ evaluation (next i) where
  app S := S.differential i
  naturality _ _ f := f.comm i

/-- Every two-step differential is the actual constant-unit group homomorphism. -/
theorem differential_comp_apply (S : IntegerExactSequence.{v}) (i : Index) (x : S.term i) :
    (S.differential (next i)).hom ((S.differential i).hom x) = 1 := by
  have h := ConcreteCategory.congr_hom (S.differential_comp i) x
  exact h

/-- Exactness is the literal subgroup equality for the same two differentials. -/
theorem kernel_eq_range (S : IntegerExactSequence.{v}) (i : Index) :
    (S.differential (next i)).hom.ker = (S.differential i).hom.range :=
  (S.exact i).monoidHom_ker_eq

end IntegerExactSequence
end GrpCat
