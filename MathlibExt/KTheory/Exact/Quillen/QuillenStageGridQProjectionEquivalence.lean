/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridFiberConnected
public import Mathlib.CategoryTheory.PUnit

/-!
# The retained-Q projection is an equivalence

The final extracted edgewise vertex is the final zero-row object of a finite
Stage.  Injectivity of underlying Quillen isomorphisms and final-zero-row
Stage extensionality therefore make the extracted-Q functor faithful.  The
iso-comma category of Stage-grid lifts consequently has subsingleton hom
types.

The direct morphism already constructed inside every strict retained-Q fiber
then proves fullness of the retained-Q projection.  Together with its landed
essential surjectivity this gives a categorical equivalence in every simplex
degree, and every strict fiber is equivalent to `Discrete PUnit`.

All fullness, faithfulness, and equivalence witnesses in this file are
theorem-valued.  No global instance, nerve or realization result, Stage-side
comparison, or Q/S statement is introduced.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The canonical Waldhausen structure used for the original retained-Q projection equivalence. -/
local instance quillenStageGridQProjectionEquivalenceWaldhausenCategory :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- At the final simplex vertex, the edgewise cross interval is exactly the
final zero-row interval. -/
theorem edgewiseStageVertexIndex_last (a : SimplexCategory) :
    interval
        (edgewiseLeftIndex a (Fin.last a.len))
        (edgewiseRightIndex a (Fin.last a.len))
        (edgewiseStageVertex_le a (Fin.last a.len)) =
      interval 0 (Fin.last (edgewiseQ.obj a).len) (Fin.zero_le _) := by
  have hLeft : edgewiseLeftIndex a (Fin.last a.len) = 0 := by
    apply Fin.ext
    simp only [edgewiseLeftIndex_val, Fin.val_last, Fin.val_zero]
    omega
  have hRight : edgewiseRightIndex a (Fin.last a.len) =
      Fin.last (edgewiseQ.obj a).len := by
    apply Fin.ext
    simp only [edgewiseRightIndex_val, Fin.val_last, edgewiseQ_obj_len]
    omega
  exact Arrow.ext hLeft hRight (Subsingleton.elim _ _)

set_option linter.defProp false in
/-- Extracting the Quillen simplex from a weak edgewise Stage is faithful.
Only the final extracted vertex is needed. -/
@[instance_reducible, no_expose]
noncomputable def edgewiseStageQuillenSimplexFunctorFaithful
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (edgewiseStageQuillenSimplexFunctor C a).Faithful := by
  constructor
  intro A B f g h
  have hLast := congrArg
    (fun η => η.app (Fin.last a.len)) h
  simp only [edgewiseStageQuillenSimplexFunctor_map,
    edgewiseStageQuillenSimplexMap_app] at hLast
  have hVertexIso :
      edgewiseStageVertexIso f (Fin.last a.len) =
        edgewiseStageVertexIso g (Fin.last a.len) :=
    QuillenQ.underlyingIso_hom_injective hLast
  have hStageApp := congrArg Iso.hom hVertexIso
  simp only [edgewiseStageVertexIso_hom] at hStageApp
  apply WideSubcategory.hom_ext
  apply Stage.hom_ext_zeroRow_last
  change f.hom.hom.app
      (interval 0 (Fin.last (edgewiseQ.obj a).len) (Fin.zero_le _)) =
    g.hom.hom.app
      (interval 0 (Fin.last (edgewiseQ.obj a).len) (Fin.zero_le _))
  rw [← edgewiseStageVertexIndex_last a]
  exact hStageApp

/-- Between two Stage-grid lifts there is at most one morphism. -/
theorem quillenStageGridLift_hom_subsingleton
    {a : SimplexCategory} (X Y : QuillenStageGridLift C a) :
    Subsingleton (X ⟶ Y) :=
  ⟨fun f g => by
    let _ : IsIso Y.obj.hom := QuillenStageGridLift.agreement_isIso Y
    have hRight : f.hom.right = g.hom.right := Subsingleton.elim _ _
    have hMap :
        (edgewiseStageQuillenSimplexFunctor C a).map f.hom.left =
          (edgewiseStageQuillenSimplexFunctor C a).map g.hom.left := by
      apply (cancel_mono Y.obj.hom).1
      calc
        (edgewiseStageQuillenSimplexFunctor C a).map f.hom.left ≫
              Y.obj.hom =
            X.obj.hom ≫
              (quillenQSimplexDiscreteInclusion C a).map f.hom.right :=
          f.hom.w
        _ = X.obj.hom ≫
              (quillenQSimplexDiscreteInclusion C a).map g.hom.right := by
          rw [hRight]
        _ = (edgewiseStageQuillenSimplexFunctor C a).map g.hom.left ≫
              Y.obj.hom := g.hom.w.symm
    have hLeft : f.hom.left = g.hom.left :=
      (edgewiseStageQuillenSimplexFunctorFaithful C a).map_injective hMap
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact hLeft
    · exact hRight⟩

/-- Every pair of objects in one strict retained-Q fiber admits a morphism. -/
theorem quillenStageGridFiber_hom_nonempty
    {a : SimplexCategory} {q : QuillenQSimplex C a}
    (X Y : QuillenStageGridFiber q) :
    Nonempty (X ⟶ Y) :=
  ⟨QuillenStageGridFiberComparison.fiberHom X Y⟩

set_option linter.defProp false in
/-- The retained-Q projection is full.  A target morphism supplies the
endpoint equality used to place both lifts in one strict fiber. -/
@[instance_reducible, no_expose]
noncomputable def quillenStageGridQProjectionFull
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).Full := by
  constructor
  intro X Y h
  let P := quillenStageGridQProjection C a
  let e : P.obj X = P.obj Y := IsDiscrete.eq_of_hom h
  let XF : QuillenStageGridFiber (C := C) X.q := ⟨X, rfl⟩
  let YF : QuillenStageGridFiber (C := C) X.q := ⟨Y, e.symm⟩
  obtain ⟨f⟩ := quillenStageGridFiber_hom_nonempty XF YF
  exact ⟨f.1, Subsingleton.elim _ _⟩

set_option linter.defProp false in
/-- The retained-Q projection is faithful. -/
@[instance_reducible, no_expose]
def quillenStageGridQProjectionFaithful
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).Faithful := by
  constructor
  intro X Y f g _
  exact (quillenStageGridLift_hom_subsingleton X Y).allEq f g

set_option linter.defProp false in
/-- The retained-Q projection is an equivalence of categories. -/
@[instance_reducible, no_expose]
noncomputable def quillenStageGridQProjectionIsEquivalence
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).IsEquivalence where
  faithful := quillenStageGridQProjectionFaithful C a
  full := quillenStageGridQProjectionFull C a
  essSurj := quillenStageGridQProjection_essSurj C a

/-- The degreewise equivalence from Stage-grid lifts to retained Quillen
simplices. -/
noncomputable def quillenStageGridQProjectionEquivalence
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    QuillenStageGridLift C a ≌ Discrete (QuillenQSimplex C a) := by
  let P := quillenStageGridQProjection C a
  letI : P.IsEquivalence := quillenStageGridQProjectionIsEquivalence C a
  exact P.asEquivalence

/-- The forward functor of the bundled equivalence is the retained-Q
projection. -/
@[simp]
theorem quillenStageGridQProjectionEquivalence_functor
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjectionEquivalence C a).functor =
      quillenStageGridQProjection C a :=
  rfl

/-- Hom types in every strict retained-Q fiber are subsingletons. -/
theorem quillenStageGridFiber_hom_subsingleton
    {a : SimplexCategory} (q : QuillenQSimplex C a)
    (X Y : QuillenStageGridFiber q) :
    Subsingleton (X ⟶ Y) :=
  ⟨fun f g => by
    apply Functor.Fiber.hom_ext
    exact (quillenStageGridLift_hom_subsingleton X.1 Y.1).allEq f.1 g.1⟩

/-- Every strict retained-Q fiber is categorically equivalent to a point. -/
noncomputable def quillenStageGridFiberEquivalencePUnit
    {a : SimplexCategory} (q : QuillenQSimplex C a) :
    QuillenStageGridFiber q ≌ Discrete PUnit := by
  apply Nonempty.some
  apply (equiv_punit_iff_unique (C := QuillenStageGridFiber q)).2
  refine ⟨quillenStageGridFiber_nonempty q, ?_⟩
  intro X Y
  obtain ⟨f⟩ := quillenStageGridFiber_hom_nonempty X Y
  let _ : Subsingleton (X ⟶ Y) :=
    quillenStageGridFiber_hom_subsingleton q X Y
  exact ⟨uniqueOfSubsingleton f⟩

section

-- Preserve the original qualified names for the same projection certificates.
open AlgebraicKTheory renaming
  edgewiseStageQuillenSimplexFunctorFaithful → edgewiseStageQuillenSimplexFunctor_faithful,
  quillenStageGridQProjectionFull → quillenStageGridQProjection_full,
  quillenStageGridQProjectionFaithful → quillenStageGridQProjection_faithful,
  quillenStageGridQProjectionIsEquivalence → quillenStageGridQProjection_isEquivalence
export _root_ (edgewiseStageQuillenSimplexFunctor_faithful quillenStageGridQProjection_full
  quillenStageGridQProjection_faithful quillenStageGridQProjection_isEquivalence)

end

end AlgebraicKTheory

end
