/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridLift

/-!
# Degreewise Stage-grid lift tests

These tests pin the discrete Q-side, the iso-comma agreement and projections,
the forward lift from a grid, and strict outer reindexing.  They make no
inverse grid choice, fiber-contractibility, nerve, realization, or Q/S claim.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenStageGridLiftTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageGridLiftTestsWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example (a : SimplexCategory) :
    Discrete (QuillenQSimplex C a) ⥤ QuillenQSimplex C a :=
  quillenQSimplexDiscreteInclusion C a

example {a : SimplexCategory} (X : QuillenStageGridLift C a) :
    X.grid = X.obj.left :=
  rfl

example {a : SimplexCategory} (X : QuillenStageGridLift C a) :
    X.q = X.obj.right.as :=
  rfl

example {a : SimplexCategory} (X : QuillenStageGridLift C a)
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized X.grid.obj k l hkl ≫
        X.agreementIso.hom.app l =
      X.agreementIso.hom.app k ≫ X.q.map (homOfLE hkl) :=
  X.shell_agreement hkl

example {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (QuillenStageGridLift.ofGrid A).grid = A := by
  simp

example {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (QuillenStageGridLift.ofGrid A).q =
      (edgewiseStageQuillenSimplexFunctor C a).obj A := by
  simp

example {a : SimplexCategory}
    (A : StageWeakCategory C (edgewiseQ.obj a).len) :
    (QuillenStageGridLift.ofGrid A).agreementIso.hom = 𝟙 _ := by
  exact QuillenStageGridLift.ofGrid_agreementIso_hom A

example {a b : SimplexCategory} (α : a ⟶ b)
    (q : QuillenQSimplex C b) :
    ((quillenQSimplexDiscreteReindex (C := C) α).obj
      (Discrete.mk q)).as =
        (edgewiseQuillenSimplexReindex (C := C) α).obj q :=
  rfl

example {a b : SimplexCategory} (α : a ⟶ b)
    (X : QuillenStageGridLift C b) :
    ((reindexQuillenStageGridLift (C := C) α).obj X).grid =
      (edgewiseStageWeakReindex (C := C) α).obj X.grid :=
  reindexQuillenStageGridLift_obj_grid α X

example {a b : SimplexCategory} (α : a ⟶ b)
    (X : QuillenStageGridLift C b) :
    ((reindexQuillenStageGridLift (C := C) α).obj X).q =
      (edgewiseQuillenSimplexReindex (C := C) α).obj X.q :=
  reindexQuillenStageGridLift_obj_q α X

example (a : SimplexCategory) :
    reindexQuillenStageGridLift (C := C) (𝟙 a) = 𝟭 _ :=
  reindexQuillenStageGridLift_id a

example {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    reindexQuillenStageGridLift (C := C) (α ≫ β) =
      reindexQuillenStageGridLift (C := C) β ⋙
        reindexQuillenStageGridLift (C := C) α :=
  reindexQuillenStageGridLift_comp α β

example {a b : SimplexCategory} (α : a ⟶ b) :
    reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridProjection C a =
      quillenStageGridProjection C b ⋙
        edgewiseStageWeakReindex (C := C) α :=
  reindexQuillenStageGridLift_comp_gridProjection α

example {a b : SimplexCategory} (α : a ⟶ b) :
    reindexQuillenStageGridLift (C := C) α ⋙
        quillenStageGridQProjection C a =
      quillenStageGridQProjection C b ⋙
        quillenQSimplexDiscreteReindex (C := C) α :=
  reindexQuillenStageGridLift_comp_qProjection α

example {a : SimplexCategory} {X Y : QuillenStageGridLift C a}
    (f : X ⟶ Y) :
    (quillenStageGridQProjection C a).map f = f.hom.right :=
  rfl

example {a : SimplexCategory} {X Y : QuillenStageGridLift C a}
    (f : X ⟶ Y) :
    (edgewiseStageQuillenSimplexFunctor C a).map f.hom.left ≫ Y.obj.hom =
      X.obj.hom ≫ (quillenQSimplexDiscreteInclusion C a).map f.hom.right :=
  f.hom.w

end QuillenStageGridLiftTests
end MathlibExtTest.KTheory.Categorical

end
