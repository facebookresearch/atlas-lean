/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctor

/-!
# Extracted Quillen simplex tests for edgewise Stage shells

These tests pin the literal cross vertices, endpoint normalization,
all-interval maps, source-to-target factor order, and functoriality under
pointwise weak Stage morphisms.  They make no outer-reindexing, lift-category,
contractibility, realization, or all-degree Q/S comparison claim.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenSpanFlagStageShellFunctorTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenSpanFlagStageShellFunctorTestsWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example (a : SimplexCategory) (k : Fin (a.len + 1)) :
    edgewiseLeftIndex a k ≤ edgewiseRightIndex a k :=
  edgewiseStageVertex_le a k

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    edgewiseStageVertex A k =
      A.obj.obj (interval (edgewiseLeftIndex a k)
        (edgewiseRightIndex a k) (edgewiseStageVertex_le a k)) :=
  rfl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket A k l hkl).source =
      edgewiseStageVertex A k :=
  edgewiseStageShellSourceEqVertex A k l hkl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket A k l hkl).target =
      edgewiseStageVertex A l :=
  edgewiseStageShellTargetEqVertex A k l hkl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized A k l hkl =
      (QuillenQ.underlyingIso
        (eqToIso (edgewiseStageShellSourceEqVertex A k l hkl))).inv ≫
      (edgewiseStageShellPacket A k l hkl).quillenHom ≫
      (QuillenQ.underlyingIso
        (eqToIso (edgewiseStageShellTargetEqVertex A k l hkl))).hom :=
  rfl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    edgewiseStageShellClassNormalized A k k le_rfl = 𝟙 _ :=
  edgewiseStageShellClassNormalized_refl A k

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    edgewiseStageShellClassNormalized A k l hkl ≫
        edgewiseStageShellClassNormalized A l r hlr =
      edgewiseStageShellClassNormalized A k r (hkl.trans hlr) :=
  edgewiseStageShellClassNormalized_comp A hkl hlr

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageQuillenSimplex A).obj k =
      ⟨edgewiseStageVertex A k⟩ :=
  edgewiseStageQuillenSimplex_obj A k

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    (edgewiseStageQuillenSimplex A).map (homOfLE hkl) =
      edgewiseStageShellClassNormalized A k l hkl :=
  edgewiseStageQuillenSimplex_map_homOfLE A hkl

/-- In degree zero the unique endomorphism is the normalized repeated shell
and hence the identity. -/
example (A : Stage C (edgewiseQ.obj ⦋0⦌).len) :
    (edgewiseStageQuillenSimplex A).map
        (homOfLE (show (0 : Fin 1) ≤ 0 by decide)) = 𝟙 _ := by
  rw [edgewiseStageQuillenSimplex_map_homOfLE,
    edgewiseStageShellClassNormalized_refl]
  change 𝟙 (⟨edgewiseStageVertex A 0⟩ : QuillenQ C) = 𝟙 _
  rfl

/-- In degree one the sole nonidentity arrow retains source-first order. -/
example (A : Stage C (edgewiseQ.obj ⦋1⦌).len) :
    (edgewiseStageQuillenSimplex A).map
        (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) =
      edgewiseStageShellClassNormalized A
        (0 : Fin 2) (1 : Fin 2) (by decide) :=
  edgewiseStageQuillenSimplex_map_homOfLE A (by decide)

/-- In degree two the long shell is the ordered composite of the two short
shells. -/
example (A : Stage C (edgewiseQ.obj ⦋2⦌).len) :
    (edgewiseStageQuillenSimplex A).map
        (homOfLE (show (0 : Fin 3) ≤ 2 by decide)) =
      (edgewiseStageQuillenSimplex A).map
          (homOfLE (show (0 : Fin 3) ≤ 1 by decide)) ≫
        (edgewiseStageQuillenSimplex A).map
          (homOfLE (show (1 : Fin 3) ≤ 2 by decide)) := by
  exact (edgewiseStageQuillenSimplex A).map_comp
    (homOfLE (show (0 : Fin 3) ≤ 1 by decide))
    (homOfLE (show (1 : Fin 3) ≤ 2 by decide))

section WeakMorphisms

variable {a : SimplexCategory}
  {A B D : StageWeakCategory C (edgewiseQ.obj a).len}

example (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (edgewiseStageVertexIso f k).hom =
      f.hom.hom.app
        (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
          (edgewiseStageVertex_le a k)) :=
  edgewiseStageVertexIso_hom f k

example (f : A ⟶ B) (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized A.obj k l hkl ≫
        (QuillenQ.underlyingIso (edgewiseStageVertexIso f l)).hom =
      (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom ≫
        edgewiseStageShellClassNormalized B.obj k l hkl :=
  edgewiseStageShellClassNormalized_naturality f k l hkl

example (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (edgewiseStageQuillenSimplexMap f).app k =
      (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom :=
  edgewiseStageQuillenSimplexMap_app f k

example :
    (edgewiseStageQuillenSimplexFunctor C a).obj A =
      edgewiseStageQuillenSimplex A.obj :=
  edgewiseStageQuillenSimplexFunctor_obj C a A

example (f : A ⟶ B) :
    (edgewiseStageQuillenSimplexFunctor C a).map f =
      edgewiseStageQuillenSimplexMap f :=
  edgewiseStageQuillenSimplexFunctor_map C a f

example :
    (edgewiseStageQuillenSimplexFunctor C a).map (𝟙 A) = 𝟙 _ := by
  exact (edgewiseStageQuillenSimplexFunctor C a).map_id A

example (f : A ⟶ B) (g : B ⟶ D) :
    (edgewiseStageQuillenSimplexFunctor C a).map (f ≫ g) =
      (edgewiseStageQuillenSimplexFunctor C a).map f ≫
        (edgewiseStageQuillenSimplexFunctor C a).map g := by
  exact (edgewiseStageQuillenSimplexFunctor C a).map_comp f g

end WeakMorphisms

end QuillenSpanFlagStageShellFunctorTests
end MathlibExtTest.KTheory.Categorical

end
