/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellNormalized
import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctorReindex

/-!
# Tests for endpoint-normalized Quillen Stage-shell representatives

These tests pin the unchanged apex, the source-first and target-second leg
transports, their admissibility, and the quotient computation in degrees
zero, one, and two.  The generic reindexing example covers face and degeneracy
maps through the already established normalized-class formula.

No reverse grid construction, lift existence, contractibility, realization,
or Q/S comparison is tested or claimed here.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenSpanFlagStageShellNormalizedTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenSpanFlagStageShellNormalizedTestsWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenSpan (edgewiseStageVertex A k) (edgewiseStageVertex A l) :=
  edgewiseStageShellSpanNormalized A k l hkl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized A k l hkl).apex =
      (edgewiseStageShellPacket A k l hkl).span.apex :=
  edgewiseStageShellSpanNormalized_apex A k l hkl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized A k l hkl).l =
      (edgewiseStageShellPacket A k l hkl).span.l ≫
        (eqToIso (edgewiseStageShellSourceEqVertex A k l hkl)).hom :=
  edgewiseStageShellSpanNormalized_l A k l hkl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized A k l hkl).r =
      (edgewiseStageShellPacket A k l hkl).span.r ≫
        (eqToIso (edgewiseStageShellTargetEqVertex A k l hkl)).hom :=
  edgewiseStageShellSpanNormalized_r A k l hkl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    IsAdmissibleEpi (edgewiseStageShellSpanNormalized A k l hkl).l :=
  (edgewiseStageShellSpanNormalized A k l hkl).wl

example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    IsAdmissibleMono (edgewiseStageShellSpanNormalized A k l hkl).r :=
  (edgewiseStageShellSpanNormalized A k l hkl).wr

/-- Every ordered interval has the requested representative computation. -/
example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom (edgewiseStageShellSpanNormalized A k l hkl) =
      edgewiseStageShellClassNormalized A k l hkl :=
  edgewiseStageShellSpanNormalized_mkHom A k l hkl

/-- A repeated shell represents the identity. -/
example {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    QuillenQ.mkHom (edgewiseStageShellSpanNormalized A k k le_rfl) =
      𝟙 (⟨edgewiseStageVertex A k⟩ : QuillenQ C) := by
  rw [edgewiseStageShellSpanNormalized_mkHom,
    edgewiseStageShellClassNormalized_refl]

/-- Degree zero has only the repeated normalized shell. -/
example (A : Stage C (edgewiseQ.obj ⦋0⦌).len) :
    QuillenQ.mkHom
        (edgewiseStageShellSpanNormalized A (0 : Fin 1) 0 (by decide)) =
      𝟙 (⟨edgewiseStageVertex A (0 : Fin 1)⟩ : QuillenQ C) := by
  rw [edgewiseStageShellSpanNormalized_mkHom,
    edgewiseStageShellClassNormalized_refl]

/-- Degree one has the forward shell from vertex zero to vertex one. -/
example (A : Stage C (edgewiseQ.obj ⦋1⦌).len) :
    QuillenQ.mkHom
        (edgewiseStageShellSpanNormalized A
          (0 : Fin 2) (1 : Fin 2) (by decide)) =
      edgewiseStageShellClassNormalized A
        (0 : Fin 2) (1 : Fin 2) (by decide) :=
  edgewiseStageShellSpanNormalized_mkHom A 0 1 (by decide)

/-- In degree two, the long normalized representative has the quotient class
of the two short shells in source-to-target order. -/
example (A : Stage C (edgewiseQ.obj ⦋2⦌).len) :
    QuillenQ.mkHom
        (edgewiseStageShellSpanNormalized A
          (0 : Fin 3) (2 : Fin 3) (by decide)) =
      edgewiseStageShellClassNormalized A
          (0 : Fin 3) (1 : Fin 3) (by decide) ≫
        edgewiseStageShellClassNormalized A
          (1 : Fin 3) (2 : Fin 3) (by decide) := by
  rw [edgewiseStageShellSpanNormalized_mkHom]
  exact (edgewiseStageShellClassNormalized_comp A (by decide) (by decide)).symm

/-- The quotient class of the normalized representative obeys every outer
simplex reindexing formula, including faces and degeneracies. -/
example {a b : SimplexCategory} (alpha : a ⟶ b)
    (A : Stage C (edgewiseQ.obj b).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom
        (edgewiseStageShellSpanNormalized
          ((reindexStage (C := C) (edgewiseQ.map alpha)).obj A)
          k l hkl) =
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
          (edgewiseStageVertex_reindex alpha A k)) ≫
        edgewiseStageShellClassNormalized A
          (alpha.toOrderHom k) (alpha.toOrderHom l)
          (alpha.toOrderHom.monotone hkl) ≫
        eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
          (edgewiseStageVertex_reindex alpha A l)).symm := by
  exact (edgewiseStageShellSpanNormalized_mkHom _ _ _ _).trans
    (edgewiseStageShellClassNormalized_reindex alpha A k l hkl)

section TypeZero

variable {C₀ : Type} [Category.{0} C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

local instance typeZeroWaldhausenC₀ : WaldhausenCategoryWithoutGluing C₀ :=
  ExactCategory.waldhausenCategory C₀

example (A : Stage C₀ (edgewiseQ.obj ⦋1⦌).len) :
    QuillenSpan (edgewiseStageVertex A (0 : Fin 2))
      (edgewiseStageVertex A (1 : Fin 2)) :=
  edgewiseStageShellSpanNormalized A 0 1 (by decide)

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

local instance typeOneWaldhausenC₁ : WaldhausenCategoryWithoutGluing C₁ :=
  ExactCategory.waldhausenCategory C₁

example (A : Stage C₁ (edgewiseQ.obj ⦋2⦌).len) :
    QuillenQ.mkHom
        (edgewiseStageShellSpanNormalized A
          (0 : Fin 3) (2 : Fin 3) (by decide)) =
      edgewiseStageShellClassNormalized A 0 2 (by decide) :=
  edgewiseStageShellSpanNormalized_mkHom A 0 2 (by decide)

end TypeOne

end QuillenSpanFlagStageShellNormalizedTests
end MathlibExtTest.KTheory.Categorical

end
