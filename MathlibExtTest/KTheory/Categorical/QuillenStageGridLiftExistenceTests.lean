/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridLiftExistence
import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctorReindex

/-!
# Tests for all-degree Quillen Stage-grid lift existence

These tests pin the six-cell shell dictionary, adjacent and arbitrary-
interval agreement, low degrees zero through three, and transport of an
obtained witness along faces and degeneracies.  The final results remain
`Nonempty`/essential-surjectivity statements: no chosen global grid,
contractible fiber, simplicial section, realization, or Q/S comparison is
introduced.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenStageGridLiftExistenceTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageGridLiftExistenceTestsWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

section ArbitraryDegree

variable {a : SimplexCategory} (q : QuillenQSimplex C a)
  (P : QuillenSimplexSpanPresentation q)

example : Nonempty { X : QuillenStageGridLift C a // X.q = q } :=
  quillenStageGridLift_exists q

example : (quillenStageGridQProjection C a).EssSurj :=
  quillenStageGridQProjection_essSurj C a

example : edgewiseStageQuillenSimplex P.filtrationStage ≅ q :=
  P.filtrationStageAgreementIso

example (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom (P.filtrationStageShellSpanToQ k l hkl) =
      q.map (homOfLE hkl) :=
  P.filtrationStageShellSpanToQ_mkHom_eq_map k l hkl

example (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    Nonempty (P.filtrationStageShellSpanToQ k l hkl ≅
      P.intervalSpan k l hkl) :=
  P.filtrationStageShellSpan_iso_intervalSpan_nonempty k l hkl

example (i : Fin a.len) :
    P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i) ≅ P.span i :=
  P.filtrationStageShellSpanIsoAdjacent i

end ArbitraryDegree

section LowDegrees

example (q0 : QuillenQSimplex C ⦋0⦌) :
    Nonempty { X : QuillenStageGridLift C ⦋0⦌ // X.q = q0 } :=
  quillenStageGridLift_exists q0

example (q1 : QuillenQSimplex C ⦋1⦌) :
    Nonempty { X : QuillenStageGridLift C ⦋1⦌ // X.q = q1 } :=
  quillenStageGridLift_exists q1

example (q2 : QuillenQSimplex C ⦋2⦌) :
    Nonempty { X : QuillenStageGridLift C ⦋2⦌ // X.q = q2 } :=
  quillenStageGridLift_exists q2

example (q3 : QuillenQSimplex C ⦋3⦌) :
    Nonempty { X : QuillenStageGridLift C ⦋3⦌ // X.q = q3 } :=
  quillenStageGridLift_exists q3

/-- Degree two keeps the source-to-target order of the long shell. -/
example (q2 : QuillenQSimplex C ⦋2⦌)
    (P2 : QuillenSimplexSpanPresentation q2) :
    QuillenQ.mkHom
        (P2.filtrationStageShellSpanToQ
          (0 : Fin 3) (2 : Fin 3) (by decide)) =
      q2.map' 0 1 (by decide) (by decide) ≫
        q2.map' 1 2 (by decide) (by decide) := by
  rw [P2.filtrationStageShellSpanToQ_mkHom_eq_map]
  exact q2.map'_comp 0 1 2

/-- Degree three exercises an arbitrary nonadjacent interval. -/
example (q3 : QuillenQSimplex C ⦋3⦌)
    (P3 : QuillenSimplexSpanPresentation q3) :
    QuillenQ.mkHom
        (P3.filtrationStageShellSpanToQ
          (1 : Fin 4) (3 : Fin 4) (by decide)) =
      q3.map' 1 3 (by decide) (by decide) := by
  simpa only [ComposableArrows.map'] using
    P3.filtrationStageShellSpanToQ_mkHom_eq_map
      (1 : Fin 4) (3 : Fin 4) (by decide)

end LowDegrees

section Reindex

private theorem reindex_witness {a b : SimplexCategory} (alpha : a ⟶ b)
    (q : QuillenQSimplex C b) :
    Nonempty { Y : QuillenStageGridLift C a //
      Y.q = (edgewiseQuillenSimplexReindex (C := C) alpha).obj q } := by
  obtain ⟨⟨X, hX⟩⟩ := quillenStageGridLift_exists q
  refine ⟨⟨(reindexQuillenStageGridLift (C := C) alpha).obj X, ?_⟩⟩
  rw [reindexQuillenStageGridLift_obj_q, hX]

/-- Face transport of an obtained degree-two witness. -/
example (q : QuillenQSimplex C ⦋2⦌) (i : Fin 3) :
    Nonempty { Y : QuillenStageGridLift C ⦋1⦌ //
      Y.q = (edgewiseQuillenSimplexReindex (C := C)
        (SimplexCategory.δ i)).obj q } := by
  exact reindex_witness (C := C) (SimplexCategory.δ i) q

/-- Degeneracy transport retains the collapsed repeated interval witness. -/
example (q : QuillenQSimplex C ⦋1⦌) (i : Fin 2) :
    Nonempty { Y : QuillenStageGridLift C ⦋2⦌ //
      Y.q = (edgewiseQuillenSimplexReindex (C := C)
        (SimplexCategory.σ i)).obj q } := by
  exact reindex_witness (C := C) (SimplexCategory.σ i) q

end Reindex

section TypeZero

variable {C₀ : Type} [Category.{0} C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example (q : QuillenQSimplex C₀ ⦋1⦌) :
    Nonempty { X : QuillenStageGridLift C₀ ⦋1⦌ // X.q = q } :=
  quillenStageGridLift_exists q

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example (q : QuillenQSimplex C₁ ⦋3⦌) :
    Nonempty { X : QuillenStageGridLift C₁ ⦋3⦌ // X.q = q } :=
  quillenStageGridLift_exists q

end TypeOne

end QuillenStageGridLiftExistenceTests
end MathlibExtTest.KTheory.Categorical

end
