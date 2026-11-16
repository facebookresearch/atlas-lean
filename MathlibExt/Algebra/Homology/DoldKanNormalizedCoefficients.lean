/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import MathlibExt.CategoryTheory.DGSourceMore.HomologyEmbeddingTruncLE

/-!
# Native normalized coefficients of Dold--Kan simplices

Project the actual simplicial coefficient through the native normalized
Moore projection, the Dold--Kan counit and the good-truncation inclusion.
This defines a fixed coefficient in cochain degree -m, in any abelian
coefficient category. There is no independent normalization isomorphism.

References: Dold--Kan; Lurie Higher Algebra Construction1.3.1.13.
The good-truncation bridge retains its pinned Tau Ceti Apache source
notices in HomologyEmbeddingTruncLE.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.Opposite
open scoped Simplicial

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual simplicial module used by native cochain realization. -/
def simplicialModule (K : CochainComplex C ℤ) : SimplicialObject C :=
  Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat)

/-- The complete native chain normalization, before the truncation inclusion. -/
def normalizationMap (K : CochainComplex C ℤ) :
    AlternatingFaceMapComplex.obj (simplicialModule K) ⟶ K.truncLE' ComplexShape.embeddingDownNat :=
  AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (simplicialModule K) ≫
    ((CategoryTheory.Abelian.DoldKan.equivalence (A := C)).counitIso.app
      (K.truncLE' ComplexShape.embeddingDownNat)).hom

/-- The native normalized coefficient of a degree-m simplicial module element. -/
def coefficientMap (K : CochainComplex C ℤ) (m : ℕ) :
    (simplicialModule K) _⦋m⦌ ⟶ K.X (-(m : ℤ)) :=
  (normalizationMap K).f m ≫ K.truncLE'ToX m

/-- The actual coefficients commute with the alternating face differential. -/
theorem coefficientMap_d (K : CochainComplex C ℤ) (m : ℕ) :
    coefficientMap K (m + 1) ≫ K.d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ)) =
      (AlternatingFaceMapComplex.obj (simplicialModule K)).d (m + 1) m ≫ coefficientMap K m := by
  dsimp only [coefficientMap]
  rw [Category.assoc, K.truncLE'ToX_d_succ, ← Category.assoc,
    (normalizationMap K).comm, Category.assoc]

end MathlibExt.Algebra.Homology.DoldKanNormalizedCoefficients
