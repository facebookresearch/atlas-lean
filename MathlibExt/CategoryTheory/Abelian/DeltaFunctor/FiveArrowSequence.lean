/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Category
public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Five-arrow sequences of δ-functors

Two adjacent degrees of a δ-functor define a five-arrow sequence.
An isomorphism of δ-functors transports its objects, arrows and exactness.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]

/-- The five arrows in a pair of adjacent degrees of a coefficient delta functor. -/
def fiveArrowSequence (T : CohomologicalDeltaFunctor A B)
    (S : ShortComplex.ShortExactSequences A) (n : ℕ) : ComposableArrows B 5 :=
  ComposableArrows.mk₅ ((T.T n).map S.obj.f) ((T.T n).map S.obj.g) ((T.connecting n).app S)
    ((T.T (n + 1)).map S.obj.f) ((T.T (n + 1)).map S.obj.g)

/-- A delta isomorphism identifies every object and arrow
of its five-arrow long-exact windows. -/
def fiveArrowSequenceIso {T T' : CohomologicalDeltaFunctor A B} (e : T ≅ T')
    (S : ShortComplex.ShortExactSequences A) (n : ℕ) :
    fiveArrowSequence T S n ≅ fiveArrowSequence T' S n :=
  ComposableArrows.isoMk₅
    (((evaluation A B n).mapIso e).app S.obj.X₁)
    (((evaluation A B n).mapIso e).app S.obj.X₂)
    (((evaluation A B n).mapIso e).app S.obj.X₃)
    (((evaluation A B (n + 1)).mapIso e).app S.obj.X₁)
    (((evaluation A B (n + 1)).mapIso e).app S.obj.X₂)
    (((evaluation A B (n + 1)).mapIso e).app S.obj.X₃)
    ((Hom.app e.hom n).naturality S.obj.f)
    ((Hom.app e.hom n).naturality S.obj.g)
    (DeltaFunctor.System.comm e.hom.hom n S)
    ((Hom.app e.hom (n + 1)).naturality S.obj.f)
    ((Hom.app e.hom (n + 1)).naturality S.obj.g)

/-- Exactness of the five-arrow window is transported by its
same delta comparison, with no additional comparison square. -/
theorem fiveArrowSequence_exact_iff {T T' : CohomologicalDeltaFunctor A B} (e : T ≅ T')
    (S : ShortComplex.ShortExactSequences A) (n : ℕ) :
    (fiveArrowSequence T S n).Exact ↔ (fiveArrowSequence T' S n).Exact :=
  ComposableArrows.exact_iff_of_iso (fiveArrowSequenceIso e S n)

end CategoryTheory.CohomologicalDeltaFunctor
