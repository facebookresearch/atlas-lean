/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ShortComplex.ShortExactSequences
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homological and cohomological δ-functors

Connecting maps are natural transformations on the category of short exact
sequences. Three exactness conditions and a degree-zero endpoint describe
the long exact sequence. Homological connecting maps lower degree by one;
cohomological connecting maps raise degree by one.

## References

* C. Weibel, *An Introduction to Homological Algebra* (1994),
  Definition 2.1.1 and Exercise 2.1.1.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable (A : Type u₁) [Category.{v₁} A] [Preadditive A]
variable (B : Type u₂) [Category.{v₂} B] [Preadditive B]

/-- An additive homological δ-functor, with connecting maps defined on short
exact sequences and a right exact degree-zero endpoint. -/
structure HomologicalDeltaFunctor where
  /-- The functor in each nonnegative degree. -/
  T : ℕ → (A ⥤ B)
  /-- Each degree functor is additive. -/
  additive : ∀ n, (T n).Additive
  /-- The natural connecting map lowers degree by one. -/
  connecting : ∀ n, (ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₃ ⋙ T (n + 1) ⟶
    (ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₁ ⋙ T n
  /-- Exactness at the first object in each degree. -/
  exactLeft : ∀ n (S : ShortComplex.ShortExactSequences A),
    ∃ w : (connecting n).app S ≫ (T n).map S.obj.f = 0,
      (ShortComplex.mk _ _ w).Exact
  /-- Exactness at the middle object in each degree. -/
  exactMiddle : ∀ n (S : ShortComplex.ShortExactSequences A),
    ∃ w : (T n).map S.obj.f ≫ (T n).map S.obj.g = 0,
      (ShortComplex.mk _ _ w).Exact
  /-- Exactness at the last object in each positive degree. -/
  exactRight : ∀ n (S : ShortComplex.ShortExactSequences A),
    ∃ w : (T (n + 1)).map S.obj.g ≫ (connecting n).app S = 0,
      (ShortComplex.mk _ _ w).Exact
  /-- The degree-zero final map is epi. -/
  epiZero : ∀ S : ShortComplex.ShortExactSequences A, Epi ((T 0).map S.obj.g)

/-- An additive cohomological δ-functor, with connecting maps defined on short
exact sequences and a left exact degree-zero endpoint. -/
structure CohomologicalDeltaFunctor where
  /-- The functor in each nonnegative degree. -/
  T : ℕ → (A ⥤ B)
  /-- Each degree functor is additive. -/
  additive : ∀ n, (T n).Additive
  /-- The natural connecting map raises degree by one. -/
  connecting : ∀ n, (ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₃ ⋙ T n ⟶
    (ShortComplex.isShortExact A).ι ⋙ ShortComplex.π₁ ⋙ T (n + 1)
  /-- Exactness at the first object in each positive degree. -/
  exactLeft : ∀ n (S : ShortComplex.ShortExactSequences A),
    ∃ w : (connecting n).app S ≫ (T (n + 1)).map S.obj.f = 0,
      (ShortComplex.mk _ _ w).Exact
  /-- Exactness at the middle object in each degree. -/
  exactMiddle : ∀ n (S : ShortComplex.ShortExactSequences A),
    ∃ w : (T n).map S.obj.f ≫ (T n).map S.obj.g = 0,
      (ShortComplex.mk _ _ w).Exact
  /-- Exactness at the last object in each degree. -/
  exactRight : ∀ n (S : ShortComplex.ShortExactSequences A),
    ∃ w : (T n).map S.obj.g ≫ (connecting n).app S = 0,
      (ShortComplex.mk _ _ w).Exact
  /-- The degree-zero first map is mono. -/
  monoZero : ∀ S : ShortComplex.ShortExactSequences A, Mono ((T 0).map S.obj.f)

namespace HomologicalDeltaFunctor

/-- Additivity is available through typeclass inference in every degree. -/
instance (D : HomologicalDeltaFunctor A B) (n : ℕ) : (D.T n).Additive :=
  D.additive n

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

/-- Additivity is available through typeclass inference in every degree. -/
instance (D : CohomologicalDeltaFunctor A B) (n : ℕ) : (D.T n).Additive :=
  D.additive n

end CohomologicalDeltaFunctor

end CategoryTheory
