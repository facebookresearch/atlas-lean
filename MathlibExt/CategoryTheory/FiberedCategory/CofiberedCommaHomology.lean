/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.Adjunction
public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaAdjunction

/-!
# Homology comparison between a cofibered comma category and its fiber

The cofibered comma/fiber adjunction identifies the homology of `p / s`
with the homology of the strict fiber over `s`.  The forward map is induced
by cocartesian pushforward, and the inverse is induced by the strict-fiber
inclusion.

This comparison is objectwise in `s`; compatibility with base change is a
separate gate.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v vA uA

namespace CategoryTheory.Functor.IsCofibered

variable {S X : Type (max u v)} [Category.{v} S] [Category.{v} X]
  {p : X ⥤ S} [p.IsCofibered]
  (A : Type uA) [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max u v} A] [CategoryWithHomology A]

/-- The right comma category of a cofibered functor and its strict fiber
have canonically isomorphic category homology. -/
noncomputable def costructuredFiberHomologyIso
    (s : S) (R : A) (n : ℕ) :
    (nerve (CostructuredArrow p s)).homology R n ≅
      (nerve (p.Fiber s)).homology R n :=
  categoryHomologyIsoOfAdjunction A
    (costructuredToFiber s) (fiberToCostructuredArrow s)
      (costructuredToFiberAdjunction s) R n

/-- The forward comma/fiber homology comparison is induced by cocartesian
pushforward. -/
@[simp]
theorem costructuredFiberHomologyIso_hom
    (s : S) (R : A) (n : ℕ) :
    (costructuredFiberHomologyIso (p := p) A s R n).hom =
      SSet.homologyMap
        (nerveMap (costructuredToFiber (p := p) s)) R n :=
  rfl

/-- The inverse comma/fiber homology comparison is induced by the strict-
fiber inclusion. -/
@[simp]
theorem costructuredFiberHomologyIso_inv
    (s : S) (R : A) (n : ℕ) :
    (costructuredFiberHomologyIso (p := p) A s R n).inv =
      SSet.homologyMap
        (nerveMap (fiberToCostructuredArrow (p := p) s)) R n :=
  rfl

end CategoryTheory.Functor.IsCofibered

end
