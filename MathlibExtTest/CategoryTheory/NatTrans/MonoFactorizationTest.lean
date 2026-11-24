/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NatTrans.MonoFactorization

/-!
# Tests for natural-transformation factorization through monomorphisms
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w v u

open CategoryTheory

namespace CategoryTheory.NatTrans.MonoFactorizationTest

variable {C : Type u} [Category.{v} C]

/-- The total-elements injection retains the full dependent element. -/
example {F G : C ⥤ Type w} (m : F ⟶ G) [Mono m]
    (x y : F.Elements) (h : m.mapElements.obj x = m.mapElements.obj y) :
    x = y :=
  m.mapElements_obj_injective h

/-- Pointwise witnesses yield one unique natural factor with the original
whole transformation equation. -/
theorem pointwise_factor_is_unique {A B D : C ⥤ Type w}
    (f : A ⟶ D) (m : B ⟶ D) [Mono m]
    (h : ∀ (X : C) (x : A.obj X), ∃ y : B.obj X,
      m.app X y = f.app X x) :
    ∃! l : A ⟶ B, l ≫ m = f := by
  let hrange := Subfunctor.range_le_range_of_app f m h
  refine ⟨NatTrans.factorThruMono f m hrange,
    NatTrans.factorThruMono_comp f m hrange, ?_⟩
  intro l hl
  exact NatTrans.factorThruMono_unique f m hrange l hl

/-- The public cardinal bridge consumes the same total-elements injection. -/
example {F G : C ⥤ Type w} (m : F ⟶ G) [Mono m] :
    Cardinal.mk F.Elements ≤ Cardinal.mk G.Elements :=
  Functor.mk_elements_le_of_mono m

/-- The dual total-elements cardinal bridge retains the original index. -/
example {F G : C ⥤ Type w} (e : F ⟶ G) [Epi e] :
    Cardinal.mk G.Elements ≤ Cardinal.mk F.Elements :=
  Functor.mk_elements_le_of_epi e

/-- The native range retains every original index while never increasing the
total number of elements. -/
example {F G : C ⥤ Type w} (f : F ⟶ G) :
    Cardinal.mk (Subfunctor.range f).toFunctor.Elements ≤ Cardinal.mk F.Elements :=
  Subfunctor.mk_elements_range_le f

end CategoryTheory.NatTrans.MonoFactorizationTest
