/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import MathlibExt.CategoryTheory.Functor.SmallIndex

/-!
# Local presentability on the original ordinary functor category

The native presheaf theorem applies to the double opposite of an actual
working-small index. Its equivalence with that index, followed by the actual
small-model equivalence of the original index, returns local presentability
on the original functor category at the supplied cardinal.

The index objects, index morphisms, coefficient objects, coefficient morphisms
and working universe are independent. No bound on the number of index objects
relative to the presentability cardinal is required. Pullbacks are precisely
the additional coefficient limit hypothesis in the native presheaf theorem.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uD vD uM vM

namespace CategoryTheory.Functor

open Limits

variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]

/-- The actual small-index equivalence gives local presentability on the
original diagram category at the same supplied regular cardinal. -/
theorem EssentialIndexData.isCardinalLocallyPresentable
    (s : EssentialIndexData.{w} D M) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ := by
  let : SmallCategory s.index := s.indexCategory
  let : IsCardinalLocallyPresentable (s.indexᵒᵖᵒᵖ ⥤ M) κ := inferInstance
  let : IsCardinalLocallyPresentable (s.index ⥤ M) κ :=
    ((opOpEquivalence s.index).congrLeft (E := M)).isCardinalLocallyPresentable κ
  exact (s.equivalence.congrLeft (E := M)).symm.isCardinalLocallyPresentable κ

/-- The simple size contract uses its genuine small-model equivalence;
neither the original category nor the supplied cardinal is replaced. -/
theorem SmallIndexData.isCardinalLocallyPresentable
    (s : SmallIndexData.{w} D M) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ :=
  s.toEssential.isCardinalLocallyPresentable κ

/-- The essentially-small entry uses the actual native representative index
and returns local presentability on the original functor category. -/
theorem isCardinalLocallyPresentable_of_essentiallySmall
    [EssentiallySmall.{w} D]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable M κ] [HasPullbacks M] :
    IsCardinalLocallyPresentable (D ⥤ M) κ :=
  (EssentialIndexData.ofEssentiallySmall (D := D) (M := M)).isCardinalLocallyPresentable κ

end CategoryTheory.Functor
