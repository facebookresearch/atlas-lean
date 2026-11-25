/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.KTheory.Exact.Quillen.NatIso
public import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalence invariance for the Quillen Q-construction

For an equivalence `e : C ≌ D` with additive exact functor and inverse,
`QuillenQ.map` in both directions assembles into
`QuillenQ.equivOfEquivalence` via `CategoryTheory.Equivalence.mk`.
No K-group, nerve, realization, Q/S comparison, S-construction, spectrum,
or BGT content.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- Quillen Q-categories are invariant under exact equivalence. -/
noncomputable def QuillenQ.equivOfEquivalence (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    [e.functor.IsExact] [e.inverse.IsExact] :
    QuillenQ C ≌ QuillenQ D :=
  CategoryTheory.Equivalence.mk
    (QuillenQ.map e.functor)
    (QuillenQ.map e.inverse)
    ((eqToIso QuillenQ.map_id).symm ≪≫
      QuillenQ.mapNatIso (𝟭 C) (e.functor ⋙ e.inverse) e.unitIso ≪≫
      eqToIso (QuillenQ.map_comp e.functor e.inverse))
    ((eqToIso (QuillenQ.map_comp e.inverse e.functor)).symm ≪≫
      QuillenQ.mapNatIso (e.inverse ⋙ e.functor) (𝟭 D) e.counitIso ≪≫
      eqToIso QuillenQ.map_id)

/-- Forward projection of the induced equivalence. -/
@[simp]
theorem QuillenQ.equivOfEquivalence_functor (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    [e.functor.IsExact] [e.inverse.IsExact] :
    (QuillenQ.equivOfEquivalence e).functor = QuillenQ.map e.functor :=
  rfl

/-- Inverse projection of the induced equivalence. -/
@[simp]
theorem QuillenQ.equivOfEquivalence_inverse (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    [e.functor.IsExact] [e.inverse.IsExact] :
    (QuillenQ.equivOfEquivalence e).inverse = QuillenQ.map e.inverse :=
  rfl

end AlgebraicKTheory
