/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Cartesian pushout-product and pullback-Hom axioms

This file defines property-level forms of the pushout-product and pullback-Hom
conditions and proves their equivalence in a closed monoidal category. For a
cartesian closed model category, it packages the three pushout-product clauses
and the corresponding three pullback-Hom clauses as equivalent propositions.

The monoidal unit axiom is independent and is not included here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [MonoidalCategory C] [MonoidalClosed C]

/-- The pushout-product of a P-map and a Q-map is an R-map. -/
def PushoutProductLe (P Q R : MorphismProperty C) : Prop :=
  ∀ ⦃A B K L : C⦄ (i : A ⟶ B) (j : K ⟶ L),
    P i → Q j → R ((Arrow.mk i □ Arrow.mk j).hom)

/-- The pullback-Hom of a P-map against a Q-map is an R-map. -/
def PullbackHomLe (P Q R : MorphismProperty C) : Prop :=
  ∀ ⦃A B X Y : C⦄ (i : A ⟶ B) (p : X ⟶ Y),
    P i → Q p →
      R (((Opposite.op (Arrow.mk i)) ⋔ Arrow.mk p).hom)

/-- The pushout-product condition against a left orthogonal is equivalent to
the corresponding pullback-Hom condition against a right orthogonal. -/
theorem pushoutProduct_le_llp_iff_pullbackHom_le_rlp
    (P Q R : MorphismProperty C) :
    PushoutProductLe P Q R.llp ↔ PullbackHomLe P R Q.rlp := by
  constructor
  · intro h A B X Y i p hi hp K L j hj
    apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff.mp
    exact h i j hi hj p hp
  · intro h A B K L i j hi hj X Y p hp
    apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff.mpr
    exact h i p hi hp j hj

end CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

open CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [ModelCategory C]

/-- The three cartesian pushout-product clauses for a model category. -/
def CartesianPushoutProductAxiom : Prop :=
  PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C) ∧
    PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C) ∧
    PushoutProductLe (cofibrations C) (trivialCofibrations C)
      (trivialCofibrations C)

/-- The three pullback-Hom clauses corresponding to the cartesian
pushout-product axioms. -/
def CartesianPullbackHomAxiom : Prop :=
  PullbackHomLe (cofibrations C) (trivialFibrations C)
      (trivialFibrations C) ∧
    PullbackHomLe (trivialCofibrations C) (fibrations C)
      (trivialFibrations C) ∧
    PullbackHomLe (cofibrations C) (fibrations C) (fibrations C)

/-- In a cartesian closed model category, the three pushout-product clauses
are equivalent to the three pullback-Hom clauses. -/
theorem cartesianPushoutProductAxiom_iff_pullbackHomAxiom :
    CartesianPushoutProductAxiom (C := C) ↔
      CartesianPullbackHomAxiom (C := C) := by
  have h₁ :
      PushoutProductLe (cofibrations C) (cofibrations C)
          (cofibrations C) ↔
        PullbackHomLe (cofibrations C) (trivialFibrations C)
          (trivialFibrations C) := by
    simpa only [trivialFibrations_llp, cofibrations_rlp] using
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
        (cofibrations C) (cofibrations C) (trivialFibrations C))
  have h₂ :
      PushoutProductLe (trivialCofibrations C) (cofibrations C)
          (trivialCofibrations C) ↔
        PullbackHomLe (trivialCofibrations C) (fibrations C)
          (trivialFibrations C) := by
    simpa only [fibrations_llp, cofibrations_rlp] using
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
        (trivialCofibrations C) (cofibrations C) (fibrations C))
  have h₃ :
      PushoutProductLe (cofibrations C) (trivialCofibrations C)
          (trivialCofibrations C) ↔
        PullbackHomLe (cofibrations C) (fibrations C)
          (fibrations C) := by
    simpa only [fibrations_llp, trivialCofibrations_rlp] using
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
        (cofibrations C) (trivialCofibrations C) (fibrations C))
  constructor
  · rintro ⟨hcof, hleft, hright⟩
    exact ⟨h₁.mp hcof, h₂.mp hleft, h₃.mp hright⟩
  · rintro ⟨hcof, hleft, hright⟩
    exact ⟨h₁.mpr hcof, h₂.mpr hleft, h₃.mpr hright⟩

end HomotopicalAlgebra
