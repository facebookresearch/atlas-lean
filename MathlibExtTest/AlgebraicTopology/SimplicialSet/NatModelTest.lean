/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NatModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.Countability

/-!
# Using natural-number models

Countability supplies encodings for arbitrary simplicial sets. The resulting
natural isomorphism retains both inverse laws and all operator equations.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.NatModelTest

/-- Every countable simplicial set is represented by an actual coded model. -/
theorem exists_model (X : SSet.{u}) [Countable X.N] :
    ∃ M : SSet.NatModel, Countable (M.toSSet.{u}).N ∧
      Nonempty (M.toSSet.{u} ≅ X) := by
  choose e he using fun x ↦ @Countable.exists_injective_nat (X.obj x)
    (@SSet.countable_obj_of_countable_N X inferInstance x)
  exact ⟨SSet.NatModel.of X e he, (SSet.NatModel.of X e he).countable_N_toSSet,
    ⟨SSet.NatModel.isoOf X e he⟩⟩

variable (X : SSet.{u}) (e : ∀ x : SimplexCategoryᵒᵖ, X.obj x → ℕ)
  (he : ∀ x, Function.Injective (e x))

/-- Decoding and encoding recover the original coded simplex. -/
theorem coded_roundtrip (x : SimplexCategoryᵒᵖ)
    (a : (SSet.NatModel.of X e he).toSSet.{u}.obj x) :
    (SSet.NatModel.ofEquiv X e he x).symm (SSet.NatModel.ofEquiv X e he x a) = a :=
  (SSet.NatModel.ofEquiv X e he x).symm_apply_apply a

/-- Encoding and decoding recover the original simplex. -/
theorem original_roundtrip (x : SimplexCategoryᵒᵖ) (a : X.obj x) :
    SSet.NatModel.ofEquiv X e he x ((SSet.NatModel.ofEquiv X e he x).symm a) = a :=
  (SSet.NatModel.ofEquiv X e he x).apply_symm_apply a

/-- The recoding isomorphism commutes with every simplicial operator. -/
theorem hom_naturality {x y : SimplexCategoryᵒᵖ} (φ : x ⟶ y) :
    (SSet.NatModel.of X e he).toSSet.{u}.map φ ≫ (SSet.NatModel.isoOf X e he).hom.app y =
      (SSet.NatModel.isoOf X e he).hom.app x ≫ X.map φ :=
  (SSet.NatModel.isoOf X e he).hom.naturality φ

/-- The inverse recoding isomorphism also commutes with every operator. -/
theorem inv_naturality {x y : SimplexCategoryᵒᵖ} (φ : x ⟶ y) :
    X.map φ ≫ (SSet.NatModel.isoOf X e he).inv.app y =
      (SSet.NatModel.isoOf X e he).inv.app x ≫ (SSet.NatModel.of X e he).toSSet.{u}.map φ :=
  (SSet.NatModel.isoOf X e he).inv.naturality φ

end MathlibExtTest.AlgebraicTopology.SimplicialSet.NatModelTest
