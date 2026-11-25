/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Basic
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# The actual chosen finite-action source models

The source models are genuine models on the original Sigma_n functor categories.
Their original I_n/J_n maps, source tractability, underlying weak class,
projective/underlying cofibration inclusions, and actual block-induction
pushout-product compatibility are retained explicitly.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Prod CategoryTheory.MonoidalCategory.ExternalProduct

namespace HomotopicalAlgebra.PositiveLevelModel

/-- The actual block-sum permutation homomorphism, preserving both original ordered finite
alphabets. -/
def blockPermutationHom (p q : ℕ) : Equiv.Perm (Fin p) × Equiv.Perm (Fin q) →* Equiv.Perm
    (Fin (p + q)) :=
  (finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).permCongrHom.toMonoidHom.comp
    { toFun := fun a => Equiv.sumCongr a.1 a.2
      map_one' := by ext x; cases x <;> rfl
      map_mul' := by intro a b; ext x; cases x <;> rfl }

/-- The original Sigma_p times Sigma_q to Sigma_(p+q) block action as its actual functor. -/
def degreeBlockInclusion (p q : ℕ) : degreeActionIndex p × degreeActionIndex q ⥤ degreeActionIndex
    (p + q) where
  obj _ := SingleObj.star (Equiv.Perm (Fin (p + q)))
  map f := blockPermutationHom p q ⟨f.1, f.2⟩
  map_id _ := by
    change blockPermutationHom p q (1, 1) = 1
    exact map_one _
  map_comp f g := by
    let fp : Equiv.Perm (Fin p) := f.1
    let fq : Equiv.Perm (Fin q) := f.2
    let gp : Equiv.Perm (Fin p) := g.1
    let gq : Equiv.Perm (Fin q) := g.2
    change blockPermutationHom p q (gp * fp, gq * fq) =
      blockPermutationHom p q (gp, gq) * blockPermutationHom p q (fp, fq)
    exact map_mul (blockPermutationHom p q) (gp, gq) (fp, fq)

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasColimitsOfSize.{0, 0} C]

/-- The actual finite block induction of the external tensor product of original finite-action
diagrams. -/
def blockInductionTensor (p q : ℕ) :
    degreeActionCategory (C := C) p × degreeActionCategory (C := C) q ⥤ degreeActionCategory
        (C := C) (p + q) :=
  externalProductBifunctor (degreeActionIndex p) (degreeActionIndex q) C ⋙
      (degreeBlockInclusion p q).lan

/-- The actual induced pushout product, with its original source pushout and both original
coefficient arrows. -/
def blockInducedPushoutProduct (p q : ℕ)
    (i : Arrow (degreeActionCategory (C := C) p)) (j : Arrow (degreeActionCategory (C := C) q)) :
    Arrow (degreeActionCategory (C := C) (p + q)) :=
  (degreeBlockInclusion p q).lan.mapArrow.obj
    ((((Functor.curry.obj
        (externalProductBifunctor (degreeActionIndex p) (degreeActionIndex q)
        C)).leibnizPushout).obj
        i).obj j)

variable [baseModel : ModelCategory C]

/-- The exact tractable finite-action source-model choices, before any R-module model is
constructed. -/
structure ChosenActionModels where
  /-- The actual chosen model on the original category of Sigma_n objects. -/
  model (n : ℕ) : ModelCategory (degreeActionCategory (C := C) n)
  /-- The original generating cofibration family of each chosen action model. -/
  I (n : ℕ) : MorphismProperty (degreeActionCategory (C := C) n)
  /-- The original generating trivial cofibration family of each chosen action model. -/
  J (n : ℕ) : MorphismProperty (degreeActionCategory (C := C) n)
  I_smallObject (n : ℕ) : (I n).HasSmallObjectArgument.{w}
  J_smallObject (n : ℕ) : (J n).HasSmallObjectArgument.{w}
  locally_presentable (n : ℕ) : IsLocallyPresentable.{w} (degreeActionCategory (C := C) n)
  I_rlp (n : ℕ) : (I n).rlp = (model n).categoryWithFibrations.fibrations ⊓
    (model n).categoryWithWeakEquivalences.weakEquivalences
  J_rlp (n : ℕ) : (J n).rlp = (model n).categoryWithFibrations.fibrations
  I_cofibrant_sources (n : ℕ) (i : (I n).toSet) :
    (model n).categoryWithCofibrations.cofibrations (initial.to i.1.left)
  J_cofibrant_sources (n : ℕ) (j : (J n).toSet) :
    (model n).categoryWithCofibrations.cofibrations (initial.to j.1.left)
  weak_eq (n : ℕ) : (model n).categoryWithWeakEquivalences.weakEquivalences =
    (weakEquivalences C).functorCategory (degreeActionIndex n)
  projective_cofibrations_le (n : ℕ) :
      ((trivialFibrations C).functorCategory (degreeActionIndex n)).llp ≤
    (model n).categoryWithCofibrations.cofibrations
  underlying_cofibrations_le (n : ℕ) : (model n).categoryWithCofibrations.cofibrations ≤
    (cofibrations C).functorCategory (degreeActionIndex n)
  induced_pushoutProducts (p q : ℕ)
      {A B : degreeActionCategory (C := C) p} {X Y : degreeActionCategory (C := C) q}
      (i : A ⟶ B) (j : X ⟶ Y)
      (hi : (model p).categoryWithCofibrations.cofibrations i)
      (hj : (model q).categoryWithCofibrations.cofibrations j) :
    (model (p + q)).categoryWithCofibrations.cofibrations
        (blockInducedPushoutProduct C p q (Arrow.mk i) (Arrow.mk
        j)).hom

end HomotopicalAlgebra.PositiveLevelModel
