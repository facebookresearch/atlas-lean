/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer
import Batteries.Tactic.Lint

/-!
# Clients of the full original right transfer

These clients use arbitrary categories and original adjoints, with independent
object and morphism universes. Both complete factorizations, the full original
free generating families and the actual source ranks remain observable.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uC vC uD vD

open CategoryTheory Limits MorphismProperty
open HomotopicalAlgebra

namespace HomotopicalAlgebra.RightTransfer.Clients

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D]
  [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (hSourceI : CategoryTheory.SmallObject.UniformRelativeSourceSmallness.{w} (I.strictMap L))
  (hSourceJ : CategoryTheory.SmallObject.UniformRelativeSourceSmallness.{w} (J.strictMap L))
  (hAcyclicity : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(J.strictMap L).IsCardinalForSmallObjectArgument κ], (J.strictMap L).rlp.llp ≤ weakClass R)

/-- The original complete model, without any target model supplied to this client. -/
def transferred : FullModelTransfer L R I J hSourceI hSourceJ :=
  fullModelTransfer L R adj I J hI hJ hSourceI hSourceJ hAcyclicity

/-- Both actual free families and every source bound are retained by the common-rank output. -/
theorem originalGeneration :
    let t := transferred L R adj I J hI hJ hSourceI hSourceJ hAcyclicity
    letI := t.generationCardinal.regular
    letI := t.generationCardinal.orderBot
    letI := t.model
    t.generation.I = I.strictMap L ∧ t.generation.J = J.strictMap L ∧
      (∀ i : (I.strictMap L).toSet,
        CategoryTheory.SmallObject.UniformRelativeSourceSmallness.sourceBound hSourceI i <
          t.generationCardinal.cardinal) ∧
      (∀ j : (J.strictMap L).toSet,
        CategoryTheory.SmallObject.UniformRelativeSourceSmallness.sourceBound hSourceJ j <
          t.generationCardinal.cardinal) := by
  let t := transferred L R adj I J hI hJ hSourceI hSourceJ hAcyclicity
  exact ⟨t.generation_I, t.generation_J, t.generationCardinal.sourceP_bounds,
    t.generationCardinal.sourceQ_bounds⟩

/-- A whole original target arrow has both complete factorizations in the exact output classes. -/
theorem originalFactors (f : Arrow D) :
    let t := transferred L R adj I J hI hJ hSourceI hSourceJ hAcyclicity
    let a := t.cofibrantFactorizationData
    let b := t.fibrantFactorizationData
    a.i.app f ≫ a.p.app f = f.hom ∧ b.i.app f ≫ b.p.app f = f.hom ∧
      cofibrationClass R (a.i.app f) ∧ trivialFibrationClass R (a.p.app f) ∧
      trivialCofibrationClass R (b.i.app f) ∧ fibrationClass R (b.p.app f) := by
  let t := transferred L R adj I J hI hJ hSourceI hSourceJ hAcyclicity
  exact ⟨t.cofibrantFactorizationData.fac_app, t.fibrantFactorizationData.fac_app,
    t.cofibrantFactorization_left f, t.cofibrantFactorization_right f,
    t.fibrantFactorization_left f, t.fibrantFactorization_right f⟩

/-- Every entire original square retains naturality of both actual factorization pairs. -/
theorem originalSquare {f g : Arrow D} (φ : f ⟶ g) :
    let t := transferred L R adj I J hI hJ hSourceI hSourceJ hAcyclicity
    let a := t.cofibrantFactorizationData
    let b := t.fibrantFactorizationData
    (φ.left ≫ a.i.app g = a.i.app f ≫ a.Z.map φ) ∧
      (a.p.app f ≫ φ.right = a.Z.map φ ≫ a.p.app g) ∧
      (φ.left ≫ b.i.app g = b.i.app f ≫ b.Z.map φ) ∧
      (b.p.app f ≫ φ.right = b.Z.map φ ≫ b.p.app g) := by
  let t := transferred L R adj I J hI hJ hSourceI hSourceJ hAcyclicity
  exact ⟨t.cofibrantFactorizationData.i.naturality φ,
    (t.cofibrantFactorizationData.p.naturality φ).symm,
    t.fibrantFactorizationData.i.naturality φ,
    (t.fibrantFactorizationData.p.naturality φ).symm⟩

end HomotopicalAlgebra.RightTransfer.Clients

#print axioms HomotopicalAlgebra.RightTransfer.generationCardinal
#print axioms HomotopicalAlgebra.RightTransfer.fullModelTransfer
#print axioms HomotopicalAlgebra.RightTransfer.FullModelTransfer.cofibrantFactorizationData
#print axioms HomotopicalAlgebra.RightTransfer.FullModelTransfer.fibrantFactorizationData
#print axioms HomotopicalAlgebra.RightTransfer.Clients.originalGeneration
#print axioms HomotopicalAlgebra.RightTransfer.Clients.originalFactors
#print axioms HomotopicalAlgebra.RightTransfer.Clients.originalSquare

#lint only unusedArguments in MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer
