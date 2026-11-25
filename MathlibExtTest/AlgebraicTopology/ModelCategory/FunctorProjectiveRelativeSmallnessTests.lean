/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.RelativeSmallness
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Actual produced base witness and original conventional projective fields -/
set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open CategoryTheory.SmallObject HomotopicalAlgebra.FunctorProjective

namespace MathlibExtTest.FunctorProjectiveRelativeSmallness

variable {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {D : Type uD} [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D]
  {I J : MorphismProperty M}

example {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData M κ) :
    RelativeGenerationWitness.{w} d.I d.J := RelativeGenerationWitness.ofData d

example {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData M κ) :
    (RelativeGenerationWitness.ofData d).cardinal = κ :=
  RelativeGenerationWitness.ofData_cardinal d

example (d : RelativeGenerationWitness.{w} I J) : ModelCategory (D ⥤ M) :=
  d.modelCategory

example (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    CofibrantGenerationData (D ⥤ M) d.cardinal :=
  d.generationData

example (d : RelativeGenerationWitness.{w} I J) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) :=
  d.cofibrantFactorizationData

example (d : RelativeGenerationWitness.{w} I J) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  d.fibrantFactorizationData

example (d : RelativeGenerationWitness.{w} I J) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
      fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
      trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
      cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  d.five_classes

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    ((d.cofibrantFactorizationData).i.app f).app x ≫
      ((d.cofibrantFactorizationData).p.app f).app x = f.hom.app x :=
  d.cofibrantFactorizationData_fac_app f x

example (d : RelativeGenerationWitness.{w} I J) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    IsWeakFactorizationSystem (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) ∧
      IsWeakFactorizationSystem (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact ⟨inferInstance, inferInstance⟩

example (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.generationData (D := D)).I = FunctorProjective.freeGenerators d.baseData I :=
  d.generationData_I

example (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.generationData (D := D)).I.IsCardinalForSmallObjectArgument d.cardinal ∧
      (d.generationData (D := D)).J.IsCardinalForSmallObjectArgument d.cardinal :=
  d.generationData_eligible

example (d : RelativeGenerationWitness.{w} I J) {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    φ.left ≫ (d.cofibrantFactorizationData).i.app g =
      (d.cofibrantFactorizationData).i.app f ≫ (d.cofibrantFactorizationData).Z.map φ := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.cofibrantFactorizationData).i.naturality φ

example (d : RelativeGenerationWitness.{w} I J)
    {f g k : Arrow (D ⥤ M)} (φ : f ⟶ g) (ψ : g ⟶ k) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.fibrantFactorizationData).Z.map (φ ≫ ψ) =
      (d.fibrantFactorizationData).Z.map φ ≫ (d.fibrantFactorizationData).Z.map ψ := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.fibrantFactorizationData).Z.map_comp φ ψ

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.cofibrantFactorizationData).Z.map (𝟙 f) = 𝟙 ((d.cofibrantFactorizationData).Z.obj f) := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.cofibrantFactorizationData).Z.map_id f

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.fibrantFactorizationData).i.app f ≫ (d.fibrantFactorizationData).p.app f = f.hom := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.fibrantFactorizationData).fac_app

example (d : RelativeGenerationWitness.{w} I J) {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.fibrantFactorizationData).Z.map φ ≫ (d.fibrantFactorizationData).p.app g =
      (d.fibrantFactorizationData).p.app f ≫ φ.right := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.fibrantFactorizationData).p.naturality φ

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    cofibrations (D ⥤ M) ((d.cofibrantFactorizationData).i.app f) := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.cofibrantFactorizationData).hi f

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    trivialFibrations (D ⥤ M) ((d.cofibrantFactorizationData).p.app f) := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.cofibrantFactorizationData).hp f

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    trivialCofibrations (D ⥤ M) ((d.fibrantFactorizationData).i.app f) := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.fibrantFactorizationData).hi f

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (D ⥤ M)) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    fibrations (D ⥤ M) ((d.fibrantFactorizationData).p.app f) := by
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact (d.fibrantFactorizationData).hp f

section ConventionalInput

variable [I.IsSmall.{w}] [J.IsSmall.{w}] [LocallySmall.{w} M] [HasCoproducts.{w} M]
  (hI : UniformRelativeSourceSmallness.{w} I) (hJ : UniformRelativeSourceSmallness.{w} J)
  (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType M)
  (hIrlp : I.rlp = trivialFibrations M) (hJrlp : J.rlp = fibrations M)

example : RelativeGenerationWitness.{w} I J :=
  RelativeGenerationWitness.ofUniformRelativeSmallness hI hJ hIteration hIrlp hJrlp

example :
    Nonempty {d : RelativeGenerationWitness.{w} I J //
      letI : ModelCategory (D ⥤ M) := d.modelCategory
      weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
        fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
        trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
        cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
        trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp} :=
  nonempty_projectiveModelCategory_of_uniform_relative_smallness I J hI hJ hIteration hIrlp hJrlp

example :
    ∃ d : RelativeGenerationWitness.{w} I J,
      letI : Fact d.cardinal.IsRegular := d.regular
      letI : OrderBot d.cardinal.ord.ToType := d.bottom
      letI : ModelCategory (D ⥤ M) := d.modelCategory
      ∃ g : CofibrantGenerationData (D ⥤ M) d.cardinal,
        g = d.generationData ∧
          weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
          fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
          g.I = FunctorProjective.freeGenerators d.baseData I ∧
          g.J = FunctorProjective.freeGenerators d.baseData J := by
  obtain ⟨⟨d, hd⟩⟩ :=
    nonempty_projectiveModelCategory_of_uniform_relative_smallness
      (D := D) I J hI hJ hIteration hIrlp hJrlp
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact ⟨d, d.generationData, rfl, hd.1, hd.2.1, d.generationData_I, d.generationData_J⟩

end ConventionalInput


section ConcreteIndices

example (d : RelativeGenerationWitness.{w} I J) :
    ModelCategory (Discrete PEmpty ⥤ M) := d.modelCategory

example (d : RelativeGenerationWitness.{w} I J) (f : Arrow (Discrete ℕ ⥤ M)) (n : ℕ) :
    letI : ModelCategory (Discrete ℕ ⥤ M) := d.modelCategory
    ((d.fibrantFactorizationData).i.app f).app ⟨n⟩ ≫
      ((d.fibrantFactorizationData).p.app f).app ⟨n⟩ = f.hom.app ⟨n⟩ :=
  d.fibrantFactorizationData_fac_app f ⟨n⟩

example (d : RelativeGenerationWitness.{w} I J) :
    ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) := d.modelCategory

local instance : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance : Small.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  small_map (ULiftHom.objEquiv.symm.trans Equiv.ulift)
local instance : Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))
local instance : LocallySmall.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) where
  hom_small x y := by
    let _ : Small.{w} (x.objDown.down ⟶ y.objDown.down) := LocallySmall.hom_small _ _
    exact small_map Equiv.ulift

example (d : RelativeGenerationWitness.{w} I J) :
    ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) := d.modelCategory

end ConcreteIndices

end MathlibExtTest.FunctorProjectiveRelativeSmallness
