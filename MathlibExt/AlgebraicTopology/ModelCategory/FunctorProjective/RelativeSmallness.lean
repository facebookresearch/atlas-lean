/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.RelativeSmallness
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization

/-!
# Original projective models from conventional relative generation

Return the actual common base cardinal, ordinal bottom and generation
datum first. Every original projective model, free family and factor
value is then the existing fixed-data getter for THAT witness. The
compatible-generation selector is never invoked to choose another one.

The original index objects and Hom universes remain independent.
Uniform source smallness and the structural colimits are explicit;
neither local presentability nor a target-diagram model/WFS is an input.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty
open CategoryTheory.SmallObject

namespace HomotopicalAlgebra.FunctorProjective

variable {M : Type uM} [Category.{vM} M] [ModelCategory M]

/-- A returned base witness retains the actual cardinal, bottom and original generating families. -/
structure RelativeGenerationWitness (I J : MorphismProperty M) where
  /-- The actual produced regular cardinal in the working universe. -/
  cardinal : Cardinal.{w}
  /-- Regularity belongs to that actual cardinal. -/
  regular : Fact cardinal.IsRegular
  /-- The bottom belongs to the ordinal of that same cardinal. -/
  bottom : OrderBot cardinal.ord.ToType
  /-- The complete base datum uses this exact cardinal and ordinal bottom. -/
  baseData : @CofibrantGenerationData M _ _ cardinal regular bottom
  /-- The stored I family is the original literal base family. -/
  baseI : baseData.I = I
  /-- The stored J family is the original literal base family. -/
  baseJ : baseData.J = J

namespace RelativeGenerationWitness

variable {I J : MorphismProperty M}

/-- An explicit fixed datum gives the same-witness record without another cardinal choice. -/
def ofData {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData M κ) : RelativeGenerationWitness d.I d.J where
  cardinal := κ
  regular := inferInstance
  bottom := inferInstance
  baseData := d
  baseI := rfl
  baseJ := rfl

/-- The whole supplied datum remains the original record field. -/
theorem ofData_baseData {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData M κ) : (ofData d).baseData = d := rfl

/-- The original fixed cardinal is retained by the explicit-data entry. -/
theorem ofData_cardinal {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData M κ) : (ofData d).cardinal = κ := rfl

/-- Conventional uniform source smallness returns one actual original base witness. -/
theorem nonempty_of_uniform_relative_smallness
    [I.IsSmall.{w}] [J.IsSmall.{w}] [LocallySmall.{w} M] [HasCoproducts.{w} M]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallness.{w} J)
    (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType M)
    (hIrlp : I.rlp = trivialFibrations M) (hJrlp : J.rlp = fibrations M) :
    Nonempty (RelativeGenerationWitness.{w} I J) := by
  obtain ⟨κ, hκ, hb, d, hdI, hdJ⟩ :=
    exists_cofibrantGenerationData_of_uniform_relative_smallness I J hI hJ hIteration hIrlp hJrlp
  exact ⟨{ cardinal := κ, regular := hκ, bottom := hb, baseData := d, baseI := hdI, baseJ := hdJ }⟩

/-- Choose that produced conventional witness once, with its original I/J equations. -/
def ofUniformRelativeSmallness
    [I.IsSmall.{w}] [J.IsSmall.{w}] [LocallySmall.{w} M] [HasCoproducts.{w} M]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallness.{w} J)
    (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType M)
    (hIrlp : I.rlp = trivialFibrations M) (hJrlp : J.rlp = fibrations M) :
    RelativeGenerationWitness.{w} I J :=
  Classical.choice (nonempty_of_uniform_relative_smallness hI hJ hIteration hIrlp hJrlp)

variable {D : Type uD} [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D]

/-- The target model is derived from the exact returned witness on the original diagram carrier. -/
@[instance_reducible]
def modelCategory (d : RelativeGenerationWitness.{w} I J) : ModelCategory (D ⥤ M) := by
  letI : Fact d.cardinal.IsRegular := d.regular
  letI : OrderBot d.cardinal.ord.ToType := d.bottom
  exact FunctorProjective.modelCategory (J := D) d.baseData

/-- The actual model is the original fixed-data construction at the returned base datum. -/
theorem modelCategory_eq_fixed (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    d.modelCategory (D := D) = FunctorProjective.modelCategory (J := D) d.baseData := rfl

/-- Public generation data retains the actual returned cardinal and original model. -/
def generationData (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    CofibrantGenerationData (D ⥤ M) d.cardinal := by
  letI : Fact d.cardinal.IsRegular := d.regular
  letI : OrderBot d.cardinal.ord.ToType := d.bottom
  letI : ModelCategory (D ⥤ M) := d.modelCategory
  exact FunctorProjective.generationData d.baseData

/-- The complete returned I family retains every original object and actual I-arrow. -/
theorem generationData_I (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.generationData (D := D)).I = FunctorProjective.freeGenerators d.baseData I := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  change FunctorProjective.freeGenerators d.baseData d.baseData.I = _
  rw [d.baseI]

/-- The complete returned J family retains every original object and actual J-arrow. -/
theorem generationData_J (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.generationData (D := D)).J = FunctorProjective.freeGenerators d.baseData J := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  change FunctorProjective.freeGenerators d.baseData d.baseData.J = _
  rw [d.baseJ]

/-- Both full eligibility dictionaries belong to the actual returned cardinal. -/
theorem generationData_eligible (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    (d.generationData (D := D)).I.IsCardinalForSmallObjectArgument d.cardinal ∧
      (d.generationData (D := D)).J.IsCardinalForSmallObjectArgument d.cardinal := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact ⟨(d.generationData).I_smallObject, (d.generationData).J_smallObject⟩

/-- The first actual factor value is the existing getter for this same returned base datum. -/
def cofibrantFactorizationData (d : RelativeGenerationWitness.{w} I J) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) := by
  letI : Fact d.cardinal.IsRegular := d.regular
  letI : OrderBot d.cardinal.ord.ToType := d.bottom
  letI : ModelCategory (D ⥤ M) := d.modelCategory
  exact FunctorProjective.cofibrantFactorizationData d.baseData

/-- The second actual factor value uses the same returned cardinal and base datum. -/
def fibrantFactorizationData (d : RelativeGenerationWitness.{w} I J) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) := by
  letI : Fact d.cardinal.IsRegular := d.regular
  letI : OrderBot d.cardinal.ord.ToType := d.bottom
  letI : ModelCategory (D ⥤ M) := d.modelCategory
  exact FunctorProjective.fibrantFactorizationData d.baseData

/-- The first whole factor record is the same original fixed-data getter. -/
theorem cofibrantFactorizationData_eq_fixed (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    d.cofibrantFactorizationData (D := D) =
      FunctorProjective.cofibrantFactorizationData d.baseData := rfl

/-- The second whole factor record is the same original fixed-data getter. -/
theorem fibrantFactorizationData_eq_fixed (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    d.fibrantFactorizationData (D := D) =
      FunctorProjective.fibrantFactorizationData d.baseData := rfl

/-- The entire cofibrant middle functor retains the original fixed-cardinal free-I field. -/
theorem cofibrantFactorizationData_Z (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    letI : IsCardinalForSmallObjectArgument
      (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.I) d.cardinal :=
        FunctorProjective.freeI_eligible d.baseData
    (d.cofibrantFactorizationData (D := D)).Z =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.I) d.cardinal).Z :=
  rfl

/-- The entire cofibrant left transformation retains the original fixed-cardinal free-I field. -/
theorem cofibrantFactorizationData_i (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    letI : IsCardinalForSmallObjectArgument
      (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.I) d.cardinal :=
        FunctorProjective.freeI_eligible d.baseData
    (d.cofibrantFactorizationData (D := D)).i =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.I) d.cardinal).i :=
  rfl

/-- The entire cofibrant right transformation retains the original fixed-cardinal free-I field. -/
theorem cofibrantFactorizationData_p (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    letI : IsCardinalForSmallObjectArgument
      (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.I) d.cardinal :=
        FunctorProjective.freeI_eligible d.baseData
    (d.cofibrantFactorizationData (D := D)).p =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.I) d.cardinal).p :=
  rfl





/-- The entire fibrant middle functor retains the original fixed-cardinal free-J field. -/
theorem fibrantFactorizationData_Z (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    letI : IsCardinalForSmallObjectArgument
      (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.J) d.cardinal :=
        FunctorProjective.freeJ_eligible d.baseData
    (d.fibrantFactorizationData (D := D)).Z =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.J) d.cardinal).Z :=
  rfl

/-- The entire fibrant left transformation retains the original fixed-cardinal free-J field. -/
theorem fibrantFactorizationData_i (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    letI : IsCardinalForSmallObjectArgument
      (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.J) d.cardinal :=
        FunctorProjective.freeJ_eligible d.baseData
    (d.fibrantFactorizationData (D := D)).i =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.J) d.cardinal).i :=
  rfl

/-- The entire fibrant right transformation retains the original fixed-cardinal free-J field. -/
theorem fibrantFactorizationData_p (d : RelativeGenerationWitness.{w} I J) :
    letI : Fact d.cardinal.IsRegular := d.regular
    letI : OrderBot d.cardinal.ord.ToType := d.bottom
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    letI : IsCardinalForSmallObjectArgument
      (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.J) d.cardinal :=
        FunctorProjective.freeJ_eligible d.baseData
    (d.fibrantFactorizationData (D := D)).p =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) d.baseData d.baseData.J) d.cardinal).p :=
  rfl





/-- Every original component retains the cofibrant i-leg Arrow naturality equation. -/
theorem cofibrantFactorizationData_i_naturality_app (d : RelativeGenerationWitness.{w} I J)
    {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    φ.left.app x ≫ ((d.cofibrantFactorizationData).i.app g).app x =
      ((d.cofibrantFactorizationData).i.app f).app x ≫ ((d.cofibrantFactorizationData).Z.map φ).app
        x := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact NatTrans.congr_app ((d.cofibrantFactorizationData).i.naturality φ) x

/-- Every original component retains the cofibrant p-leg Arrow naturality equation. -/
theorem cofibrantFactorizationData_p_naturality_app (d : RelativeGenerationWitness.{w} I J)
    {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    ((d.cofibrantFactorizationData).Z.map φ).app x ≫ ((d.cofibrantFactorizationData).p.app g).app x
      =
      ((d.cofibrantFactorizationData).p.app f).app x ≫ φ.right.app x := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact NatTrans.congr_app ((d.cofibrantFactorizationData).p.naturality φ) x

/-- Every original component retains the fibrant i-leg Arrow naturality equation. -/
theorem fibrantFactorizationData_i_naturality_app (d : RelativeGenerationWitness.{w} I J)
    {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    φ.left.app x ≫ ((d.fibrantFactorizationData).i.app g).app x =
      ((d.fibrantFactorizationData).i.app f).app x ≫ ((d.fibrantFactorizationData).Z.map φ).app x :=
        by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact NatTrans.congr_app ((d.fibrantFactorizationData).i.naturality φ) x

/-- Every original component retains the fibrant p-leg Arrow naturality equation. -/
theorem fibrantFactorizationData_p_naturality_app (d : RelativeGenerationWitness.{w} I J)
    {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    ((d.fibrantFactorizationData).Z.map φ).app x ≫ ((d.fibrantFactorizationData).p.app g).app x =
      ((d.fibrantFactorizationData).p.app f).app x ≫ φ.right.app x := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact NatTrans.congr_app ((d.fibrantFactorizationData).p.naturality φ) x

/-- All five prescribed classes retain the exact original fixed-data model. -/
theorem five_classes (d : RelativeGenerationWitness.{w} I J) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
      fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
      trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
      cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact FunctorProjective.five_classes d.baseData


/-- The actual first factor equation holds at every original diagram component. -/
theorem cofibrantFactorizationData_fac_app (d : RelativeGenerationWitness.{w} I J)
    (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    ((d.cofibrantFactorizationData).i.app f).app x ≫
      ((d.cofibrantFactorizationData).p.app f).app x = f.hom.app x := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact NatTrans.congr_app ((d.cofibrantFactorizationData).fac_app) x

/-- The actual second factor equation holds at every original diagram component. -/
theorem fibrantFactorizationData_fac_app (d : RelativeGenerationWitness.{w} I J)
    (f : Arrow (D ⥤ M)) (x : D) :
    letI : ModelCategory (D ⥤ M) := d.modelCategory
    ((d.fibrantFactorizationData).i.app f).app x ≫
      ((d.fibrantFactorizationData).p.app f).app x = f.hom.app x := by
  let _ : Fact d.cardinal.IsRegular := d.regular
  let _ : OrderBot d.cardinal.ord.ToType := d.bottom
  let _ : ModelCategory (D ⥤ M) := d.modelCategory
  exact NatTrans.congr_app ((d.fibrantFactorizationData).fac_app) x

end RelativeGenerationWitness

/-- Conventional generation retains the actual base witness and its projective class equations. -/
theorem nonempty_projectiveModelCategory_of_uniform_relative_smallness
    {D : Type uD} [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D]
    (I J : MorphismProperty M) [I.IsSmall.{w}] [J.IsSmall.{w}]
    [LocallySmall.{w} M] [HasCoproducts.{w} M]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallness.{w} J)
    (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType M)
    (hIrlp : I.rlp = trivialFibrations M) (hJrlp : J.rlp = fibrations M) :
    Nonempty {d : RelativeGenerationWitness.{w} I J //
      letI : ModelCategory (D ⥤ M) := d.modelCategory
      weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
        fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
        trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
        cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
        trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp} := by
  let d := RelativeGenerationWitness.ofUniformRelativeSmallness hI hJ hIteration hIrlp hJrlp
  exact ⟨⟨d, d.five_classes⟩⟩

end HomotopicalAlgebra.FunctorProjective
