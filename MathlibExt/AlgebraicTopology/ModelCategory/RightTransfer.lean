/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.RelativeSmallness
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Full right transfer with original free generators and source ranks

Uniform relative source smallness produces one common regular cardinal for the
literal images of the caller's two generating families. Model recognition uses
the original adjunction and the derived acyclicity of the free trivial cells.
The output stores the original families, the source bounds and both complete
functorial factorizations on the existing target category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC uD vD

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.SmallObject

namespace HomotopicalAlgebra.RightTransfer

section Cardinal

variable {D : Type uD} [Category.{vD} D]

/-- A common regular source rank, retaining both actual families and all six SOA fields. -/
structure GenerationCardinal (P Q : MorphismProperty D)
    (hP : UniformRelativeSourceSmallness.{w} P)
    (hQ : UniformRelativeSourceSmallness.{w} Q) where
  /-- The produced common source rank. -/
  cardinal : Cardinal.{w}
  /-- Regularity of that same cardinal. -/
  regular : Fact cardinal.IsRegular
  /-- The original ordinal bottom used by both constructions. -/
  orderBot : OrderBot cardinal.ord.ToType
  /-- Every original first-family source bound is below the common rank. -/
  sourceP_bounds : ∀ p : P.toSet, UniformRelativeSourceSmallness.sourceBound hP p < cardinal
  /-- Every original second-family source bound is below the same rank. -/
  sourceQ_bounds : ∀ q : Q.toSet, UniformRelativeSourceSmallness.sourceBound hQ q < cardinal
  /-- The complete small-object eligibility for the literal first family. -/
  P_smallObject : letI := regular; letI := orderBot; P.IsCardinalForSmallObjectArgument cardinal
  /-- The complete small-object eligibility for the literal second family. -/
  Q_smallObject : letI := regular; letI := orderBot; Q.IsCardinalForSmallObjectArgument cardinal

variable [LocallySmall.{w} D] [HasColimitsOfSize.{w, w} D]
  (P Q : MorphismProperty D) [P.IsSmall.{w}] [Q.IsSmall.{w}]
  (hP : UniformRelativeSourceSmallness.{w} P)
  (hQ : UniformRelativeSourceSmallness.{w} Q)

/-- Actual uniform source smallness constructs both algorithms at one common regular rank. -/
def generationCardinal : GenerationCardinal P Q hP hQ := by
  letI : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeOfUnivLE.{w, w} D
  apply Classical.choice
  obtain ⟨κ, hκ, hPκ, hQκ⟩ := exists_common_relative_source_bound P Q hP hQ
  let : Fact κ.IsRegular := ⟨hκ⟩
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ.ne_zero
  let bottom : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let : OrderBot κ.ord.ToType := bottom
  refine ⟨?_⟩
  exact
    { cardinal := κ
      regular := inferInstance
      orderBot := bottom
      sourceP_bounds := hPκ
      sourceQ_bounds := hQκ
      P_smallObject := isCardinalForSmallObjectArgument_of_uniform_bounds P hP κ hPκ
      Q_smallObject := isCardinalForSmallObjectArgument_of_uniform_bounds Q hQ κ hQκ }

end Cardinal

section Classes

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D]

/-- The weak class is created by the actual original right adjoint. -/
abbrev weakClass (R : D ⥤ C) : MorphismProperty D := (weakEquivalences C).inverseImage R

/-- The fibration class consists of the actual underlying base fibrations. -/
abbrev fibrationClass (R : D ⥤ C) : MorphismProperty D := (fibrations C).inverseImage R

/-- The actual underlying trivial-fibration class. -/
abbrev trivialFibrationClass (R : D ⥤ C) : MorphismProperty D := (trivialFibrations C).inverseImage R

/-- Cofibrations lift against every actual underlying trivial fibration. -/
abbrev cofibrationClass (R : D ⥤ C) : MorphismProperty D := (trivialFibrationClass R).llp

/-- The trivial-cofibration class in the constructed full model. -/
abbrev trivialCofibrationClass (R : D ⥤ C) : MorphismProperty D := cofibrationClass R ⊓ weakClass R

variable (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
  (I J : MorphismProperty C)
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)

/-- A full right transfer on the existing target, with all source and factorization data retained. -/
structure FullModelTransfer
    (hSourceI : UniformRelativeSourceSmallness.{w} (I.strictMap L))
    (hSourceJ : UniformRelativeSourceSmallness.{w} (J.strictMap L)) where
  /-- The produced cardinal and both original source smallness dictionaries. -/
  generationCardinal : GenerationCardinal (I.strictMap L) (J.strictMap L) hSourceI hSourceJ
  /-- Completeness of the actual target category. -/
  complete : HasLimitsOfSize.{w, w} D
  /-- Cocompleteness of that same category. -/
  cocomplete : HasColimitsOfSize.{w, w} D
  /-- The constructed model, supplied as output only. -/
  model : ModelCategory D
  /-- Exact original underlying weak equivalences. -/
  weak_eq : letI := model; weakEquivalences D = weakClass R
  /-- Exact original underlying fibrations. -/
  fibrations_eq : letI := model; fibrations D = fibrationClass R
  /-- Exact cofibrations against the original underlying trivial fibrations. -/
  cofibrations_eq : letI := model; cofibrations D = cofibrationClass R
  /-- Exact original underlying trivial fibrations. -/
  trivialFibrations_eq : letI := model; trivialFibrations D = trivialFibrationClass R
  /-- The full original free-J generated left class. -/
  trivialCofibrations_eq : letI := model; trivialCofibrations D = (J.strictMap L).rlp.llp
  /-- The complete generating-family datum for this same model and cardinal. -/
  generation : letI := generationCardinal.regular; letI := generationCardinal.orderBot; letI := model;
    CofibrantGenerationData D generationCardinal.cardinal
  /-- The I family is literally the caller's actual free-I family. -/
  generation_I : letI := generationCardinal.regular; letI := generationCardinal.orderBot; letI := model;
    generation.I = I.strictMap L
  /-- The J family is literally the caller's actual free-J family. -/
  generation_J : letI := generationCardinal.regular; letI := generationCardinal.orderBot; letI := model;
    generation.J = J.strictMap L

variable [HasLimitsOfSize.{w, w} D] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hSourceI : UniformRelativeSourceSmallness.{w} (I.strictMap L))
  (hSourceJ : UniformRelativeSourceSmallness.{w} (J.strictMap L))

/-- Full right transfer from actual relative source smallness and derived free-cell acyclicity.
The acyclicity callback is used only at the common cardinal constructed from the source bounds. -/
def fullModelTransfer
    (hAcyclicity : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
      [(J.strictMap L).IsCardinalForSmallObjectArgument κ], (J.strictMap L).rlp.llp ≤ weakClass R) :
    FullModelTransfer L R I J hSourceI hSourceJ := by
  letI : (I.strictMap L).IsSmall.{w} := IsSmall.strictMap (inferInstance : I.IsSmall.{w}) L
  letI : (J.strictMap L).IsSmall.{w} := IsSmall.strictMap (inferInstance : J.IsSmall.{w}) L
  let d := generationCardinal (I.strictMap L) (J.strictMap L) hSourceI hSourceJ
  letI : Fact d.cardinal.IsRegular := d.regular
  letI : OrderBot d.cardinal.ord.ToType := d.orderBot
  letI : (I.strictMap L).IsCardinalForSmallObjectArgument d.cardinal := d.P_smallObject
  letI : (J.strictMap L).IsCardinalForSmallObjectArgument d.cardinal := d.Q_smallObject
  letI : HasLimitsOfSize.{0, 0} D := hasLimitsOfSizeOfUnivLE.{w, w} D
  letI : HasColimitsOfSize.{0, 0} D := hasColimitsOfSizeOfUnivLE.{w, w} D
  let M : ModelCategory D := by
    letI : (I.strictMap L).HasSmallObjectArgument.{w} :=
      ⟨d.cardinal, inferInstance, inferInstance, inferInstance⟩
    letI : (J.strictMap L).HasSmallObjectArgument.{w} :=
      ⟨d.cardinal, inferInstance, inferInstance, inferInstance⟩
    have hIRight : (I.strictMap L).rlp = trivialFibrationClass R := by
      rw [strictMap_rlp_eq_inverseImage_rlp I L R adj, hI]
    have hJRight : (J.strictMap L).rlp = fibrationClass R := by
      rw [strictMap_rlp_eq_inverseImage_rlp J L R adj, hJ]
    have hRight : (I.strictMap L).rlp = (J.strictMap L).rlp ⊓ weakClass R := by
      rw [hIRight, hJRight]
      rfl
    let smith := SmithModelStructureData.ofGenerators (I.strictMap L) (J.strictMap L)
      (weakClass R) inferInstance hRight (hAcyclicity d.cardinal)
    letI : CategoryWithCofibrations D := ⟨cofibrationClass R⟩
    letI : CategoryWithFibrations D := ⟨fibrationClass R⟩
    letI : CategoryWithWeakEquivalences D := ⟨weakClass R⟩
    exact smith.modelCategory inferInstance (congrArg MorphismProperty.llp hIRight).symm hJRight.symm rfl
  letI : ModelCategory D := M
  have hTF : trivialFibrations D = trivialFibrationClass R := rfl
  have hFib : fibrations D = fibrationClass R := rfl
  have hTC : trivialCofibrations D = (J.strictMap L).rlp.llp := by
    rw [← fibrations_llp D, hFib]
    change ((fibrations C).inverseImage R).llp = (J.strictMap L).rlp.llp
    rw [← hJ, ← strictMap_rlp_eq_inverseImage_rlp J L R adj]
  refine
    { generationCardinal := d
      complete := inferInstance
      cocomplete := inferInstance
      model := M
      weak_eq := rfl
      fibrations_eq := hFib
      cofibrations_eq := rfl
      trivialFibrations_eq := hTF
      trivialCofibrations_eq := hTC
      generation :=
        { I := I.strictMap L
          J := J.strictMap L
          I_smallObject := inferInstance
          J_smallObject := inferInstance
          I_rlp := ?_
          J_rlp := ?_ }
      generation_I := rfl
      generation_J := rfl }
  · rw [strictMap_rlp_eq_inverseImage_rlp I L R adj, hI, hTF]
  · rw [strictMap_rlp_eq_inverseImage_rlp J L R adj, hJ, hFib]

end Classes

namespace FullModelTransfer

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D]
  {L : C ⥤ D} {R : D ⥤ C} {I J : MorphismProperty C}
  {hSourceI : UniformRelativeSourceSmallness.{w} (I.strictMap L)}
  {hSourceJ : UniformRelativeSourceSmallness.{w} (J.strictMap L)}
  (t : FullModelTransfer L R I J hSourceI hSourceJ)

/-- The actual free-I algorithm gives the full cofibration/trivial-fibration factorization. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData (cofibrationClass R) (trivialFibrationClass R) := by
  letI : Fact t.generationCardinal.cardinal.IsRegular := t.generationCardinal.regular
  letI : OrderBot t.generationCardinal.cardinal.ord.ToType := t.generationCardinal.orderBot
  letI : ModelCategory D := t.model
  exact t.generation.cofibrantFactorizationData.ofLE t.cofibrations_eq.le t.trivialFibrations_eq.le

/-- The same original common rank gives the full trivial-cofibration/fibration factorization. -/
def fibrantFactorizationData :
    FunctorialFactorizationData (trivialCofibrationClass R) (fibrationClass R) := by
  letI : Fact t.generationCardinal.cardinal.IsRegular := t.generationCardinal.regular
  letI : OrderBot t.generationCardinal.cardinal.ord.ToType := t.generationCardinal.orderBot
  letI : ModelCategory D := t.model
  have hTC : trivialCofibrations D = trivialCofibrationClass R := by
    change cofibrations D ⊓ weakEquivalences D = trivialCofibrationClass R
    rw [t.cofibrations_eq, t.weak_eq]
  exact t.generation.fibrantFactorizationData.ofLE hTC.le t.fibrations_eq.le

/-- Both complete natural transformations factor every original target arrow. -/
theorem cofibrantFactorization_fac :
    t.cofibrantFactorizationData.i ≫ t.cofibrantFactorizationData.p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  t.cofibrantFactorizationData.fac

/-- The original free-J construction factors every target arrow with the same endpoints. -/
theorem fibrantFactorization_fac :
    t.fibrantFactorizationData.i ≫ t.fibrantFactorizationData.p =
      (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  t.fibrantFactorizationData.fac

/-- Every first factor is a cofibration in the exact original lifting class. -/
theorem cofibrantFactorization_left (f : Arrow D) :
    cofibrationClass R (t.cofibrantFactorizationData.i.app f) :=
  t.cofibrantFactorizationData.hi f

/-- Every second factor is an actual underlying trivial fibration. -/
theorem cofibrantFactorization_right (f : Arrow D) :
    trivialFibrationClass R (t.cofibrantFactorizationData.p.app f) :=
  t.cofibrantFactorizationData.hp f

/-- Every original free-J first factor is trivial in the returned full model. -/
theorem fibrantFactorization_left (f : Arrow D) :
    trivialCofibrationClass R (t.fibrantFactorizationData.i.app f) :=
  t.fibrantFactorizationData.hi f

/-- Every original free-J second factor is an actual underlying fibration. -/
theorem fibrantFactorization_right (f : Arrow D) :
    fibrationClass R (t.fibrantFactorizationData.p.app f) :=
  t.fibrantFactorizationData.hp f

end FullModelTransfer

end HomotopicalAlgebra.RightTransfer
