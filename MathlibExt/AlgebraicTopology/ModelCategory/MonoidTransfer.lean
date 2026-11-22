/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidTransfer.RelativeSmallness
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRecognition
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# The full transferred model on associative unital monoids

The actual tensor-word free images of the original I and J families generate
the model on `Mon C`. The source monoid axiom and the actual word filtration
prove free-J acyclicity. Uniform relative source-Hom smallness constructs one
regular cardinal and both complete small-object arguments. The returned
generation data gives the two original functorial factorizations on all arrows.
-/

@[expose] public section

noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty
open CategoryTheory.SmallObject

namespace HomotopicalAlgebra.MonoidTransfer

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]

local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))

/-- The original adjunction identifies the entire free right lifting class with its underlying class. -/
theorem freeGenerators_rlp (P : MorphismProperty C) :
    (freeGenerators P).rlp = P.rlp.inverseImage (Mon.forget C) :=
  strictMap_rlp_eq_inverseImage_rlp P free (Mon.forget C) adjunction

variable [ModelCategory C]

/-- Weak equivalences are created by the actual original monoid forgetful functor. -/
abbrev weakClass : MorphismProperty (Mon C) := (weakEquivalences C).inverseImage (Mon.forget C)

/-- Fibrations are the actual underlying source fibrations. -/
abbrev fibrationClass : MorphismProperty (Mon C) := (fibrations C).inverseImage (Mon.forget C)

/-- Trivial fibrations retain the entire underlying source intersection. -/
abbrev trivialFibrationClass : MorphismProperty (Mon C) :=
  (trivialFibrations C).inverseImage (Mon.forget C)

/-- Cofibrations have the full left lifting property against all underlying trivial fibrations. -/
abbrev cofibrationClass : MorphismProperty (Mon C) := (trivialFibrationClass (C := C)).llp

/-- Trivial cofibrations are the actual intersection in the returned model. -/
abbrev trivialCofibrationClass : MorphismProperty (Mon C) := cofibrationClass (C := C) ⊓ weakClass (C := C)

section FixedCardinal

variable [IsClosedSymmetricMonoidalModelCategory C] [MonoidAxiom.{w} C]
  [HasFiniteLimits (Mon C)] [HasFiniteColimits (Mon C)]
  (I J : MorphismProperty C)
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [(freeGenerators I).IsCardinalForSmallObjectArgument κ]
  [(freeGenerators J).IsCardinalForSmallObjectArgument κ]

/-- The two original small-object arguments and the A4-derived acyclicity construct the full target model. -/
@[instance_reducible]
def modelCategoryAtCardinal : ModelCategory (Mon C) := by
  let : (freeGenerators I).HasSmallObjectArgument.{w} := ⟨κ, inferInstance, inferInstance, inferInstance⟩
  let : (freeGenerators J).HasSmallObjectArgument.{w} := ⟨κ, inferInstance, inferInstance, inferInstance⟩
  let : (weakClass (C := C)).HasTwoOutOfThreeProperty := inferInstance
  have hIRight : (freeGenerators I).rlp = trivialFibrationClass (C := C) := by
    rw [freeGenerators_rlp, hI]
  have hJRight : (freeGenerators J).rlp = fibrationClass (C := C) := by
    rw [freeGenerators_rlp, hJ]
  have hRight : (freeGenerators I).rlp = (freeGenerators J).rlp ⊓ weakClass (C := C) := by
    rw [hIRight, hJRight]
    rfl
  let d := SmithModelStructureData.ofGenerators (freeGenerators I) (freeGenerators J)
    (weakClass (C := C)) inferInstance hRight (freeJLeft_underlying_weak J hJ κ)
  letI : CategoryWithCofibrations (Mon C) := ⟨cofibrationClass (C := C)⟩
  letI : CategoryWithFibrations (Mon C) := ⟨fibrationClass (C := C)⟩
  letI : CategoryWithWeakEquivalences (Mon C) := ⟨weakClass (C := C)⟩
  exact d.modelCategory inferInstance (congrArg MorphismProperty.llp hIRight).symm hJRight.symm rfl

/-- The selected full model has exactly the original underlying weak class. -/
theorem weakEquivalencesAtCardinal_eq :
    letI : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
    weakEquivalences (Mon C) = weakClass (C := C) := rfl

/-- The selected full model has exactly the original underlying fibration class. -/
theorem fibrationsAtCardinal_eq :
    letI : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
    fibrations (Mon C) = fibrationClass (C := C) := rfl

/-- The selected cofibration class is the full left lifting class against underlying trivial fibrations. -/
theorem cofibrationsAtCardinal_eq :
    letI : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
    cofibrations (Mon C) = cofibrationClass (C := C) := rfl

/-- The selected full model retains the entire original underlying trivial-fibration class. -/
theorem trivialFibrationsAtCardinal_eq :
    letI : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
    trivialFibrations (Mon C) = trivialFibrationClass (C := C) := rfl

/-- Trivial cofibrations are precisely the original free-J left lifting class. -/
theorem trivialCofibrationsAtCardinal_eq :
    letI : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
    trivialCofibrations (Mon C) = (freeGenerators J).rlp.llp := by
  let : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
  rw [← fibrations_llp (Mon C), fibrationsAtCardinal_eq I J hI hJ κ, freeGenerators_rlp, hJ]

/-- The returned generation record stores the caller's actual free-I and free-J families at this cardinal. -/
def generationDataAtCardinal :
    letI : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
    CofibrantGenerationData (Mon C) κ := by
  let : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ κ
  exact
    { I := freeGenerators I
      J := freeGenerators J
      I_smallObject := inferInstance
      J_smallObject := inferInstance
      I_rlp := by rw [freeGenerators_rlp, hI, trivialFibrationsAtCardinal_eq I J hI hJ κ]
      J_rlp := by rw [freeGenerators_rlp, hJ, fibrationsAtCardinal_eq I J hI hJ κ] }

end FixedCardinal

/-- Complete full transfer data on the actual monoid category, including original source ranks and generators. -/
structure FullModelTransfer (I J : MorphismProperty C)
    (hSourceI : UniformRelativeSourceSmallness.{w} (freeGenerators I))
    (hSourceJ : UniformRelativeSourceSmallness.{w} (freeGenerators J)) where
  /-- The common regular cardinal, original source bounds, and both entire eligibility records. -/
  generationCardinal : FreeGenerationCardinal I J hSourceI hSourceJ
  /-- Actual completeness of the genuine monoid category. -/
  complete : HasLimitsOfSize.{w, w} (Mon C)
  /-- Actual cocompleteness of that same monoid category. -/
  cocomplete : HasColimitsOfSize.{w, w} (Mon C)
  /-- Preservation by the actual tensor-word free monad, including the unit summand. -/
  monadFiltered :
    PreservesFilteredColimitsOfSize.{w, w} (MonoidalCategory.TensorWord.tensorWordMonad (C := C) : C ⥤ C)
  /-- The constructed full model; no target model is supplied to its constructor. -/
  model : ModelCategory (Mon C)
  /-- Exact underlying weak equivalences for the returned model. -/
  weak_eq : letI := model; weakEquivalences (Mon C) = weakClass (C := C)
  /-- Exact underlying fibrations for that same model. -/
  fibrations_eq : letI := model; fibrations (Mon C) = fibrationClass (C := C)
  /-- Exact cofibrations against all underlying trivial fibrations. -/
  cofibrations_eq : letI := model; cofibrations (Mon C) = cofibrationClass (C := C)
  /-- Exact underlying trivial fibrations. -/
  trivialFibrations_eq : letI := model; trivialFibrations (Mon C) = trivialFibrationClass (C := C)
  /-- Exact free-J generated trivial cofibrations. -/
  trivialCofibrations_eq : letI := model; trivialCofibrations (Mon C) = (freeGenerators J).rlp.llp
  /-- The complete cofibrant generation data on this same model and this same original common cardinal. -/
  generation : letI := generationCardinal.regular; letI := generationCardinal.orderBot; letI := model;
    CofibrantGenerationData (Mon C) generationCardinal.cardinal
  /-- The stored I family is literally the original free-I family. -/
  generation_I : letI := generationCardinal.regular; letI := generationCardinal.orderBot; letI := model;
    generation.I = freeGenerators I
  /-- The stored J family is literally the original free-J family. -/
  generation_J : letI := generationCardinal.regular; letI := generationCardinal.orderBot; letI := model;
    generation.J = freeGenerators J

variable [IsClosedSymmetricMonoidalModelCategory C] [MonoidAxiom.{w} C]
  [HasLimitsOfSize.{w, w} C] [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} (Mon C)]
  (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
  (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
  (hSourceI : UniformRelativeSourceSmallness.{w} (freeGenerators I))
  (hSourceJ : UniformRelativeSourceSmallness.{w} (freeGenerators J))

/-- Full associative unital algebra model transfer from the original source hypotheses.
Both complete functorial factors are constructed from the returned original generation data. -/
def fullAssociativeUnitalAlgebraModelTransfer : FullModelTransfer I J hSourceI hSourceJ := by
  let d := freeGenerationCardinal I J hSourceI hSourceJ
  let : Fact d.cardinal.IsRegular := d.regular
  letI : OrderBot d.cardinal.ord.ToType := d.orderBot
  let : (freeGenerators I).IsCardinalForSmallObjectArgument d.cardinal := d.I_smallObject
  let : (freeGenerators J).IsCardinalForSmallObjectArgument d.cardinal := d.J_smallObject
  let complete : HasLimitsOfSize.{w, w} (Mon C) := { has_limits_of_shape := fun _ _ => inferInstance }
  let : HasLimitsOfSize.{w, w} (Mon C) := complete
  let : HasLimitsOfSize.{0, 0} (Mon C) := hasLimitsOfSizeOfUnivLE.{w, w} (Mon C)
  let : HasColimitsOfSize.{0, 0} (Mon C) := hasColimitsOfSizeOfUnivLE.{w, w} (Mon C)
  let M : ModelCategory (Mon C) := modelCategoryAtCardinal I J hI hJ d.cardinal
  exact
    { generationCardinal := d
      complete := complete
      cocomplete := inferInstance
      monadFiltered := tensorWordMonadPreservesFilteredColimits
      model := M
      weak_eq := weakEquivalencesAtCardinal_eq I J hI hJ d.cardinal
      fibrations_eq := fibrationsAtCardinal_eq I J hI hJ d.cardinal
      cofibrations_eq := cofibrationsAtCardinal_eq I J hI hJ d.cardinal
      trivialFibrations_eq := trivialFibrationsAtCardinal_eq I J hI hJ d.cardinal
      trivialCofibrations_eq := trivialCofibrationsAtCardinal_eq I J hI hJ d.cardinal
      generation := generationDataAtCardinal I J hI hJ d.cardinal
      generation_I := rfl
      generation_J := rfl }

/-- The actual original free-I algorithm gives a complete factorization on all monoid arrows. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData (cofibrationClass (C := C)) (trivialFibrationClass (C := C)) := by
  let t := fullAssociativeUnitalAlgebraModelTransfer I J hI hJ hSourceI hSourceJ
  let : Fact t.generationCardinal.cardinal.IsRegular := t.generationCardinal.regular
  letI : OrderBot t.generationCardinal.cardinal.ord.ToType := t.generationCardinal.orderBot
  letI : ModelCategory (Mon C) := t.model
  exact t.generation.cofibrantFactorizationData.ofLE t.cofibrations_eq.le t.trivialFibrations_eq.le

/-- The actual original free-J algorithm gives the complete trivial-cofibration/fibration factor. -/
def fibrantFactorizationData :
    FunctorialFactorizationData (trivialCofibrationClass (C := C)) (fibrationClass (C := C)) := by
  let t := fullAssociativeUnitalAlgebraModelTransfer I J hI hJ hSourceI hSourceJ
  let : Fact t.generationCardinal.cardinal.IsRegular := t.generationCardinal.regular
  letI : OrderBot t.generationCardinal.cardinal.ord.ToType := t.generationCardinal.orderBot
  letI : ModelCategory (Mon C) := t.model
  have hTC : trivialCofibrations (Mon C) = trivialCofibrationClass (C := C) := by
    change cofibrations (Mon C) ⊓ weakEquivalences (Mon C) = trivialCofibrationClass (C := C)
    rw [t.cofibrations_eq, t.weak_eq]
  exact t.generation.fibrantFactorizationData.ofLE hTC.le t.fibrations_eq.le

/-- The whole I intermediate functor and both original natural transformations are the original algorithm. -/
theorem cofibrantFactorizationData_fields :
    let d := freeGenerationCardinal I J hSourceI hSourceJ
    letI := d.regular
    letI := d.orderBot
    letI : (freeGenerators I).IsCardinalForSmallObjectArgument d.cardinal := d.I_smallObject
    let raw := SmallObject.functorialFactorizationData (freeGenerators I) d.cardinal
    let out := cofibrantFactorizationData I J hI hJ hSourceI hSourceJ
    out.Z = raw.Z ∧ out.i = raw.i ∧ out.p = raw.p := ⟨rfl, rfl, rfl⟩

/-- The whole J intermediate functor and both natural transformations use the same original cardinal. -/
theorem fibrantFactorizationData_fields :
    let d := freeGenerationCardinal I J hSourceI hSourceJ
    letI := d.regular
    letI := d.orderBot
    letI : (freeGenerators J).IsCardinalForSmallObjectArgument d.cardinal := d.J_smallObject
    let raw := SmallObject.functorialFactorizationData (freeGenerators J) d.cardinal
    let out := fibrantFactorizationData I J hI hJ hSourceI hSourceJ
    out.Z = raw.Z ∧ out.i = raw.i ∧ out.p = raw.p := ⟨rfl, rfl, rfl⟩

/-- Every original monoid commutative square gives precisely the original I middle map. -/
theorem cofibrantFactorizationData_map {f g : Arrow (Mon C)} (φ : f ⟶ g) :
    let d := freeGenerationCardinal I J hSourceI hSourceJ
    letI := d.regular
    letI := d.orderBot
    letI : (freeGenerators I).IsCardinalForSmallObjectArgument d.cardinal := d.I_smallObject
    (cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).Z.map φ =
      SmallObject.objMap (freeGenerators I) d.cardinal φ := rfl

/-- Every original monoid square gives the original J middle map, on that same produced rank. -/
theorem fibrantFactorizationData_map {f g : Arrow (Mon C)} (φ : f ⟶ g) :
    let d := freeGenerationCardinal I J hSourceI hSourceJ
    letI := d.regular
    letI := d.orderBot
    letI : (freeGenerators J).IsCardinalForSmallObjectArgument d.cardinal := d.J_smallObject
    (fibrantFactorizationData I J hI hJ hSourceI hSourceJ).Z.map φ =
      SmallObject.objMap (freeGenerators J) d.cardinal φ := rfl

/-- The entire original I factor transformations recover the original Arrow transformation. -/
theorem cofibrantFactorizationData_fac :
    (cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).i ≫
      (cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).p =
        (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).fac

/-- The original J factor transformations recover every original Arrow at once. -/
theorem fibrantFactorizationData_fac :
    (fibrantFactorizationData I J hI hJ hSourceI hSourceJ).i ≫
      (fibrantFactorizationData I J hI hJ hSourceI hSourceJ).p =
        (Arrow.leftToRight : Arrow.leftFunc ⟶ Arrow.rightFunc) :=
  (fibrantFactorizationData I J hI hJ hSourceI hSourceJ).fac

/-- Every original I left factor is a full transferred cofibration. -/
theorem cofibrantFactorizationData_hi (f : Arrow (Mon C)) :
    cofibrationClass (C := C) ((cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).i.app f) :=
  (cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).hi f

/-- Every original I right factor is an actual underlying source trivial fibration. -/
theorem cofibrantFactorizationData_hp (f : Arrow (Mon C)) :
    trivialFibrations C ((cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).p.app f).hom :=
  (cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).hp f

/-- Every original J left factor is a full cofibration and an actual underlying weak equivalence. -/
theorem fibrantFactorizationData_hi (f : Arrow (Mon C)) :
    trivialCofibrationClass (C := C) ((fibrantFactorizationData I J hI hJ hSourceI hSourceJ).i.app f) :=
  (fibrantFactorizationData I J hI hJ hSourceI hSourceJ).hi f

/-- Every original J right factor is an actual underlying source fibration. -/
theorem fibrantFactorizationData_hp (f : Arrow (Mon C)) :
    fibrations C ((fibrantFactorizationData I J hI hJ hSourceI hSourceJ).p.app f).hom :=
  (fibrantFactorizationData I J hI hJ hSourceI hSourceJ).hp f

/-- Both original I naturality squares retain the complete source and target maps of every supplied square. -/
theorem cofibrantFactorizationData_naturality {f g : Arrow (Mon C)} (φ : f ⟶ g) :
    let out := cofibrantFactorizationData I J hI hJ hSourceI hSourceJ
    out.i.app f ≫ out.Z.map φ = φ.left ≫ out.i.app g ∧
      out.Z.map φ ≫ out.p.app g = out.p.app f ≫ φ.right :=
  ⟨((cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).i.naturality φ).symm,
    (cofibrantFactorizationData I J hI hJ hSourceI hSourceJ).p.naturality φ⟩

/-- Both original J squares retain all supplied monoid-map components. -/
theorem fibrantFactorizationData_naturality {f g : Arrow (Mon C)} (φ : f ⟶ g) :
    let out := fibrantFactorizationData I J hI hJ hSourceI hSourceJ
    out.i.app f ≫ out.Z.map φ = φ.left ≫ out.i.app g ∧
      out.Z.map φ ≫ out.p.app g = out.p.app f ≫ φ.right :=
  ⟨((fibrantFactorizationData I J hI hJ hSourceI hSourceJ).i.naturality φ).symm,
    (fibrantFactorizationData I J hI hJ hSourceI hSourceJ).p.naturality φ⟩

/-- The actual original free/forgetful adjunction is Quillen for the constructed full model. -/
theorem freeForget_isQuillenAdjunction :
    letI : ModelCategory (Mon C) :=
      (fullAssociativeUnitalAlgebraModelTransfer I J hI hJ hSourceI hSourceJ).model
    (adjunction (C := C)).IsQuillenAdjunction := by
  let t := fullAssociativeUnitalAlgebraModelTransfer I J hI hJ hSourceI hSourceJ
  let : ModelCategory (Mon C) := t.model
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro A B f hf
    rw [t.fibrations_eq] at hf
    exact hf
  · intro A B f hf
    rw [t.trivialFibrations_eq] at hf
    exact hf

include I J hI hJ hSourceI hSourceJ in
/-- Full lifting against any original underlying trivial fibration holds on all monoid arrows. -/
theorem cofibration_trivialFibration_hasLift
    {A B X Y : Mon C} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ X} {v : B ⟶ Y}
    (sq : CommSq u i p v) (hi : cofibrationClass (C := C) i) (hp : trivialFibrations C p.hom) :
    sq.HasLift := by
  let t := fullAssociativeUnitalAlgebraModelTransfer I J hI hJ hSourceI hSourceJ
  let : ModelCategory (Mon C) := t.model
  have hi' : cofibrations (Mon C) i := by rw [t.cofibrations_eq]; exact hi
  have hp' : trivialFibrations (Mon C) p := by rw [t.trivialFibrations_eq]; exact hp
  let : HasLiftingProperty i p := hasLiftingProperty_of_wfs i p hi' hp'
  infer_instance

include I J hI hJ hSourceI hSourceJ in
/-- The remaining lifting axiom holds for every transferred trivial cofibration and underlying fibration. -/
theorem trivialCofibration_fibration_hasLift
    {A B X Y : Mon C} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ X} {v : B ⟶ Y}
    (sq : CommSq u i p v) (hi : trivialCofibrationClass (C := C) i) (hp : fibrations C p.hom) :
    sq.HasLift := by
  let t := fullAssociativeUnitalAlgebraModelTransfer I J hI hJ hSourceI hSourceJ
  let : ModelCategory (Mon C) := t.model
  have hi' : trivialCofibrations (Mon C) i := by
    change cofibrations (Mon C) i ∧ weakEquivalences (Mon C) i
    rw [t.cofibrations_eq, t.weak_eq]
    exact hi
  have hp' : fibrations (Mon C) p := by rw [t.fibrations_eq]; exact hp
  let : HasLiftingProperty i p := hasLiftingProperty_of_wfs i p hi' hp'
  infer_instance

/-- The full constructed I lifting axiom supplies an actual diagonal and both original equations. -/
def cofibrationTrivialFibrationLift
    {A B X Y : Mon C} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ X} {v : B ⟶ Y}
    (sq : CommSq u i p v) (hi : cofibrationClass (C := C) i) (hp : trivialFibrations C p.hom) :
    sq.LiftStruct := by
  let h := cofibration_trivialFibration_hasLift I J hI hJ hSourceI hSourceJ sq hi hp
  exact h.exists_lift.some

/-- The full constructed J lifting axiom gives an actual diagonal for every original square. -/
def trivialCofibrationFibrationLift
    {A B X Y : Mon C} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ X} {v : B ⟶ Y}
    (sq : CommSq u i p v) (hi : trivialCofibrationClass (C := C) i) (hp : fibrations C p.hom) :
    sq.LiftStruct := by
  let h := trivialCofibration_fibration_hasLift I J hI hJ hSourceI hSourceJ sq hi hp
  exact h.exists_lift.some














end HomotopicalAlgebra.MonoidTransfer
