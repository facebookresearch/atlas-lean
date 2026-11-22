/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableModelConstruction
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.StableFactorizations

/-!
# The original native sequential stable model and its whole chosen factors

The stable model is constructed from the actual native chosen-fiber
recognition argument. Its I and K factorizations use the entire original
records at the same realized cardinal and caller bottom. Their objects,
Arrow maps, both natural transformations and factor equations are retained.

The original I cofibrant replacement and K Omega replacement become the
stable cofibrant and fibrant replacements. Their entire original functors,
zero arrows, units, counits and both source-map naturalities remain literal.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory ZeroObject

namespace PointedCGWH.Spectra.NativeStableModels

private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev family := PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original continuous enriched sequential carrier has its constructed stable model. -/
@[instance_reducible]
def sequentialModelCategory : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
  StableModelConstruction.sequentialModelCategory

/-- Actual native source smallness and the proved stable classes give full original generation. -/
def sequentialGenerationData :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    CofibrantGenerationData PointedCGWH.SequentialSpectrum.{u, v} realizedGeneratorCardinal.{v} :=
  StableModelConstruction.sequentialGenerationData

/-- The full stable I factorization is the original I record in its proved stable classes. -/
def sequentialIFactorizationData :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    FunctorialFactorizationData (cofibrations PointedCGWH.SequentialSpectrum.{u, v})
      (trivialFibrations PointedCGWH.SequentialSpectrum.{u, v}) := by
  let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
  change FunctorialFactorizationData (NativeK.levelI (I := Index)).rlp.llp
    ((NativeK.generators family).rlp ⊓ NativeK.omegaTests family)
  exact PointedCGWH.Spectra.NativeStable.sequentialIFactorizationData.{u, v}

/-- The full stable K factorization uses actual sphere-Hom cofibrancy,
with every original generator label and chosen factor map retained. -/
def sequentialKFactorizationData :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    FunctorialFactorizationData (trivialCofibrations PointedCGWH.SequentialSpectrum.{u, v})
      (fibrations PointedCGWH.SequentialSpectrum.{u, v}) := by
  let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
  change FunctorialFactorizationData
    ((NativeK.levelI (I := Index)).rlp.llp ⊓ NativeK.omegaTests family)
    (NativeK.generators family).rlp
  exact PointedCGWH.Spectra.NativeStable.sequentialKFactorizationData.{u, v}

/-- The complete I middle functor and both natural arrows are the original existing values. -/
theorem sequentialI_original_fields :
    sequentialIFactorizationData.{u, v}.Z =
        (OriginalFactorizationAssembly.originalI (A := Index)).Z ∧
      sequentialIFactorizationData.{u, v}.i =
        (OriginalFactorizationAssembly.originalI (A := Index)).i ∧
      sequentialIFactorizationData.{u, v}.p =
        (OriginalFactorizationAssembly.originalI (A := Index)).p :=
  ⟨rfl, rfl, rfl⟩

/-- The complete K middle functor and both natural arrows are the unchanged original K values. -/
theorem sequentialK_original_fields :
    sequentialKFactorizationData.{u, v}.Z = (NativeK.factorizationData family).Z ∧
      sequentialKFactorizationData.{u, v}.i = (NativeK.factorizationData family).i ∧
      sequentialKFactorizationData.{u, v}.p = (NativeK.factorizationData family).p :=
  ⟨rfl, rfl, rfl⟩

attribute [local instance] Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

/-- Both intermediate objects are the original same-cardinal small-object outputs. -/
theorem sequential_factorization_objects (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    sequentialIFactorizationData.{u, v}.Z.obj F =
        SmallObject.obj (NativeK.levelI (I := Index)) realizedGeneratorCardinal.{v} F.hom ∧
      sequentialKFactorizationData.{u, v}.Z.obj F =
        SmallObject.obj (NativeK.generators family) realizedGeneratorCardinal.{v} F.hom :=
  ⟨rfl, rfl⟩

/-- Every arbitrary original Arrow square has both entire original small-object maps. -/
theorem sequential_factorization_maps {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}}
    (φ : F ⟶ G) :
    sequentialIFactorizationData.{u, v}.Z.map φ =
        SmallObject.objMap (NativeK.levelI (I := Index)) realizedGeneratorCardinal.{v} φ ∧
      sequentialKFactorizationData.{u, v}.Z.map φ =
        SmallObject.objMap (NativeK.generators family) realizedGeneratorCardinal.{v} φ :=
  ⟨rfl, rfl⟩

/-- All four chosen factor legs retain the original I/K injection and projection functions. -/
theorem sequential_factorization_legs (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    sequentialIFactorizationData.{u, v}.i.app F =
        SmallObject.ιObj (NativeK.levelI (I := Index)) realizedGeneratorCardinal.{v} F.hom ∧
      sequentialIFactorizationData.{u, v}.p.app F =
        SmallObject.πObj (NativeK.levelI (I := Index)) realizedGeneratorCardinal.{v} F.hom ∧
      sequentialKFactorizationData.{u, v}.i.app F =
        SmallObject.ιObj (NativeK.generators family) realizedGeneratorCardinal.{v} F.hom ∧
      sequentialKFactorizationData.{u, v}.p.app F =
        SmallObject.πObj (NativeK.generators family) realizedGeneratorCardinal.{v} F.hom :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both entire original I/K records factor the same caller arrow. -/
theorem sequential_factorization_fac (F : Arrow PointedCGWH.SequentialSpectrum.{u, v}) :
    sequentialIFactorizationData.{u, v}.i.app F ≫
        sequentialIFactorizationData.{u, v}.p.app F = F.hom ∧
      sequentialKFactorizationData.{u, v}.i.app F ≫
        sequentialKFactorizationData.{u, v}.p.app F = F.hom :=
  ⟨sequentialIFactorizationData.{u, v}.fac_app, sequentialKFactorizationData.{u, v}.fac_app⟩

/-- Both factorization functors retain both sides of every original Arrow naturality square. -/
theorem sequential_factorization_naturality {F G : Arrow PointedCGWH.SequentialSpectrum.{u, v}}
    (φ : F ⟶ G) :
    sequentialIFactorizationData.{u, v}.i.app F ≫ sequentialIFactorizationData.{u, v}.Z.map φ =
        φ.left ≫ sequentialIFactorizationData.{u, v}.i.app G ∧
      sequentialIFactorizationData.{u, v}.Z.map φ ≫ sequentialIFactorizationData.{u, v}.p.app G =
        sequentialIFactorizationData.{u, v}.p.app F ≫ φ.right ∧
      sequentialKFactorizationData.{u, v}.i.app F ≫ sequentialKFactorizationData.{u, v}.Z.map φ =
        φ.left ≫ sequentialKFactorizationData.{u, v}.i.app G ∧
      sequentialKFactorizationData.{u, v}.Z.map φ ≫ sequentialKFactorizationData.{u, v}.p.app G =
        sequentialKFactorizationData.{u, v}.p.app F ≫ φ.right :=
  ⟨(sequentialIFactorizationData.{u, v}.i.naturality φ).symm,
    sequentialIFactorizationData.{u, v}.p.naturality φ,
    (sequentialKFactorizationData.{u, v}.i.naturality φ).symm,
    sequentialKFactorizationData.{u, v}.p.naturality φ⟩

/-- The two stable weak factorization systems have these actual full functorial records. -/
theorem sequential_functorialFactorizations :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    HasFunctorialFactorization (cofibrations PointedCGWH.SequentialSpectrum.{u, v})
        (trivialFibrations PointedCGWH.SequentialSpectrum.{u, v}) ∧
      HasFunctorialFactorization (trivialCofibrations PointedCGWH.SequentialSpectrum.{u, v})
        (fibrations PointedCGWH.SequentialSpectrum.{u, v}) :=
  ⟨⟨⟨sequentialIFactorizationData⟩⟩, ⟨⟨sequentialKFactorizationData⟩⟩⟩

/-- Stable cofibrations retain exactly the original native level cofibration class. -/
theorem sequential_cofibrations_eq_level :
    sequentialModelCategory.{u, v}.categoryWithCofibrations.cofibrations =
      (Native.modelCategory (B := B) (A := Index)).categoryWithCofibrations.cofibrations := by
  change (NativeK.levelI (I := Index)).rlp.llp = _
  exact (Native.cofibrations_eq (B := B) (A := Index)).symm

/-- The original I middle functor on the original zero-source arrows is the stable Q. -/
def sequentialCofibrantReplacement : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    PointedCGWH.SequentialSpectrum.{u, v} :=
  Diagrams.fromZeroArrow ⋙ sequentialIFactorizationData.Z

/-- The whole original I first map is retained at the original zero-source family. -/
def sequentialInitialToQ :
    (Functor.const PointedCGWH.SequentialSpectrum.{u, v}).obj Diagrams.zeroDiagram ⟶
      sequentialCofibrantReplacement :=
  Functor.whiskerLeft Diagrams.fromZeroArrow sequentialIFactorizationData.i

/-- The whole original I second map is the stable Q counit. -/
def sequentialQCounit : sequentialCofibrantReplacement.{u, v} ⟶
    𝟭 PointedCGWH.SequentialSpectrum.{u, v} :=
  Functor.whiskerLeft Diagrams.fromZeroArrow sequentialIFactorizationData.p

/-- The original K middle functor on the same zero-target arrows is the
stable fibrant replacement. -/
def sequentialFibrantReplacement : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    PointedCGWH.SequentialSpectrum.{u, v} :=
  Diagrams.toZeroArrow ⋙ sequentialKFactorizationData.Z

/-- The entire original K inclusion is the stable replacement unit. -/
def sequentialRUnit : 𝟭 PointedCGWH.SequentialSpectrum.{u, v} ⟶
    sequentialFibrantReplacement.{u, v} :=
  Functor.whiskerLeft Diagrams.toZeroArrow sequentialKFactorizationData.i

/-- The entire original K projection keeps the original chosen zero-target map. -/
def sequentialRToZero : sequentialFibrantReplacement.{u, v} ⟶
    (Functor.const PointedCGWH.SequentialSpectrum.{u, v}).obj Diagrams.zeroDiagram :=
  Functor.whiskerLeft Diagrams.toZeroArrow sequentialKFactorizationData.p

/-- Both whole replacements and their four natural maps retain the original I/K choices. -/
theorem sequential_replacement_original_fields :
    sequentialCofibrantReplacement.{u, v} = Replacement.cofibrantReplacement (A := Index) ∧
      sequentialInitialToQ.{u, v} = Replacement.initialToCofibrantReplacement (A := Index) ∧
      sequentialQCounit.{u, v} = Replacement.cofibrantReplacementCounit (A := Index) ∧
      sequentialFibrantReplacement.{u, v} = NativeK.omegaReplacement family.{u, v} ∧
      sequentialRUnit.{u, v} = NativeK.omegaReplacementUnit family.{u, v} ∧
      sequentialRToZero.{u, v} = Functor.whiskerLeft Diagrams.toZeroArrow
        (NativeK.factorizationData family.{u, v}).p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The actual I replacement is cofibrant for the constructed stable model at every source. -/
theorem sequentialQ_isCofibrant (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    IsCofibrant (sequentialCofibrantReplacement.obj X) := by
  let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
  change IsCofibrant (sequentialCofibrantReplacement.obj X)
  rw [isCofibrant_iff_of_isInitial (sequentialInitialToQ.app X) Diagrams.zeroDiagramIsInitial]
  exact (HomotopicalAlgebra.cofibration_iff (sequentialInitialToQ.app X)).mpr
    (sequentialIFactorizationData.hi (Diagrams.fromZeroArrow.obj X))

/-- The original Q counit is a stable trivial fibration on every original source. -/
theorem sequentialQCounit_trivialFibration (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    trivialFibrations PointedCGWH.SequentialSpectrum.{u, v} (sequentialQCounit.app X) :=
  sequentialIFactorizationData.hp (Diagrams.fromZeroArrow.obj X)

/-- The actual full-family K replacement is stable fibrant at every original source. -/
theorem sequentialR_isFibrant (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    IsFibrant (sequentialFibrantReplacement.obj X) := by
  let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
  change IsFibrant (sequentialFibrantReplacement.obj X)
  have h : IsFibrant (sequentialFibrantReplacement.obj X) ↔
      NativeK.IsOmega family (sequentialFibrantReplacement.obj X) :=
    StableModelConstruction.sequential_isFibrant_iff_isOmega (sequentialFibrantReplacement.obj X)
  exact h.mpr (NativeK.omegaReplacement_isOmega family X)

/-- The original K unit is a stable trivial cofibration for arbitrary original sources. -/
theorem sequentialRUnit_trivialCofibration (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    let : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} := sequentialModelCategory
    trivialCofibrations PointedCGWH.SequentialSpectrum.{u, v} (sequentialRUnit.app X) :=
  sequentialKFactorizationData.hi (Diagrams.toZeroArrow.obj X)

/-- The original replacement factor equations keep both genuine zero-arrow inputs. -/
theorem sequential_replacement_fac (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    sequentialInitialToQ.app X ≫ sequentialQCounit.app X = Diagrams.zeroTo X ∧
      sequentialRUnit.app X ≫ sequentialRToZero.app X = Diagrams.toZero X :=
  ⟨sequentialIFactorizationData.fac_app, sequentialKFactorizationData.fac_app⟩

/-- Every original source map retains both entire replacement unit/counit naturality squares. -/
theorem sequential_replacement_naturality {X Y : PointedCGWH.SequentialSpectrum.{u, v}}
    (f : X ⟶ Y) :
    sequentialCofibrantReplacement.map f ≫ sequentialQCounit.app Y =
        sequentialQCounit.app X ≫ f ∧
      f ≫ sequentialRUnit.app Y = sequentialRUnit.app X ≫ sequentialFibrantReplacement.map f :=
  ⟨sequentialQCounit.naturality f, sequentialRUnit.naturality f⟩

/-- The original level and constructed stable models share the identity adjunction
on the same underlying native spectrum category. -/
def sequentialLevelToStableAdjunction :
    ExplicitModelIdentity.comparison
        (Native.modelCategory (B := B) (A := Index) :
          ModelCategory PointedCGWH.SequentialSpectrum.{u, v})
        sequentialModelCategory.{u, v} ⊣
      ExplicitModelIdentity.comparison sequentialModelCategory.{u, v}
        (Native.modelCategory (B := B) (A := Index) :
          ModelCategory PointedCGWH.SequentialSpectrum.{u, v}) :=
  ExplicitModelIdentity.identityAdjunction
    (Native.modelCategory (B := B) (A := Index) :
      ModelCategory PointedCGWH.SequentialSpectrum.{u, v}) sequentialModelCategory.{u, v}

/-- Actual original cofibrations and native level weakness prove this whole Quillen adjunction. -/
theorem sequentialLevelToStable_isQuillen :
    sequentialLevelToStableAdjunction.{u, v}.IsQuillenAdjunction :=
  ExplicitModelIdentity.identityAdjunction_isQuillen
    (Native.modelCategory (B := B) (A := Index)) sequentialModelCategory
    (Native.cofibrations_eq (B := B) (A := Index))
    (NativeK.levelWeak_le_omegaTests family)

end PointedCGWH.Spectra.NativeStableModels
