/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.OriginalClasses

/-!
# Original full orthogonal factors and replacement functions

The full I and paired K records are the existing classified orthogonal
records. Every original middle object, Arrow action, factor leg and natural
square uses the original realized-cardinal small-object functions.
The two zero-arrow restrictions retain the actual original Q and Omega
replacement, including all four native maps and every input source action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativeStableModels

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C := OrthogonalCarrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.generatorsI_isCardinalForSmallObjectArgument
  NativeK.generators_isCardinalForSmallObjectArgument

/-- Both entire original middle objects have the unchanged source,
realized-generator cardinal and caller's ordinal bottom. -/
theorem factorization_objects (F : Arrow C.{u, v}) :
    classifiedIFactorizationData.Z.obj F =
        SmallObject.obj originalI realizedGeneratorCardinal.{v} F.hom ∧
      classifiedKFactorizationData.Z.obj F =
        SmallObject.obj originalK realizedGeneratorCardinal.{v} F.hom :=
  ⟨rfl, rfl⟩

/-- Every whole original native Arrow square retains both actual
same-cardinal small-object maps. -/
theorem factorization_maps {F G : Arrow C.{u, v}} (q : F ⟶ G) :
    classifiedIFactorizationData.Z.map q =
        SmallObject.objMap originalI realizedGeneratorCardinal.{v} q ∧
      classifiedKFactorizationData.Z.map q =
        SmallObject.objMap originalK realizedGeneratorCardinal.{v} q :=
  ⟨rfl, rfl⟩

/-- Every full original factor leg is the same original injection or
projection, retaining the full paired generator source. -/
theorem factorization_legs (F : Arrow C.{u, v}) :
    classifiedIFactorizationData.i.app F =
        SmallObject.ιObj originalI realizedGeneratorCardinal.{v} F.hom ∧
      classifiedIFactorizationData.p.app F =
        SmallObject.πObj originalI realizedGeneratorCardinal.{v} F.hom ∧
      classifiedKFactorizationData.i.app F =
        SmallObject.ιObj originalK realizedGeneratorCardinal.{v} F.hom ∧
      classifiedKFactorizationData.p.app F =
        SmallObject.πObj originalK realizedGeneratorCardinal.{v} F.hom :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both complete original records factor the caller's unchanged arrow. -/
theorem factorization_fac (F : Arrow C.{u, v}) :
    classifiedIFactorizationData.i.app F ≫ classifiedIFactorizationData.p.app F = F.hom ∧
      classifiedKFactorizationData.i.app F ≫ classifiedKFactorizationData.p.app F = F.hom :=
  ⟨classifiedIFactorizationData.fac_app, classifiedKFactorizationData.fac_app⟩

/-- All four original natural squares retain the entire native input
Arrow map and the unchanged two small-object outputs. -/
theorem factorization_naturality {F G : Arrow C.{u, v}} (q : F ⟶ G) :
    classifiedIFactorizationData.i.app F ≫ classifiedIFactorizationData.Z.map q =
        q.left ≫ classifiedIFactorizationData.i.app G ∧
      classifiedIFactorizationData.Z.map q ≫ classifiedIFactorizationData.p.app G =
        classifiedIFactorizationData.p.app F ≫ q.right ∧
      classifiedKFactorizationData.i.app F ≫ classifiedKFactorizationData.Z.map q =
        q.left ≫ classifiedKFactorizationData.i.app G ∧
      classifiedKFactorizationData.Z.map q ≫ classifiedKFactorizationData.p.app G =
        classifiedKFactorizationData.p.app F ≫ q.right :=
  ⟨(classifiedIFactorizationData.i.naturality q).symm,
    classifiedIFactorizationData.p.naturality q,
    (classifiedKFactorizationData.i.naturality q).symm,
    classifiedKFactorizationData.p.naturality q⟩

/-- The full original I middle functor on the actual zero-source arrows
is the unchanged cofibrant replacement. -/
def cofibrantReplacement : C.{u, v} ⥤ C.{u, v} :=
  Diagrams.fromZeroArrow ⋙ classifiedIFactorizationData.Z

/-- Its entire original I first map retains the original zero endpoint. -/
def initialToQ : (Functor.const C.{u, v}).obj Diagrams.zeroDiagram ⟶ cofibrantReplacement :=
  Functor.whiskerLeft Diagrams.fromZeroArrow classifiedIFactorizationData.i

/-- Its entire original I projection is the actual Q counit. -/
def qCounit : cofibrantReplacement.{u, v} ⟶ 𝟭 C.{u, v} :=
  Functor.whiskerLeft Diagrams.fromZeroArrow classifiedIFactorizationData.p

/-- The full paired K middle functor on the original zero-target arrows
is the actual native Omega replacement. -/
def fibrantReplacement : C.{u, v} ⥤ C.{u, v} :=
  Diagrams.toZeroArrow ⋙ classifiedKFactorizationData.Z

/-- The original K first map is the full replacement unit. -/
def rUnit : 𝟭 C.{u, v} ⟶ fibrantReplacement.{u, v} :=
  Functor.whiskerLeft Diagrams.toZeroArrow classifiedKFactorizationData.i

/-- The original K projection retains the original actual zero target. -/
def rToZero : fibrantReplacement.{u, v} ⟶
    (Functor.const C.{u, v}).obj Diagrams.zeroDiagram :=
  Functor.whiskerLeft Diagrams.toZeroArrow classifiedKFactorizationData.p

/-- Both whole replacement functions and all four complete maps are the
literal original I/K functions and choices. -/
theorem replacement_original_fields :
    cofibrantReplacement.{u, v} = Replacement.cofibrantReplacement (B := B) (A := O.{u, v}) ∧
      initialToQ.{u, v} = Replacement.initialToCofibrantReplacement (B := B) (A := O.{u, v}) ∧
      qCounit.{u, v} = Replacement.cofibrantReplacementCounit (B := B) (A := O.{u, v}) ∧
      fibrantReplacement.{u, v} = NativeK.omegaReplacement orthogonalFamily ∧
      rUnit.{u, v} = NativeK.omegaReplacementUnit orthogonalFamily ∧
      rToZero.{u, v} = Functor.whiskerLeft Diagrams.toZeroArrow
        (NativeK.factorizationData orthogonalFamily).p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The original Q counit lies in the entire actual trivial-right
intersection at every native source. -/
theorem qCounit_stableTrivialFibration (X : C.{u, v}) :
    stableTrivialFibrations (qCounit.app X) :=
  classifiedIFactorizationData.hp (Diagrams.fromZeroArrow.obj X)

/-- The full original K replacement unit lies in the actual trivial-left
intersection at every native source. -/
theorem rUnit_stableTrivialCofibration (X : C.{u, v}) :
    stableTrivialCofibrations (rUnit.app X) :=
  classifiedKFactorizationData.hi (Diagrams.toZeroArrow.obj X)

/-- The original K projection belongs to the entire paired right class. -/
theorem rToZero_stableFibration (X : C.{u, v}) :
    stableFibrations (rToZero.app X) :=
  classifiedKFactorizationData.hp (Diagrams.toZeroArrow.obj X)

/-- Every original full paired Omega condition holds on the same actual
native K replacement object. -/
theorem fibrantReplacement_isOmega (X : C.{u, v}) :
    NativeK.IsOmega orthogonalFamily (fibrantReplacement.obj X) :=
  NativeK.omegaReplacement_isOmega orthogonalFamily X

/-- Both whole replacement factors retain their original zero-arrow inputs. -/
theorem replacement_fac (X : C.{u, v}) :
    initialToQ.app X ≫ qCounit.app X = Diagrams.zeroTo X ∧
      rUnit.app X ≫ rToZero.app X = Diagrams.toZero X :=
  ⟨classifiedIFactorizationData.fac_app, classifiedKFactorizationData.fac_app⟩

/-- Every actual native source map retains both original replacement
unit and counit squares as full enriched maps. -/
theorem replacement_naturality {X Y : C.{u, v}} (f : X ⟶ Y) :
    cofibrantReplacement.map f ≫ qCounit.app Y = qCounit.app X ≫ f ∧
      f ≫ rUnit.app Y = rUnit.app X ≫ fibrantReplacement.map f :=
  ⟨qCounit.naturality f, rUnit.naturality f⟩

end PointedCGWH.Spectra.Orthogonal.NativeStableModels
