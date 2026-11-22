/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceProducers.FreeCellHistories
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductAxiom

/-!
# Full original-cardinal operadic transfer from ordinal source producers

The two source-Hom comparisons produce the original free-I/free-J small-object
arguments. The original I endpoint comparisons also close the entire free-J
history through the checked ordinal acyclicity theorem. Recognition constructs
the full model, and both complete functorial factors are the literal original
small-object algorithms at the caller's cardinal and bottom.

This output record has no native presentability field. The hypotheses concern
the source model and its original generating endpoints, not a desired target
model, a recognition equality, or a free-J acyclicity outcome. The actual native
and conventional endpoint producers are connected in separate modules.

Pavlov--Scholbach's arXiv:1410.5675v4 monoidal-model convention omits the unit
axiom. The explicit pushout-product witness concerns the selected source model
and tensor; its name has a leading underscore because the broader recognition
proof needs no additional monoidal law. No cofibrant-unit premise is added.
-/

set_option autoImplicit false
noncomputable section

universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject
open CategoryTheory.Operad CategoryTheory.Operad.Tensor

namespace HomotopicalAlgebra.OperadicTransfer.SourceProducers

variable (S : SourceContext.{uW, v, u, us})

/-- The finite tensor in the original ordinal model source context. -/
local instance ordinalFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance ordinalTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance ordinalProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

/-- The conventional compact source input supplies the same original ordinal
source comparisons; a larger smallness rank alone cannot construct this value. -/
theorem ordinalSourceHomOfCompact (I P : MorphismProperty S.C)
    (h : CompactGeneratingSources.{us} I P) : SourceHomPreservation.{u, v, us} I P where
  domains i := by
    intro T _ _ _ D hD
    exact h.domains i T D hD
  codomains i := by
    intro T _ _ _ D hD
    exact h.codomains i T D hD

/-- Both original endpoint comparisons restrict to an earned structural
subclass on the same actual diagrams, without changing the source arrows. -/
theorem ordinalSourceHomOfLE (I P Q : MorphismProperty S.C)
    (h : SourceHomPreservation.{u, v, us} I P) (hQP : Q ≤ P) :
    SourceHomPreservation.{u, v, us} I Q where
  domains i := by
    intro T _ _ _ D hD
    exact h.domains i T D (fun a b f => hQP _ (hD a b f))
  codomains i := by
    intro T _ _ _ D hD
    exact h.codomains i T D (fun a b f => hQP _ (hD a b f))

/-- The full model and exact generation outputs at the caller's original
cardinal. Native source producers need no local-presentability certificate. -/
structure OriginalCardinalModelTransfer
    (O : ColoredOperadObj S.W S.C) (I J : MorphismProperty S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] where
  /-- The original free-I family's six actual small-object fields. -/
  I_smallObject : (freeGenerators S O I).IsCardinalForSmallObjectArgument κ
  /-- The original free-J family at exactly the same cardinal and bottom. -/
  J_smallObject : (freeGenerators S O J).IsCardinalForSmallObjectArgument κ
  /-- The full transferred model on the actual original algebra category. -/
  model : ModelCategory (Algebra O)
  /-- Weak equivalences are created at every original color. -/
  weak_class : letI := model; weakEquivalences (Algebra O) = weakClass S O
  /-- Fibrations are the actual underlying fibrations. -/
  fibration_class : letI := model; fibrations (Algebra O) = fibrationClass S O
  /-- Cofibrations retain the entire original trivial-fibration lifting class. -/
  cofibration_class : letI := model; cofibrations (Algebra O) = cofibrationClass S O
  /-- The literal original free-I right class generates this model. -/
  I_rlp : letI := model; (freeGenerators S O I).rlp = trivialFibrations (Algebra O)
  /-- The literal original free-J right class generates this model. -/
  J_rlp : letI := model; (freeGenerators S O J).rlp = fibrations (Algebra O)

/-- Source Hom for both original I/J families earns both small-object arguments,
and source Hom for the original I endpoints earns the full free-J acyclicity. -/
def fullModelTransferOfOrdinalSources
    (_hPP : MonoidalPushoutProductAxiom S.C)
    (O : ColoredOperadObj S.W S.C) (I J : MorphismProperty S.C)
    [I.IsSmall.{us}] [J.IsSmall.{us}] [LocallySmall.{us} S.C]
    (hI : I.rlp = trivialFibrations S.C) (hJ : J.rlp = fibrations S.C)
    (hSourcesI : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (hSourcesJ : SourceHomPreservation.{u, v, us} J
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] :
    OriginalCardinalModelTransfer S O I J κ := by
  letI : HasLimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasLimits S O
  letI : HasColimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasColimits S O
  letI : HasLimitsOfSize.{0, 0} (Algebra O) := hasLimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  letI : HasColimitsOfSize.{0, 0} (Algebra O) := hasColimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  letI : (freeGenerators S O I).IsCardinalForSmallObjectArgument κ :=
    freeGenerators_smallObject S O I
      (SemiModel.ColorSource.originalIGenerators_le_cofibrations S.C I hI) hSourcesI κ
  letI : (freeGenerators S O J).IsCardinalForSmallObjectArgument κ :=
    freeGenerators_smallObject S O J
      ((SemiModel.ColorSource.originalJGenerators_le_trivialCofibrations S.C J hJ).trans
        inf_le_left) hSourcesJ κ
  let hAcyclicity := freeJLeft_underlying_weak_ordinal S I hI hSourcesI h O J hJ κ
  let m := modelCategoryAtCardinal S O I J hI hJ κ hAcyclicity
  let d := generationDataAtCardinal S O I J hI hJ κ hAcyclicity
  exact
    { I_smallObject := inferInstance
      J_smallObject := inferInstance
      model := m
      weak_class := weakEquivalencesAtCardinal_eq S O I J hI hJ κ hAcyclicity
      fibration_class := fibrationsAtCardinal_eq S O I J hI hJ κ hAcyclicity
      cofibration_class := cofibrationsAtCardinal_eq S O I J hI hJ κ hAcyclicity
      I_rlp := d.I_rlp
      J_rlp := d.J_rlp }

namespace OriginalCardinalModelTransfer

variable {S} {O : ColoredOperadObj S.W S.C} {I J : MorphismProperty S.C}
  {κ : Cardinal.{us}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : OriginalCardinalModelTransfer S O I J κ)

/-- The generation data uses precisely the original free I/J and caller rank. -/
def generationData : letI := d.model; CofibrantGenerationData (Algebra O) κ := by
  letI := d.model
  exact
    { I := freeGenerators S O I
      J := freeGenerators S O J
      I_smallObject := d.I_smallObject
      J_smallObject := d.J_smallObject
      I_rlp := d.I_rlp
      J_rlp := d.J_rlp }

/-- The selected I factor is the original functorial small-object factor. -/
def cofibrantFactorizationData : letI := d.model;
    FunctorialFactorizationData (cofibrations (Algebra O)) (trivialFibrations (Algebra O)) := by
  letI := d.model
  exact d.generationData.cofibrantFactorizationData

/-- The selected J factor uses the same original ordinal and bottom. -/
def fibrantFactorizationData : letI := d.model;
    FunctorialFactorizationData (trivialCofibrations (Algebra O)) (fibrations (Algebra O)) := by
  letI := d.model
  exact d.generationData.fibrantFactorizationData

/-- The full I middle functor is unchanged by the model-class conversion. -/
theorem cofibrantFactorizationData_Z : letI := d.model;
    letI := d.I_smallObject;
    d.cofibrantFactorizationData.Z = (SmallObject.functorialFactorizationData (freeGenerators S O I) κ).Z :=
  rfl

/-- The full J middle functor is the original free-J small-object functor. -/
theorem fibrantFactorizationData_Z : letI := d.model;
    letI := d.J_smallObject;
    d.fibrantFactorizationData.Z = (SmallObject.functorialFactorizationData (freeGenerators S O J) κ).Z :=
  rfl

/-- Both original I natural transformations, with all caller Arrow squares, are retained. -/
theorem cofibrantFactorizationData_maps : letI := d.model;
    letI := d.I_smallObject;
    d.cofibrantFactorizationData.i = (SmallObject.functorialFactorizationData (freeGenerators S O I) κ).i ∧
      d.cofibrantFactorizationData.p = (SmallObject.functorialFactorizationData (freeGenerators S O I) κ).p :=
  ⟨rfl, rfl⟩

/-- Both original J natural transformations retain the same actual algorithm. -/
theorem fibrantFactorizationData_maps : letI := d.model;
    letI := d.J_smallObject;
    d.fibrantFactorizationData.i = (SmallObject.functorialFactorizationData (freeGenerators S O J) κ).i ∧
      d.fibrantFactorizationData.p = (SmallObject.functorialFactorizationData (freeGenerators S O J) κ).p :=
  ⟨rfl, rfl⟩

/-- Every I factorization acts on the caller's original arrow. -/
theorem cofibrantFactorizationData_fac (f : Arrow (Algebra O)) : letI := d.model;
    d.cofibrantFactorizationData.i.app f ≫ d.cofibrantFactorizationData.p.app f = f.hom :=
  d.cofibrantFactorizationData.fac_app

/-- Every J factorization retains the same original caller arrow. -/
theorem fibrantFactorizationData_fac (f : Arrow (Algebra O)) : letI := d.model;
    d.fibrantFactorizationData.i.app f ≫ d.fibrantFactorizationData.p.app f = f.hom :=
  d.fibrantFactorizationData.fac_app

end OriginalCardinalModelTransfer


end HomotopicalAlgebra.OperadicTransfer.SourceProducers
