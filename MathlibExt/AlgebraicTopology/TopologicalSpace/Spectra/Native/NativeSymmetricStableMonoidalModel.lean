/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeSymmetricOriginalUnitComparisons
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeSymmetricStableModelConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalUnitModelChange
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductQuillen

/-!
# The original native symmetric stable smash classes

The full original I-left cofibration class retains the actual level smash
pushout-product law. The literal complete K-by-I product lies in the
intersection of that same cofibration class and every original Omega test.
The stable-model recognition identifies this intersection with the full
original K-left class before the final model packaging.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory CGWH.limits

namespace PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash

private abbrev V := PointedCGWH.{u, v}
private abbrev Operator := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} Operator.{u, v}

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal
  monoidalCategory symmetricCategory monoidalClosed

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The unchanged original I-left classes have the entire actual smash cofibration product. -/
theorem originalILeft_pushoutProduct_originalILeft :
    PushoutProductLe (NativeK.levelI (I := Operator.{u, v})).rlp.llp
      (NativeK.levelI (I := Operator.{u, v})).rlp.llp
      (NativeK.levelI (I := Operator.{u, v})).rlp.llp := by
  simpa only [HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq] using
    (cofibrations_pushoutProduct_cofibrations (B := B))

/-- Every literal original K-by-I product is both an original I-left
cofibration and an equivalence on every original Omega target. -/
theorem originalGenerators_pushoutProduct_originalILeft_omegaTests :
    PushoutProductLe (NativeK.generators Actual.symmetricFamily.{u, v})
      (NativeK.levelI (I := Operator.{u, v}))
      ((NativeK.levelI (I := Operator.{u, v})).rlp.llp ⊓
        NativeK.omegaTests Actual.symmetricFamily.{u, v}) := by
  intro X Y K L i j hi hj
  have hiC : (NativeK.levelI (I := Operator.{u, v})).rlp.llp i := by
    rw [← HomotopicalAlgebra.EnrichedProjective.Native.cofibrations_eq]
    exact NativeK.generators_le_cofibrations Actual.symmetricFamily i hi
  exact ⟨originalILeft_pushoutProduct_originalILeft i j hiC
      ((NativeK.levelI (I := Operator.{u, v})).le_llp_rlp j hj),
    generators_pushoutProduct_levelI_omegaTests i j hi hj⟩

/-- The stable model is the actual original-family construction on this native carrier. -/
private abbrev constructedStableModel : ModelCategory Carrier.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricModelCategory
    (B := B)

private theorem level_cofibrations_eq_stable :
    (letI : ModelCategory Carrier.{u, v} :=
      HomotopicalAlgebra.EnrichedProjective.Native.modelCategory (A := Operator.{u, v}) (B := B)
     cofibrations Carrier.{u, v}) =
      (letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
       cofibrations Carrier.{u, v}) := by
  exact
    (HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetric_cofibrations_eq_level
      (B := B)).symm

/-- All three stable pushout-product laws follow from the literal original I/K products,
the actual original generation data and the whole Arrow braid. -/
theorem stablePushoutProductAxiom :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    MonoidalPushoutProductAxiom Carrier.{u, v} := by
  let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
  let G := HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricGenerationData
    (B := B)
  apply G.pushoutProductAxiom_of_generatorProducts
  · change MorphismProperty.PushoutProductLe (NativeK.levelI (I := Operator.{u, v}))
      (NativeK.levelI (I := Operator.{u, v})) (NativeK.levelI (I := Operator.{u, v})).rlp.llp
    intro X Y K L i j hi hj
    exact originalILeft_pushoutProduct_originalILeft i j
      ((NativeK.levelI (I := Operator.{u, v})).le_llp_rlp i hi)
      ((NativeK.levelI (I := Operator.{u, v})).le_llp_rlp j hj)
  · change MorphismProperty.PushoutProductLe (NativeK.generators Actual.symmetricFamily.{u, v})
      (NativeK.levelI (I := Operator.{u, v}))
      ((NativeK.levelI (I := Operator.{u, v})).rlp.llp ⊓ NativeK.omegaTests Actual.symmetricFamily.{u, v})
    exact originalGenerators_pushoutProduct_originalILeft_omegaTests (B := B)

/-- Actual sphere-unit cofibrancy transports through the unchanged original I-left class. -/
theorem stableTensorUnit_isCofibrant :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    IsCofibrant (𝟙_ Carrier.{u, v}) :=
  (HomotopicalAlgebra.ModelCategory.isCofibrant_iff_of_cofibrations_eq
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
      (A := Operator.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (𝟙_ Carrier.{u, v})).mp (levelTensorUnit_isCofibrant.{u, v} (B := B))

/-- Only membership proofs change in the actual original initial-unit factor record. -/
def originalStableUnitFactor :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    MapFactorizationData (cofibrations Carrier.{u, v}) (trivialFibrations Carrier.{u, v})
      (initial.to (𝟙_ Carrier.{u, v})) :=
  HomotopicalAlgebra.ModelCategory.cofibrantMapFactorizationOfCofibrationsEq
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
      (A := Operator.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (initial.to (𝟙_ Carrier.{u, v})) (originalLevelUnitFactor (B := B))

/-- The middle object and both original factor arrows retain their exact values. -/
theorem originalStableUnitFactor_original_fields :
    (originalStableUnitFactor (B := B)).Z = (originalLevelUnitFactor (B := B)).Z ∧
      (originalStableUnitFactor (B := B)).i = (originalLevelUnitFactor (B := B)).i ∧
      (originalStableUnitFactor (B := B)).p = (originalLevelUnitFactor (B := B)).p :=
  ⟨rfl, rfl, rfl⟩

/-- The stable unit witness uses this same original native I-factor and sphere unit. -/
def stableUnitAxiomWitness :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    MonoidalUnitAxiomWitness Carrier.{u, v} :=
  HomotopicalAlgebra.ModelCategory.unitAxiomWitnessOfCofibrationsEqUnitFactor
    (HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
      (A := Operator.{u, v}) (B := B))
    (constructedStableModel (B := B)) (level_cofibrations_eq_stable (B := B))
    (stablePushoutProductAxiom (B := B)) (levelTensorUnit_isCofibrant.{u, v} (B := B))
    (originalLevelUnitFactor (B := B))

/-- The stable witness retains the entire original same-cardinal middle functor value. -/
theorem stableUnitAxiomWitness_Q :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    (stableUnitAxiomWitness (B := B)).Q =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).Z.obj
          (CategoryTheory.Arrow.mk (initial.to (𝟙_ Carrier.{u, v}))) := rfl

/-- The stable witness map is exactly the original same-bottom right factor. -/
theorem stableUnitAxiomWitness_q :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    (stableUnitAxiomWitness (B := B)).q =
      (HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
        (A := Operator.{u, v}) (B := B)).p.app
          (CategoryTheory.Arrow.mk (initial.to (𝟙_ Carrier.{u, v}))) := rfl

/-- Both original factor legs retain their original complete factor equation. -/
theorem stableUnitAxiomWitness_fac :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    (originalLevelUnitFactor (B := B)).i ≫ (stableUnitAxiomWitness (B := B)).q =
      initial.to (𝟙_ Carrier.{u, v}) :=
  (originalLevelUnitFactor (B := B)).fac

/-- The full left unit replacement uses the actual original q and actual left unitor. -/
theorem stableUnitReplacement_left (X : Carrier.{u, v})
    (hX : letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
      IsCofibrant X) :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    weakEquivalences Carrier.{u, v}
      ((leftUnitReplacementMap (stableUnitAxiomWitness (B := B)).q).app X) := by
  let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
  let : IsCofibrant X := hX
  let : IsCofibrant (𝟙_ Carrier.{u, v}) := stableTensorUnit_isCofibrant (B := B)
  let w : MonoidalUnitAxiomWitness Carrier.{u, v} := stableUnitAxiomWitness (B := B)
  exact (stablePushoutProductAxiom (B := B)).leftUnitReplacementMap_weak
    w.q w.Q_cofibrant w.q_trivialFibration X

/-- The full right replacement comparison uses the same original q and actual right unitor. -/
theorem stableUnitReplacement_right (X : Carrier.{u, v})
    (hX : letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
      IsCofibrant X) :
    letI : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    weakEquivalences Carrier.{u, v}
      ((rightUnitReplacementMap (stableUnitAxiomWitness (B := B)).q).app X) := by
  let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
  let : IsCofibrant X := hX
  let : IsCofibrant (𝟙_ Carrier.{u, v}) := stableTensorUnit_isCofibrant (B := B)
  let w : MonoidalUnitAxiomWitness Carrier.{u, v} := stableUnitAxiomWitness (B := B)
  exact (stablePushoutProductAxiom (B := B)).rightUnitReplacementMap_weak
    w.q w.Q_cofibrant w.q_trivialFibration X

/-- The entire left comparison in the stable witness retains the original level q and unitor. -/
theorem originalLeftUnitComparison_eq_stableWitness :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    originalLeftUnitComparison.{u, v} (B := B) =
      leftUnitReplacementMap (stableUnitAxiomWitness (B := B)).q := rfl

/-- The entire right comparison in the stable witness retains that same original q and unitor. -/
theorem originalRightUnitComparison_eq_stableWitness :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    originalRightUnitComparison.{u, v} (B := B) =
      rightUnitReplacementMap (stableUnitAxiomWitness (B := B)).q := rfl

/-- The original left q/unitor comparison is a stable equivalence on every actual cofibrant. -/
theorem stableOriginalLeftUnitComparison_weak (X : Carrier.{u, v})
    (hX : let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
      IsCofibrant X) :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    weakEquivalences Carrier.{u, v} ((originalLeftUnitComparison.{u, v} (B := B)).app X) :=
  stableUnitReplacement_left X hX

/-- The original right q/unitor comparison is a stable equivalence on every actual cofibrant. -/
theorem stableOriginalRightUnitComparison_weak (X : Carrier.{u, v})
    (hX : let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
      IsCofibrant X) :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    weakEquivalences Carrier.{u, v} ((originalRightUnitComparison.{u, v} (B := B)).app X) :=
  stableUnitReplacement_right X hX

/-- The stable witness uses the actual original native Q object and literal unit counit. -/
def nativeStableUnitAxiomWitness :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    MonoidalUnitAxiomWitness Carrier.{u, v} := by
  let _ : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
  let _ : IsCofibrant (𝟙_ Carrier.{u, v}) := stableTensorUnit_isCofibrant (B := B)
  exact (stablePushoutProductAxiom (B := B)).unitAxiomWitnessOfCofibrantUnit
    (nativeUnitReplacementMap.{u, v} (B := B))
    (HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricQ_isCofibrant
      (B := B) (𝟙_ Carrier.{u, v}))
    (HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricQCounit_trivialFibration
      (B := B) (𝟙_ Carrier.{u, v}))

/-- The stable unit witness retains the whole original native Q and its literal unit counit. -/
theorem nativeStableUnitAxiomWitness_original_fields :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    (nativeStableUnitAxiomWitness (B := B)).Q = nativeUnitReplacementSource.{u, v} (B := B) ∧
      (nativeStableUnitAxiomWitness (B := B)).q = nativeUnitReplacementMap.{u, v} (B := B) :=
  ⟨rfl, rfl⟩

/-- The entire left comparison in this stable witness is the literal original native family. -/
theorem nativeLeftUnitComparison_eq_stableWitness :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    nativeLeftUnitComparison.{u, v} (B := B) =
      leftUnitReplacementMap (nativeStableUnitAxiomWitness (B := B)).q := rfl

/-- The entire right comparison in this stable witness is the same original native family. -/
theorem nativeRightUnitComparison_eq_stableWitness :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    nativeRightUnitComparison.{u, v} (B := B) =
      rightUnitReplacementMap (nativeStableUnitAxiomWitness (B := B)).q := rfl

/-- The actual native Q counit followed by the original left unitor is a stable equivalence. -/
theorem stableNativeLeftUnitComparison_weak (X : Carrier.{u, v})
    (hX : let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
      IsCofibrant X) :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    weakEquivalences Carrier.{u, v}
      ((((HomotopicalAlgebra.EnrichedProjective.Native.Replacement.cofibrantReplacementCounit
        (A := Operator.{u, v}) (B := B)).app (𝟙_ Carrier.{u, v}) ▷ X) ≫ (λ_ X).hom)) := by
  let _ : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant (𝟙_ Carrier.{u, v}) := stableTensorUnit_isCofibrant (B := B)
  let P : MonoidalPushoutProductAxiom Carrier.{u, v} := stablePushoutProductAxiom (B := B)
  let Q : Carrier.{u, v} := nativeUnitReplacementSource.{u, v} (B := B)
  let q : Q ⟶ 𝟙_ Carrier.{u, v} := nativeUnitReplacementMap.{u, v} (B := B)
  have hQ : IsCofibrant Q :=
    HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricQ_isCofibrant
      (B := B) (𝟙_ Carrier.{u, v})
  have hq : trivialFibrations Carrier.{u, v} q :=
    HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricQCounit_trivialFibration
      (B := B) (𝟙_ Carrier.{u, v})
  exact P.leftUnitReplacementMap_weak q hQ hq X

/-- The same actual native Q counit followed by the original right unitor is stable weak. -/
theorem stableNativeRightUnitComparison_weak (X : Carrier.{u, v})
    (hX : let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
      IsCofibrant X) :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    weakEquivalences Carrier.{u, v}
      (((X ◁ (HomotopicalAlgebra.EnrichedProjective.Native.Replacement.cofibrantReplacementCounit
        (A := Operator.{u, v}) (B := B)).app (𝟙_ Carrier.{u, v})) ≫ (ρ_ X).hom)) := by
  let _ : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant (𝟙_ Carrier.{u, v}) := stableTensorUnit_isCofibrant (B := B)
  let P : MonoidalPushoutProductAxiom Carrier.{u, v} := stablePushoutProductAxiom (B := B)
  let Q : Carrier.{u, v} := nativeUnitReplacementSource.{u, v} (B := B)
  let q : Q ⟶ 𝟙_ Carrier.{u, v} := nativeUnitReplacementMap.{u, v} (B := B)
  have hQ : IsCofibrant Q :=
    HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricQ_isCofibrant
      (B := B) (𝟙_ Carrier.{u, v})
  have hq : trivialFibrations Carrier.{u, v} q :=
    HomotopicalAlgebra.EnrichedProjective.Native.StableModelConstruction.symmetricQCounit_trivialFibration
      (B := B) (𝟙_ Carrier.{u, v})
  exact P.rightUnitReplacementMap_weak q hQ hq X

/-- The actual constructed native stable model has its closed symmetric smash model laws,
with the exact original native Q sphere-unit replacement and actual unitors. -/
theorem stableSmashMonoidalModel :
    let : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
    IsClosedSymmetricMonoidalModelCategory Carrier.{u, v} := by
  let _ : ModelCategory Carrier.{u, v} := constructedStableModel (B := B)
  exact {
    cofibration_pushoutProduct := (stablePushoutProductAxiom (B := B)).cofibration_pushoutProduct
    trivial_pushoutProduct_left := (stablePushoutProductAxiom (B := B)).trivial_pushoutProduct_left
    trivial_pushoutProduct_right := (stablePushoutProductAxiom (B := B)).trivial_pushoutProduct_right
    unit_axiom := ⟨nativeStableUnitAxiomWitness (B := B)⟩ }

end PointedCGWH.Spectra.NativeStableMonoidal.SymmetricSmash
